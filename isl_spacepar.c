/*
 * Copyright 2023      zhaosiying12138@IAYJT_LAS
 *
 * Use of this software is governed by the MIT license
 *
 * Written by zhaosiying12138, Institute of Advanced YanJia
 *  Technology - LiuYueCity Academy of Science 
 */

#include <assert.h>
#include <stdio.h>
#include <limits.h>
#include <isl_ctx_private.h>
#include <isl_map_private.h>
#include <isl_aff_private.h>
#include <isl_space_private.h>
#include <isl/id.h>
#include <isl/set.h>
#include <isl/flow.h>
#include <isl_constraint_private.h>
#include <isl/polynomial.h>
#include <isl/union_set.h>
#include <isl/union_map.h>
#include <isl_factorization.h>
#include <isl/schedule.h>
#include <isl/schedule_node.h>
#include <isl_options_private.h>
#include <isl_vertices_private.h>
#include <isl/ast_build.h>
#include <isl/val.h>
#include <isl/ilp.h>
#include <isl_ast_build_expr.h>
#include <isl/options.h>

static void zsy_codegen(__isl_keep isl_union_map *schedule)
{
	isl_ctx *ctx;
	isl_ast_build *build;
	isl_ast_node *tree;
	
	ctx = isl_union_map_get_ctx(schedule);
	build = isl_ast_build_from_context(isl_set_read_from_str(ctx, "{ : }"));
	tree = isl_ast_build_node_from_schedule_map(build, isl_union_map_copy(schedule));
	printf("%s\n", isl_ast_node_to_C_str(tree));
	isl_ast_node_free(tree);
}

static __isl_give isl_basic_map *zsy_isl_basic_map_set_range_dim_constant_val(__isl_take isl_basic_map *bmap, unsigned int pos, int val)
{
	isl_constraint *c;
	bmap = isl_basic_map_project_out(bmap, isl_dim_out, pos, 1);
	bmap = isl_basic_map_insert_dims(bmap, isl_dim_out, pos, 1);
	c = isl_constraint_alloc_equality(isl_local_space_from_space(isl_basic_map_get_space(bmap)));
	c = isl_constraint_set_coefficient_si(c, isl_dim_out, pos, -1);
	c = isl_constraint_set_constant_si(c, val);
	bmap = isl_basic_map_add_constraint(bmap, c);
	return bmap;
}

static __isl_give isl_union_map *zsy_isl_union_map_set_range_dim_constant_val(__isl_take isl_union_map *umap, unsigned int pos, int val)
{
	isl_union_map *res_umap = isl_union_map_empty(isl_union_map_get_space(umap));
	isl_map_list *map_list = isl_union_map_get_map_list(umap);
	for (int i = 0; i < isl_map_list_n_map(map_list); i++) {
		isl_map *map = isl_map_list_get_map(map_list, i);
		isl_basic_map_list *bmap_list = isl_map_get_basic_map_list(map);
		assert(isl_basic_map_list_n_basic_map(bmap_list) == 1);
		isl_basic_map *bmap = isl_basic_map_list_get_basic_map(bmap_list, 0);
		bmap = zsy_isl_basic_map_set_range_dim_constant_val(bmap, pos, val);
		res_umap = isl_union_map_add_map(res_umap, isl_map_from_basic_map(bmap));
	}
	return res_umap;
}

int zsy_spacepar_compute_schedule(isl_ctx *ctx)
{
	const char *d, *w, *r, *s, *con;
	isl_set *CON;
	isl_union_set *D;
	isl_union_map *W, *R, *S;
	isl_union_map *empty;
	isl_union_map *dep_raw, *dep_war, *dep_waw, *dep, *dep_rev;
	isl_union_map *validity;
	// isl_union_map *proximity, *coincidence;
	isl_schedule_constraints *sc;
	isl_schedule *sched;

	con = "{ : }";
	d = "{ S1[i, j] : 1 <= i <= 100 and 1 <= j <= 100; S2[i, j] : 1 <= i <= 100 and 1 <= j <= 100 }";
	w = "{ S1[i, j] -> X[i, j]; S2[i, j] -> Y[i, j] }";
	r = "{ S1[i, j] -> X[i, j]; S1[i, j] -> Y[i - 1, j]; S2[i, j] -> Y[i, j]; S2[i, j] -> X[i, j - 1] }";
	s = "{ S1[i, j] -> [0, i, 0, j, 0]; S2[i, j] -> [0, i, 0, j, 1] }";

	printf("\nCompute schedule:\n");
	CON = isl_set_read_from_str(ctx, con);
	D = isl_union_set_read_from_str(ctx, d);
	W = isl_union_map_read_from_str(ctx, w);
	R = isl_union_map_read_from_str(ctx, r);
	S = isl_union_map_read_from_str(ctx, s);

	W = isl_union_map_intersect_domain(W, isl_union_set_copy(D));
	R = isl_union_map_intersect_domain(R, isl_union_set_copy(D));
	S = isl_union_map_intersect_domain(S, isl_union_set_copy(D));

	empty = isl_union_map_empty(isl_union_map_get_space(S));
    isl_union_map_compute_flow(isl_union_map_copy(R),
				   isl_union_map_copy(W), isl_union_map_copy(empty),
				   isl_union_map_copy(S),
				   &dep_raw, NULL, NULL, NULL);
	isl_union_map_compute_flow(isl_union_map_copy(W),
				   isl_union_map_copy(W), isl_union_map_copy(empty),
				   isl_union_map_copy(S),
				   &dep_waw, NULL, NULL, NULL);
	isl_union_map_compute_flow(isl_union_map_copy(W),
				   isl_union_map_copy(R), isl_union_map_copy(empty),
				   isl_union_map_copy(S),
				   &dep_war, NULL, NULL, NULL);
	dep = isl_union_map_union(isl_union_map_copy(dep_waw), isl_union_map_copy(dep_war));
	dep = isl_union_map_union(dep, isl_union_map_copy(dep_raw));
	dep_rev = isl_union_map_reverse(isl_union_map_copy(dep));
	dep = isl_union_map_union(dep, dep_rev);

	validity = isl_union_map_copy(dep);
//	coincidence = isl_union_map_copy(dep);
//	proximity = isl_union_map_copy(dep);

	sc = isl_schedule_constraints_on_domain(isl_union_set_copy(D));
	sc = isl_schedule_constraints_set_context(sc, CON);
	sc = isl_schedule_constraints_set_validity(sc, validity);
//	sc = isl_schedule_constraints_set_coincidence(sc, coincidence);
//	sc = isl_schedule_constraints_set_proximity(sc, proximity);
	sched = isl_schedule_constraints_compute_schedule(sc);

	return 0;
}

int zsy_spacepar_isl_codegen(isl_ctx *ctx)
{
	const char *d, *s, *con;
	isl_set *CON;
	isl_union_set *D;
	isl_union_map *S;
	isl_schedule *sched;
	isl_ast_build *build;
	isl_ast_node *tree;

	con = "{ : }";
	d = "{ S1[i, j] : 1 <= i <= 100 and 1 <= j <= 100; S2[i, j] : 1 <= i <= 100 and 1 <= j <= 100 }";
	s = "{ S1[i, j] -> [i - j - 1, 0, i, 0, j, 0]; S2[i, j] -> [i - j, 0, i, 0, j, 1] }";

	printf("\nCodegen with ISL-native-ast-build:\n");
	CON = isl_set_read_from_str(ctx, con);
	D = isl_union_set_read_from_str(ctx, d);
	S = isl_union_map_read_from_str(ctx, s);
	S = isl_union_map_intersect_domain(S, D);

	build = isl_ast_build_from_context(CON);
	tree = isl_ast_build_node_from_schedule_map(build, S);
	printf("%s\n", isl_ast_node_to_C_str(tree));

	isl_ast_node_free(tree);
	isl_ast_build_free(build);

	return 0;
}

int zsy_test_space_partition_Quillere_step1(isl_ctx *ctx)
{
	const char *domain_str[2], *domain_name_str[2], *trans_str[2], *schedule_orig_str;
	isl_set *domain[2];
	isl_map *trans[2], *tmp_map;
	isl_union_map *schedule_orig;
	isl_set *domain_trans[2], *domain_trans_1dim[2], *domain_trans_2dim[2];
	isl_set *domain_trans_1dim_split[2][2], *domain_trans_2dim_split[2][2];
	isl_union_set *tmp_split_domain[3];
	isl_union_map *tmp_split_sched[3];
	isl_union_map *total_sched;

	printf("\nCodegen using Quillere Algo implemented manually:\n");
	printf("[Step 1]:\n");
	domain_str[0] = "{ S1[i, j] : 1 <= i <= 100 and 1 <= j <= 100 }";
	domain_str[1] = "{ S2[i, j] : 1 <= i <= 100 and 1 <= j <= 100 }";
	trans_str[0] = "{ S1[i, j] -> [p = i - j - 1, i, j] }";
	trans_str[1] = "{ S2[i, j] -> [p = i - j    , i, j] }";
	schedule_orig_str = "{ S1[p, i, j] -> [0, p, 0, i, 0, j, 0]; S2[p, i, j] -> [0, p, 0, i, 0, j, 1] }";

	domain[0] = isl_set_read_from_str(ctx, domain_str[0]);
	domain[1] = isl_set_read_from_str(ctx, domain_str[1]);
	domain_name_str[0] = isl_set_get_tuple_name(domain[0]);
	domain_name_str[1] = isl_set_get_tuple_name(domain[1]);
	trans[0] = isl_map_read_from_str(ctx, trans_str[0]);
	trans[1] = isl_map_read_from_str(ctx, trans_str[1]);
	schedule_orig = isl_union_map_read_from_str(ctx, schedule_orig_str);

	trans[0] = isl_map_set_tuple_name(trans[0], isl_dim_out, domain_name_str[0]);
	trans[1] = isl_map_set_tuple_name(trans[1], isl_dim_out, domain_name_str[1]);
	domain_trans[0] = isl_set_apply(domain[0], trans[0]);
	domain_trans[1] = isl_set_apply(domain[1], trans[1]);

	domain_trans_1dim[0] = isl_set_eliminate(isl_set_copy(domain_trans[0]), isl_dim_set, 1, 2);
	domain_trans_1dim[1] = isl_set_eliminate(isl_set_copy(domain_trans[1]), isl_dim_set, 1, 2);
	domain_trans_1dim[0] = isl_set_set_tuple_name(domain_trans_1dim[0], "");
	domain_trans_1dim[1] = isl_set_set_tuple_name(domain_trans_1dim[1], "");

	domain_trans_1dim_split[0][0] = isl_set_subtract(isl_set_copy(domain_trans_1dim[0]), isl_set_copy(domain_trans_1dim[1]));
	domain_trans_1dim_split[0][1] = isl_set_intersect(isl_set_copy(domain_trans_1dim[0]), isl_set_copy(domain_trans_1dim[1]));
	domain_trans_1dim_split[1][0] = isl_set_intersect(isl_set_copy(domain_trans_1dim[1]), isl_set_copy(domain_trans_1dim[0]));
	domain_trans_1dim_split[1][1] = isl_set_subtract(isl_set_copy(domain_trans_1dim[1]), isl_set_copy(domain_trans_1dim[0]));

	tmp_map = isl_set_lex_gt_set(isl_set_copy(domain_trans_1dim_split[0][0]), isl_set_copy(domain_trans_1dim_split[0][1]));
	domain_trans_1dim_split[0][0] = isl_set_set_tuple_name(domain_trans_1dim_split[0][0], domain_name_str[0]);
	domain_trans_1dim_split[0][1] = isl_set_set_tuple_name(domain_trans_1dim_split[0][1], domain_name_str[0]);
	domain_trans_1dim_split[1][0] = isl_set_set_tuple_name(domain_trans_1dim_split[1][0], domain_name_str[1]);
	domain_trans_1dim_split[1][1] = isl_set_set_tuple_name(domain_trans_1dim_split[1][1], domain_name_str[1]);
	domain_trans_1dim_split[0][0] = isl_set_intersect(domain_trans_1dim_split[0][0], isl_set_copy(domain_trans[0]));
	domain_trans_1dim_split[0][1] = isl_set_intersect(domain_trans_1dim_split[0][1], isl_set_copy(domain_trans[0]));
	domain_trans_1dim_split[1][0] = isl_set_intersect(domain_trans_1dim_split[1][0], isl_set_copy(domain_trans[1]));
	domain_trans_1dim_split[1][1] = isl_set_intersect(domain_trans_1dim_split[1][1], isl_set_copy(domain_trans[1]));

	if (isl_map_is_empty(tmp_map)) {
		tmp_split_domain[0] = isl_union_set_from_set(domain_trans_1dim_split[0][0]);
		tmp_split_domain[1] = isl_union_set_union(isl_union_set_from_set(domain_trans_1dim_split[0][1]),
													isl_union_set_from_set(domain_trans_1dim_split[1][0]));
		tmp_split_domain[2] = isl_union_set_from_set(domain_trans_1dim_split[1][1]);
	} else {
		tmp_split_domain[2] = isl_union_set_from_set(domain_trans_1dim_split[0][0]);
		tmp_split_domain[1] = isl_union_set_union(isl_union_set_from_set(domain_trans_1dim_split[0][1]),
													isl_union_set_from_set(domain_trans_1dim_split[1][0]));
		tmp_split_domain[0] = isl_union_set_from_set(domain_trans_1dim_split[1][1]);
	}

	isl_map_free(tmp_map);
	tmp_split_sched[0] = zsy_isl_union_map_set_range_dim_constant_val(isl_union_map_copy(schedule_orig), 0, 0);
	tmp_split_sched[1] = zsy_isl_union_map_set_range_dim_constant_val(isl_union_map_copy(schedule_orig), 0, 1);
	tmp_split_sched[2] = zsy_isl_union_map_set_range_dim_constant_val(isl_union_map_copy(schedule_orig), 0, 2);
	tmp_split_sched[0] = isl_union_map_intersect_domain(tmp_split_sched[0], isl_union_set_copy(tmp_split_domain[0]));
	tmp_split_sched[1] = isl_union_map_intersect_domain(tmp_split_sched[1], isl_union_set_copy(tmp_split_domain[1]));
	tmp_split_sched[2] = isl_union_map_intersect_domain(tmp_split_sched[2], isl_union_set_copy(tmp_split_domain[2]));


	zsy_codegen(tmp_split_sched[0]);
	zsy_codegen(tmp_split_sched[1]);
	zsy_codegen(tmp_split_sched[2]);

	return 0;
}

int zsy_test_space_partition_Quillere_step2(isl_ctx *ctx)
{
	const char *domain_str[2], *domain_name_str[2], *trans_str[2], *schedule_orig_str;
	isl_set *domain[2];
	isl_map *trans[2], *tmp_map;
	isl_union_map *schedule_orig;
	isl_set *domain_trans[2], *domain_trans_1dim[2], *domain_trans_2dim[2];
	isl_set *domain_trans_1dim_split[2][2], *domain_trans_2dim_split[2][2];
	isl_union_set *tmp_split_domain[3];
	isl_union_map *tmp_split_sched[3];
	isl_union_map *total_sched;

	printf("[Step 2]:\n");
	domain_str[0] = "{ S1[i, j] : 1 <= i <= 100 and 1 <= j <= 100 }";
	domain_str[1] = "{ S2[i, j] : 1 <= i <= 100 and 1 <= j <= 100 }";
	trans_str[0] = "{ S1[i, j] -> [p = i - j - 1, i, j] }";
	trans_str[1] = "{ S2[i, j] -> [p = i - j    , i, j] }";
	schedule_orig_str = "{ S1[p, i, j] -> [0, p, 0, i, 0, j, 0]; S2[p, i, j] -> [0, p, 0, i, 0, j, 1] }";

	domain[0] = isl_set_read_from_str(ctx, domain_str[0]);
	domain[1] = isl_set_read_from_str(ctx, domain_str[1]);
	domain_name_str[0] = isl_set_get_tuple_name(domain[0]);
	domain_name_str[1] = isl_set_get_tuple_name(domain[1]);
	trans[0] = isl_map_read_from_str(ctx, trans_str[0]);
	trans[1] = isl_map_read_from_str(ctx, trans_str[1]);
	schedule_orig = isl_union_map_read_from_str(ctx, schedule_orig_str);

	trans[0] = isl_map_set_tuple_name(trans[0], isl_dim_out, domain_name_str[0]);
	trans[1] = isl_map_set_tuple_name(trans[1], isl_dim_out, domain_name_str[1]);
	domain_trans[0] = isl_set_apply(domain[0], trans[0]);
	domain_trans[1] = isl_set_apply(domain[1], trans[1]);

	domain_trans_1dim[0] = isl_set_eliminate(isl_set_copy(domain_trans[0]), isl_dim_set, 1, 2);
	domain_trans_1dim[1] = isl_set_eliminate(isl_set_copy(domain_trans[1]), isl_dim_set, 1, 2);
	domain_trans_1dim[0] = isl_set_set_tuple_name(domain_trans_1dim[0], "");
	domain_trans_1dim[1] = isl_set_set_tuple_name(domain_trans_1dim[1], "");

	domain_trans_1dim_split[0][0] = isl_set_subtract(isl_set_copy(domain_trans_1dim[0]), isl_set_copy(domain_trans_1dim[1]));
	domain_trans_1dim_split[0][1] = isl_set_intersect(isl_set_copy(domain_trans_1dim[0]), isl_set_copy(domain_trans_1dim[1]));
	domain_trans_1dim_split[1][0] = isl_set_intersect(isl_set_copy(domain_trans_1dim[1]), isl_set_copy(domain_trans_1dim[0]));
	domain_trans_1dim_split[1][1] = isl_set_subtract(isl_set_copy(domain_trans_1dim[1]), isl_set_copy(domain_trans_1dim[0]));

	tmp_map = isl_set_lex_gt_set(isl_set_copy(domain_trans_1dim_split[0][0]), isl_set_copy(domain_trans_1dim_split[0][1]));
	domain_trans_1dim_split[0][0] = isl_set_set_tuple_name(domain_trans_1dim_split[0][0], domain_name_str[0]);
	domain_trans_1dim_split[0][1] = isl_set_set_tuple_name(domain_trans_1dim_split[0][1], domain_name_str[0]);
	domain_trans_1dim_split[1][0] = isl_set_set_tuple_name(domain_trans_1dim_split[1][0], domain_name_str[1]);
	domain_trans_1dim_split[1][1] = isl_set_set_tuple_name(domain_trans_1dim_split[1][1], domain_name_str[1]);
	domain_trans_1dim_split[0][0] = isl_set_intersect(domain_trans_1dim_split[0][0], isl_set_copy(domain_trans[0]));
	domain_trans_1dim_split[0][1] = isl_set_intersect(domain_trans_1dim_split[0][1], isl_set_copy(domain_trans[0]));
	domain_trans_1dim_split[1][0] = isl_set_intersect(domain_trans_1dim_split[1][0], isl_set_copy(domain_trans[1]));
	domain_trans_1dim_split[1][1] = isl_set_intersect(domain_trans_1dim_split[1][1], isl_set_copy(domain_trans[1]));

	if (isl_map_is_empty(tmp_map)) {
		tmp_split_domain[0] = isl_union_set_from_set(domain_trans_1dim_split[0][0]);
		tmp_split_domain[2] = isl_union_set_from_set(domain_trans_1dim_split[1][1]);
	} else {
		tmp_split_domain[2] = isl_union_set_from_set(domain_trans_1dim_split[0][0]);
		tmp_split_domain[0] = isl_union_set_from_set(domain_trans_1dim_split[1][1]);
	}

	isl_map_free(tmp_map);
	tmp_split_sched[0] = zsy_isl_union_map_set_range_dim_constant_val(isl_union_map_copy(schedule_orig), 0, 0);
	tmp_split_sched[2] = zsy_isl_union_map_set_range_dim_constant_val(isl_union_map_copy(schedule_orig), 0, 2);
	tmp_split_sched[0] = isl_union_map_intersect_domain(tmp_split_sched[0], isl_union_set_copy(tmp_split_domain[0]));
	tmp_split_sched[2] = isl_union_map_intersect_domain(tmp_split_sched[2], isl_union_set_copy(tmp_split_domain[2]));
	//total_sched = isl_union_map_union(tmp_split_sched[0], tmp_split_sched[2]);
	zsy_codegen(tmp_split_sched[0]);

	{
		isl_union_map *tmp_split_sched[3];

		domain_trans_2dim[0] = isl_set_eliminate(isl_set_copy(domain_trans_1dim_split[0][1]), isl_dim_set, 2, 1);
		domain_trans_2dim[1] = isl_set_eliminate(isl_set_copy(domain_trans_1dim_split[1][0]), isl_dim_set, 2, 1);
		domain_trans_2dim[0] = isl_set_set_tuple_name(domain_trans_2dim[0], "");
		domain_trans_2dim[1] = isl_set_set_tuple_name(domain_trans_2dim[1], "");
		domain_trans_2dim_split[0][0] = isl_set_subtract(isl_set_copy(domain_trans_2dim[0]), isl_set_copy(domain_trans_2dim[1]));
		domain_trans_2dim_split[0][1] = isl_set_intersect(isl_set_copy(domain_trans_2dim[0]), isl_set_copy(domain_trans_2dim[1]));
		domain_trans_2dim_split[1][0] = isl_set_intersect(isl_set_copy(domain_trans_2dim[1]), isl_set_copy(domain_trans_2dim[0]));
		domain_trans_2dim_split[1][1] = isl_set_subtract(isl_set_copy(domain_trans_2dim[1]), isl_set_copy(domain_trans_2dim[0]));

		tmp_map = isl_set_lex_gt_set(isl_set_copy(domain_trans_2dim_split[0][0]), isl_set_copy(domain_trans_2dim_split[0][1]));
		// add constraints for { [p, i1, i2] -> [p', o1, o2] : p = p' }
		isl_constraint *c;
		c = isl_constraint_alloc_equality(isl_local_space_from_space(isl_map_get_space(tmp_map)));
		c = isl_constraint_set_coefficient_si(c, isl_dim_in, 0, 1);
		c = isl_constraint_set_coefficient_si(c, isl_dim_out, 0, -1);
		c = isl_constraint_set_constant_si(c, 0);
		tmp_map = isl_map_add_constraint(tmp_map, c);
		domain_trans_2dim_split[0][0] = isl_set_set_tuple_name(domain_trans_2dim_split[0][0], domain_name_str[0]);
		domain_trans_2dim_split[0][1] = isl_set_set_tuple_name(domain_trans_2dim_split[0][1], domain_name_str[0]);
		domain_trans_2dim_split[1][0] = isl_set_set_tuple_name(domain_trans_2dim_split[1][0], domain_name_str[1]);
		domain_trans_2dim_split[1][1] = isl_set_set_tuple_name(domain_trans_2dim_split[1][1], domain_name_str[1]);
		domain_trans_2dim_split[0][0] = isl_set_intersect(domain_trans_2dim_split[0][0], isl_set_copy(domain_trans[0]));
		domain_trans_2dim_split[0][1] = isl_set_intersect(domain_trans_2dim_split[0][1], isl_set_copy(domain_trans[0]));
		domain_trans_2dim_split[1][0] = isl_set_intersect(domain_trans_2dim_split[1][0], isl_set_copy(domain_trans[1]));
		domain_trans_2dim_split[1][1] = isl_set_intersect(domain_trans_2dim_split[1][1], isl_set_copy(domain_trans[1]));

		if (isl_map_is_empty(tmp_map)) {
			tmp_split_domain[2] = isl_union_set_from_set(domain_trans_2dim_split[1][1]);
			tmp_split_domain[1] = isl_union_set_union(isl_union_set_from_set(domain_trans_2dim_split[0][1]),
												isl_union_set_from_set(domain_trans_2dim_split[1][0]));
			tmp_split_domain[0] = isl_union_set_from_set(domain_trans_2dim_split[0][0]);
		} else {
			tmp_split_domain[0] = isl_union_set_from_set(domain_trans_2dim_split[1][1]);
			tmp_split_domain[1] = isl_union_set_union(isl_union_set_from_set(domain_trans_2dim_split[0][1]),
												isl_union_set_from_set(domain_trans_2dim_split[1][0]));
			tmp_split_domain[2] = isl_union_set_from_set(domain_trans_2dim_split[0][0]);
		}

		isl_map_free(tmp_map);
		tmp_split_sched[0] = zsy_isl_union_map_set_range_dim_constant_val(isl_union_map_copy(schedule_orig), 0, 1);
		tmp_split_sched[0] = zsy_isl_union_map_set_range_dim_constant_val(tmp_split_sched[0], 2, 0);
		tmp_split_sched[1] = zsy_isl_union_map_set_range_dim_constant_val(isl_union_map_copy(schedule_orig), 0, 1);
		tmp_split_sched[1] = zsy_isl_union_map_set_range_dim_constant_val(tmp_split_sched[1], 2, 1);
		tmp_split_sched[2] = zsy_isl_union_map_set_range_dim_constant_val(isl_union_map_copy(schedule_orig), 0, 1);
		tmp_split_sched[2] = zsy_isl_union_map_set_range_dim_constant_val(tmp_split_sched[2], 2, 2);

		tmp_split_sched[0] = isl_union_map_intersect_domain(tmp_split_sched[0], isl_union_set_copy(tmp_split_domain[0]));
		tmp_split_sched[1] = isl_union_map_intersect_domain(tmp_split_sched[1], isl_union_set_copy(tmp_split_domain[1]));
		tmp_split_sched[2] = isl_union_map_intersect_domain(tmp_split_sched[2], isl_union_set_copy(tmp_split_domain[2]));

		total_sched = isl_union_map_union(tmp_split_sched[0], tmp_split_sched[1]);
		total_sched = isl_union_map_union(total_sched, tmp_split_sched[2]);
		zsy_codegen(total_sched);
	}
	zsy_codegen(tmp_split_sched[2]);

	return 0;
}


int main(int argc, char **argv)
{
	int i;
	struct isl_ctx *ctx;
	struct isl_options *options;

	options = isl_options_new_with_defaults();
	assert(options);
	argc = isl_options_parse(options, argc, argv, ISL_ARG_ALL);
	ctx = isl_ctx_alloc_with_options(&isl_options_args, options);

	printf("Space-Partition-Demo by zhaosiying12138@Institute of Advanced YanJia"
				" Technology, LiuYueCity Academy of Science\n");
	zsy_spacepar_compute_schedule(ctx);
	zsy_spacepar_isl_codegen(ctx);
	zsy_test_space_partition_Quillere_step1(ctx);
	zsy_test_space_partition_Quillere_step2(ctx);
	isl_ctx_free(ctx);
	return 0;
error:
	isl_ctx_free(ctx);
	return -1;
}
