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

	printf("\nCompute schedule for Space-Partition-Constraints Demo:\n");
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

	printf("Codegen with ISL-native-ast-build:\n");
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
	isl_ctx_free(ctx);
	return 0;
error:
	isl_ctx_free(ctx);
	return -1;
}
