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

#define STR_MAX 10

struct zsy_dep_graph
{
	int n;
	char **node_names;
	int *edge;
	int *visited;
};

static void zsy_dep_graph_init(struct zsy_dep_graph *dep_graph, isl_union_set *domain)
{
	int n = isl_union_set_n_set(domain);
	dep_graph->n = n;
	dep_graph->node_names = (char **)malloc(n * sizeof(char *));
	dep_graph->edge = (int *)calloc(n * n, sizeof(int));
	isl_map_list *domain_list = isl_union_set_get_set_list(domain);
	for (int i = 0; i < n; i++) {
		isl_set *tmp_set = isl_set_list_get_at(domain_list, i);
		const char *tmp_name = isl_set_get_tuple_name(tmp_set);
		dep_graph->node_names[i] = (char *)malloc(STR_MAX * sizeof(char));
		strncpy(dep_graph->node_names[i], tmp_name, STR_MAX - 1);
//		printf("%s\n", dep_graph->node_names[i]);
	}
	dep_graph->visited = (int *)calloc(n, sizeof(int));
}

static void zsy_dep_graph_clear_visited(struct zsy_dep_graph *dep_graph)
{
	for (int i = 0; i < dep_graph->n; i++) {
		dep_graph->visited[i] = 0;
	}
}

static int zsy_dep_graph_get_node_id(struct zsy_dep_graph *dep_graph, const char *node_name)
{
	for (int i = 0; i < dep_graph->n; i++) {
		if (strncmp(dep_graph->node_names[i], node_name, STR_MAX - 1) == 0)
			return i;
	}
	return -1;
}

static void zsy_dep_graph_add_edge(struct zsy_dep_graph *dep_graph, int id1, int id2)
{
	dep_graph->edge[id1 * dep_graph->n + id2] = 1;
}

static int zsy_dep_graph_check_edge(struct zsy_dep_graph *dep_graph, int id1, int id2)
{
	return dep_graph->edge[id1 * dep_graph->n + id2];
}

static void zsy_dep_graph_dump(struct zsy_dep_graph *dep_graph)
{
	printf("Dependece Graph Dump:\n");
	for (int i = 0; i < dep_graph->n; i++) {
		for (int j = 0; j < dep_graph->n; j++) {
			if (zsy_dep_graph_check_edge(dep_graph, i, j)) {
				printf("%s(%d) -> %s(%d)\n", dep_graph->node_names[i], i, dep_graph->node_names[j], j);
			}
		}
	}
}

void zsy_compute_dep_graph(struct zsy_dep_graph *dep_graph, isl_union_set *domain, isl_union_map *dep_all)
{
	zsy_dep_graph_init(dep_graph, domain);

	isl_map_list *map_list = isl_union_map_get_map_list(dep_all);
	for (int i = 0; i < isl_map_list_n_map(map_list); i++) {
		isl_map *tmp_map = isl_map_list_get_map(map_list, i);
		const char *node_source_name = isl_map_get_tuple_name(tmp_map, isl_dim_in);
		const char *node_sink_name = isl_map_get_tuple_name(tmp_map, isl_dim_out);
		int source_id = zsy_dep_graph_get_node_id(dep_graph, node_source_name);
		int sink_id = zsy_dep_graph_get_node_id(dep_graph, node_sink_name);
		zsy_dep_graph_add_edge(dep_graph, source_id, sink_id);
	}
	printf("\n");
	zsy_dep_graph_dump(dep_graph);
}

static int zsy_dep_graph_check_recurrence_call(struct zsy_dep_graph *dep_graph, int start_node_id)
{
	if (dep_graph->visited[start_node_id] == 1)
		return 1;
	dep_graph->visited[start_node_id] = 1;
	for (int i = 0; i < dep_graph->n; i++) {
		if (zsy_dep_graph_check_edge(dep_graph, start_node_id, i) == 1) {
			//printf("Check %s -> %s\n", dep_graph->node_names[start_node_id], dep_graph->node_names[i]);
			if (zsy_dep_graph_check_recurrence_call(dep_graph, i) == 1)
				return 1;
		}
	}
	dep_graph->visited[start_node_id] = 0;
	return 0;
}

int zsy_dep_graph_check_recurrence(struct zsy_dep_graph *dep_graph)
{
	zsy_dep_graph_clear_visited(dep_graph);
	for (int i = 0; i < dep_graph->n; i++) {
		if (zsy_dep_graph_check_recurrence_call(dep_graph, i) == 1)
			return 1;
	}
	return 0;
}

static int zsy_compute_max_common_loops(__isl_keep isl_basic_map *bmap, __isl_keep isl_union_map *S)
{
	isl_basic_set *bmap_domain = isl_basic_map_domain(isl_basic_map_copy(bmap));
	isl_size sched1_dim = isl_basic_set_dim(bmap_domain, isl_dim_set);
	isl_union_map *sched_domain = isl_union_map_intersect_domain(isl_union_map_copy(S), isl_union_set_from_basic_set(bmap_domain));
	isl_union_set *sched_domain_range = isl_union_map_range(sched_domain);
	isl_basic_set_list *sched1_list = isl_union_set_get_basic_set_list(sched_domain_range);
	assert(isl_basic_set_list_n_basic_set(sched1_list) == 1);
	isl_basic_set *sched1 = isl_basic_set_list_get_basic_set(sched1_list, 0);

	isl_basic_set *bmap_range = isl_basic_map_range(isl_basic_map_copy(bmap));
	isl_size sched2_dim = isl_basic_set_dim(bmap_range, isl_dim_set);
	isl_union_map *sched_range = isl_union_map_intersect_domain(isl_union_map_copy(S), isl_union_set_from_basic_set(bmap_range));
	isl_union_set *sched_range_range = isl_union_map_range(sched_range);
	isl_basic_set_list *sched2_list = isl_union_set_get_basic_set_list(sched_range_range);
	assert(isl_basic_set_list_n_basic_set(sched2_list) == 1);
	isl_basic_set *sched2 = isl_basic_set_list_get_basic_set(sched2_list, 0);
	
	isl_size sched_dim_min = sched1_dim < sched2_dim ? sched1_dim : sched2_dim;
	//printf("sched1_dim = %d, sched2_dim = %d\n", sched1_dim, sched2_dim);

	int max_common_loops = 0;
	isl_int tmp_val1, tmp_val2;
	isl_int_init(tmp_val1);
	isl_int_init(tmp_val2);
	for (int i = 0; i < sched_dim_min * 2; i += 2) {
		assert(isl_basic_set_plain_dim_is_fixed(sched1, i, &tmp_val1));
		assert(isl_basic_set_plain_dim_is_fixed(sched2, i, &tmp_val2));
		if (isl_int_eq(tmp_val1, tmp_val2)) {
			max_common_loops++;
			continue;
		} else {
			break;
		}
	}

	return max_common_loops;
}

static int zsy_compute_loop_carried(__isl_keep isl_basic_map *bmap, __isl_keep isl_union_map *S)
{
	isl_size common_loop_size = zsy_compute_max_common_loops(bmap, S);
	isl_basic_map *bmap_tmp = isl_basic_map_copy(bmap);
	isl_size dim_in_size = isl_basic_map_dim(bmap_tmp, isl_dim_in);
	isl_size dim_out_size = isl_basic_map_dim(bmap_tmp, isl_dim_out);
	isl_int tmp_val;
	isl_int_init(tmp_val);
	int i;

	bmap_tmp = isl_basic_map_project_out(bmap_tmp, isl_dim_in,  common_loop_size, dim_in_size - common_loop_size);
	bmap_tmp = isl_basic_map_project_out(bmap_tmp, isl_dim_out, common_loop_size, dim_out_size - common_loop_size);
	isl_basic_set *delta = isl_basic_map_deltas(bmap_tmp);
	//isl_basic_set_dump(delta);

	for (i = 0; i < common_loop_size; i++) {
		if (isl_basic_set_plain_dim_is_fixed(delta, i, &tmp_val)) {
			if (isl_int_is_zero(tmp_val)) {
				continue;
			}
		}
		break;
	}
	if (i == common_loop_size)
		i = -1;
	else
		++i;
	isl_basic_map_dump(bmap);
	printf("max_common_loops = %d, loop_carried = %d\n", common_loop_size, i);

	isl_basic_set_free(delta);
	return i;
}

static void zsy_dump_dependence(__isl_keep isl_union_map *dep, __isl_keep isl_union_map *S)
{
	isl_map_list *map_list = isl_union_map_get_map_list(dep);
	for (int i = 0; i < isl_map_list_n_map(map_list); i++) {
		isl_map *tmp_map = isl_map_list_get_map(map_list, i);
		isl_basic_map_list *tmp_bmap_list = isl_map_get_basic_map_list(tmp_map);
		for (int j = 0; j < isl_basic_map_list_n_basic_map(tmp_bmap_list); j++) {
			isl_basic_map *tmp_bmap = isl_basic_map_list_get_basic_map(tmp_bmap_list, j);
			zsy_compute_loop_carried(tmp_bmap, S);
		}
	}
}

int zsy_test_autovec(isl_ctx *ctx)
{
	const char *con, *d, *w, *r, *s;
	isl_set *CON;
	isl_union_set *D, *delta;
	isl_set *delta_set, *delta_set_lexmin, *delta_set_lexmax;
	isl_union_map *W, *R, *W_rev, *R_rev, *S, *S_le_S, *S_lt_S;
	isl_union_map *empty;
	isl_union_map *dep_raw, *dep_war, *dep_waw, *dep;
	isl_union_map *validity, *proximity, *coincidence;
	isl_union_map *schedule, *schedule_isl, *schedule_paper, *schedule_test;
	isl_schedule_constraints *sc;
	isl_schedule *sched;
	isl_ast_build *build;
	isl_ast_node *tree;

	isl_options_set_schedule_serialize_sccs(ctx, 1);
	con = "{ : }";
	d = "[N] -> { S1[i] : 1 <= i <= 100; S2[i, j] : 1 <= i, j <= 100; "
					" S3[i, j, k] : 1 <= i, j, k <= 100; S4[i, j] : 1 <= i, j <= 100 } ";
	w = "[N] -> { S1[i] -> X[i]; S2[i, j] -> B[j]; S3[i, j, k] -> A[j + 1, k]; S4[i, j] -> Y[i + j] }";
	r = "[N] -> { S1[i] -> Y[i]; S2[i, j] -> A[j, N]; S3[i, j, k] -> B[j]; S3[i, j, k] -> C[j, k]; S4[i, j] -> A[j + 1, N] }";
	s = "[N] -> { S1[i] -> [0, i, 0, 0, 0, 0, 0]; S2[i, j] -> [0, i, 1, j, 0, 0, 0]; "
					" S3[i, j, k] -> [0, i, 1, j, 1, k, 0]; S4[i, j] -> [0, i, 1, j, 2, 0, 0] }";

	CON = isl_set_read_from_str(ctx, con);
	D = isl_union_set_read_from_str(ctx, d);
	W = isl_union_map_read_from_str(ctx, w);
	R = isl_union_map_read_from_str(ctx, r);
	S = isl_union_map_read_from_str(ctx, s);

	W = isl_union_map_intersect_domain(W, isl_union_set_copy(D));
	R = isl_union_map_intersect_domain(R, isl_union_set_copy(D));
	S = isl_union_map_intersect_domain(S, isl_union_set_copy(D));

	build = isl_ast_build_from_context(isl_set_read_from_str(ctx, con));
	tree = isl_ast_build_node_from_schedule_map(build, isl_union_map_copy(S));
	printf("Before Transform:\n%s\n", isl_ast_node_to_C_str(tree));

	W_rev = isl_union_map_reverse(isl_union_map_copy(W));
	R_rev = isl_union_map_reverse(isl_union_map_copy(R));
	S_lt_S = isl_union_map_lex_lt_union_map(isl_union_map_copy(S), isl_union_map_copy(S));
	S_le_S = isl_union_map_lex_le_union_map(isl_union_map_copy(S), isl_union_map_copy(S));
	dep_raw = isl_union_map_apply_range(isl_union_map_copy(W), isl_union_map_copy(R_rev));
	dep_raw = isl_union_map_intersect(dep_raw, isl_union_map_copy(S_lt_S));
	dep_waw = isl_union_map_apply_range(isl_union_map_copy(W), isl_union_map_copy(W_rev));
	dep_waw = isl_union_map_intersect(dep_waw, isl_union_map_copy(S_lt_S));
	dep_war = isl_union_map_apply_range(isl_union_map_copy(R), isl_union_map_copy(W_rev));
	dep_war = isl_union_map_intersect(dep_war, isl_union_map_copy(S_le_S));

#if 1
	printf("\nRAW Dependence:\n");
	zsy_dump_dependence(dep_raw, S);
	printf("\nWAW Dependence:\n");
	zsy_dump_dependence(dep_waw, S);
	printf("\nWAR Dependence:\n");
	zsy_dump_dependence(dep_war, S);
#endif

#if 0
	dep = isl_union_map_union(isl_union_map_copy(dep_waw), isl_union_map_copy(dep_war));
	dep = isl_union_map_union(dep, isl_union_map_copy(dep_raw));


	isl_basic_map *t_map = isl_basic_map_read_from_str(ctx, " [N] -> { S3[i, j, k] -> S2[i', j'] : (k = N and j' = 1 + j and N > 0 and N <= 100 and i > 0 and i <= 100 and j > 0 and j <= 99 and i' > 0 and i' <= 100 and i' > i) } ");
	zsy_compute_loop_carried(t_map, S);
	

	t_map = isl_basic_map_read_from_str(ctx, " [N] -> { S3[i, j, k] -> S2[i', j'] : (k = N and i' = i and j' = 1 + j and N > 0 and N <= 100 and i > 0 and i <= 100 and j > 0 and j <= 99) } ");
	zsy_compute_loop_carried(t_map, S);

	t_map = isl_basic_map_read_from_str(ctx, " [N] -> { S3[i, j, k] -> S4[i', j'] : (k = N and i' = i and j' = j and N > 0 and N <= 100 and i > 0 and i <= 100 and j > 0 and j <= 100) } ");
	zsy_compute_loop_carried(t_map, S);


	validity = isl_union_map_copy(dep);
	coincidence = isl_union_map_copy(dep);
	proximity = isl_union_map_copy(dep);

	sc = isl_schedule_constraints_on_domain(isl_union_set_copy(D));
	sc = isl_schedule_constraints_set_context(sc, CON);
	sc = isl_schedule_constraints_set_validity(sc, validity);
	sc = isl_schedule_constraints_set_coincidence(sc, coincidence);
	sc = isl_schedule_constraints_set_proximity(sc, proximity);
	sched = isl_schedule_constraints_compute_schedule(sc);
	isl_schedule_dump(sched);
	schedule = isl_schedule_get_map(sched);
	printf("Schedule:\n");
	isl_union_map_dump(schedule);

//	tree = isl_ast_build_node_from_schedule_map(build, schedule);
//	printf("After Transform:\n%s\n", isl_ast_node_to_C_str(tree));
//	isl_ast_node_free(tree);
#endif

	return 0;
}

int zsy_test_schedule_tree1(isl_ctx *ctx)
{
	const char *d;
	isl_union_set *D;
	isl_schedule_node *node;
	isl_schedule *sched;
	const char *str;
	isl_multi_union_pw_aff *mupa;
	isl_union_set *uset;
	isl_union_set_list *filters;
	isl_ast_build *build;
	isl_ast_node *tree;

	d = "[N] -> { S1[i] : 1 <= i <= 100; S2[i, j] : 1 <= i, j <= 100; "
					" S3[i, j, k, l] : 1 <= i, j, k, l <= 100; S4[i, j] : 1 <= i, j <= 100 } ";
	D = isl_union_set_read_from_str(ctx, d);
	node = isl_schedule_node_from_domain(D);
	node = isl_schedule_node_child(node, 0);

	str = "[N] -> [{ S1[i] -> [i]; S2[i, j] -> [i]; S3[i, j, k, l] -> [i]; S4[i, j] -> [i] }]";
	mupa = isl_multi_union_pw_aff_read_from_str(ctx, str);
	node = isl_schedule_node_insert_partial_schedule(node, mupa);
	node = isl_schedule_node_band_set_permutable(node, 0);
	node = isl_schedule_node_band_member_set_coincident(node, 0, 0);
	node = isl_schedule_node_child(node, 0);

	str = "{ S1[i] }";
	uset = isl_union_set_read_from_str(ctx, str);
	filters = isl_union_set_list_from_union_set(uset);
	str = "{ S2[i, j]; S3[i, j, k, l]; S4[i, j] }";
	uset = isl_union_set_read_from_str(ctx, str);
	filters = isl_union_set_list_add(filters, uset);
	node = isl_schedule_node_insert_sequence(node, filters);
	node = isl_schedule_node_grandchild(node, 1, 0);

	str = "[N] -> [{ S2[i, j] -> [j]; S3[i, j, k, l] -> [j]; S4[i, j] -> [j] }]";
	mupa = isl_multi_union_pw_aff_read_from_str(ctx, str);
	node = isl_schedule_node_insert_partial_schedule(node, mupa);
	node = isl_schedule_node_band_set_permutable(node, 0);
	node = isl_schedule_node_band_member_set_coincident(node, 0, 0);
	node = isl_schedule_node_child(node, 0);

	str = "{ S2[i, j] }";
	uset = isl_union_set_read_from_str(ctx, str);
	filters = isl_union_set_list_from_union_set(uset);
	str = "{ S3[i, j, k, l] }";
	uset = isl_union_set_read_from_str(ctx, str);
	filters = isl_union_set_list_add(filters, uset);
	str = "{ S4[i, j] }";
	uset = isl_union_set_read_from_str(ctx, str);
	filters = isl_union_set_list_add(filters, uset);
	node = isl_schedule_node_insert_sequence(node, filters);
	node = isl_schedule_node_grandchild(node, 1, 0);

	str = "[N] -> [{ S3[i, j, k, l] -> [k] }, { S3[i, j, k, l] -> [l] }]";
	mupa = isl_multi_union_pw_aff_read_from_str(ctx, str);
	node = isl_schedule_node_insert_partial_schedule(node, mupa);
	node = isl_schedule_node_band_set_permutable(node, 0);
	node = isl_schedule_node_band_member_set_coincident(node, 0, 0);
	node = isl_schedule_node_child(node, 0);

	node = isl_schedule_node_root(node);
	sched = isl_schedule_node_get_schedule(node);
	printf("Before Transform:\n");
	isl_schedule_dump(sched);
	build = isl_ast_build_from_context(isl_set_read_from_str(ctx, "{ : }"));
	tree = isl_ast_build_node_from_schedule(build, sched);
	printf("\n\n%s\n", isl_ast_node_to_C_str(tree));

	return 0;
}

int zsy_test_schedule_tree2(isl_ctx *ctx)
{
	const char *d;
	isl_union_set *D;
	isl_schedule_node *node;
	isl_schedule *sched;
	const char *str;
	isl_multi_union_pw_aff *mupa;
	isl_union_set *uset;
	isl_union_set_list *filters;
	isl_ast_build *build;
	isl_ast_node *tree;

	d = "[N] -> { S1[i] : 1 <= i <= 100; S2[i, j] : 1 <= i <= 100 and 1 <= j <= 200; "
					" S3[i, j, k, l] : 1 <= i <= 100 and 1 <= j <= 200 and 1 <= k <= 300 and 1 <= l <= 400; S4[i, j] : 1 <= i <= 100 and 1 <= j <= 200 } ";
	D = isl_union_set_read_from_str(ctx, d);
	node = isl_schedule_node_from_domain(D);
	node = isl_schedule_node_child(node, 0);

	str = "{ S2[i, j]; S3[i, j, k, l]; S4[i, j] }";
	uset = isl_union_set_read_from_str(ctx, str);
	filters = isl_union_set_list_from_union_set(uset);
	str = "{ S1[i] }";
	uset = isl_union_set_read_from_str(ctx, str);
	filters = isl_union_set_list_add(filters, uset);
	node = isl_schedule_node_insert_sequence(node, filters);

	node = isl_schedule_node_grandchild(node, 0, 0);
	str = "[N] -> [{ S2[i, j] -> [i]; S3[i, j, k, l] -> [i]; S4[i, j] -> [i] }]";
	mupa = isl_multi_union_pw_aff_read_from_str(ctx, str);
	node = isl_schedule_node_insert_partial_schedule(node, mupa);
	node = isl_schedule_node_band_set_permutable(node, 0);
	node = isl_schedule_node_band_member_set_coincident(node, 0, 0);
//	node = isl_schedule_node_insert_mark(node, (void *)0x12138);
	node = isl_schedule_node_grandparent(node);

	node = isl_schedule_node_grandchild(node, 1, 0);
	str = "[N] -> [{ S1[i] -> [i] }]";
	mupa = isl_multi_union_pw_aff_read_from_str(ctx, str);
	node = isl_schedule_node_insert_partial_schedule(node, mupa);
	node = isl_schedule_node_band_set_permutable(node, 1);
	node = isl_schedule_node_band_member_set_coincident(node, 0, 1);
	node = isl_schedule_node_grandparent(node);

	node = isl_schedule_node_grandchild(node, 0, 0);
	node = isl_schedule_node_child(node, 0);
	str = "{ S2[i, j]; S3[i, j, k, l] }";
	uset = isl_union_set_read_from_str(ctx, str);
	filters = isl_union_set_list_from_union_set(uset);
	str = "{ S4[i, j] }";
	uset = isl_union_set_read_from_str(ctx, str);
	filters = isl_union_set_list_add(filters, uset);
	node = isl_schedule_node_insert_sequence(node, filters);

	node = isl_schedule_node_grandchild(node, 0, 0);
	str = "[N] -> [{ S2[i, j] -> [j]; S3[i, j, k, l] -> [j] }]";
	mupa = isl_multi_union_pw_aff_read_from_str(ctx, str);
	node = isl_schedule_node_insert_partial_schedule(node, mupa);
	node = isl_schedule_node_band_set_permutable(node, 0);
	node = isl_schedule_node_band_member_set_coincident(node, 0, 0);
	node = isl_schedule_node_grandparent(node);

	node = isl_schedule_node_grandchild(node, 1, 0);
	str = "[N] -> [{ S4[i, j] -> [j] }]";
	mupa = isl_multi_union_pw_aff_read_from_str(ctx, str);
	node = isl_schedule_node_insert_partial_schedule(node, mupa);
	node = isl_schedule_node_band_set_permutable(node, 1);
	node = isl_schedule_node_band_member_set_coincident(node, 0, 1);
	node = isl_schedule_node_grandparent(node);

	node = isl_schedule_node_grandchild(node, 0, 0);
	node = isl_schedule_node_child(node, 0);
	str = "{ S2[i, j] }";
	uset = isl_union_set_read_from_str(ctx, str);
	filters = isl_union_set_list_from_union_set(uset);
	str = "{ S3[i, j, k, l] }";
	uset = isl_union_set_read_from_str(ctx, str);
	filters = isl_union_set_list_add(filters, uset);
	node = isl_schedule_node_insert_sequence(node, filters);

	node = isl_schedule_node_grandchild(node, 1, 0);
	str = "[N] -> [{ S3[i, j, k, l] -> [k] }, { S3[i, j, k, l] -> [l] }]";
	mupa = isl_multi_union_pw_aff_read_from_str(ctx, str);
	node = isl_schedule_node_insert_partial_schedule(node, mupa);
	node = isl_schedule_node_band_set_permutable(node, 1);
	node = isl_schedule_node_band_member_set_coincident(node, 0, 1);
	node = isl_schedule_node_band_member_set_coincident(node, 1, 1);
	node = isl_schedule_node_grandparent(node);

	node = isl_schedule_node_root(node);
	sched = isl_schedule_node_get_schedule(node);
	printf("\n\nAfter Transform:\n");
	isl_schedule_dump(sched);
	build = isl_ast_build_from_context(isl_set_read_from_str(ctx, "{ : }"));
	tree = isl_ast_build_node_from_schedule(build, sched);
//	isl_ast_node_dump(tree);
	printf("\n\n%s\n", isl_ast_node_to_C_str(tree));

	return 0;
}

int zsy_test_check_recurrence(isl_ctx *ctx)
{
	const char *d, *w, *r, *s;
	isl_union_set *D, *delta;
	isl_union_map *W, *R, *W_rev, *R_rev, *S, *S_le_S, *S_lt_S;
	isl_union_map *dep_raw, *dep_war, *dep_waw, *dep_all;
	struct zsy_dep_graph dep_graph;
#define SCALER_EXTENSION 0
#if SCALER_EXTENSION
	d = "[N] -> { S1[i] : 1 <= i <= N; S2[i] : 1 <= i <= N; S3[i] : 1 <= i <= N; }";
	w = "[N] -> { S1[i] -> A[i]; S2[i] -> Y[i]; S3[i] -> A[i]; }";
	r = "[N] -> { S1[i] -> A[i - 1]; S1[i] -> X[]; S2[i] -> A[i]; S2[i] -> Z[]; S3[i] -> B[i]; S3[i] -> C[]; }";
	s = "[N] -> { S1[i] -> [0, i, 0]; S2[i] -> [0, i, 1]; S3[i] -> [0, i, 2]; }";
#else
	d = "[N] -> { S1[i] : 1 <= i <= N }";
	w = "[N] -> { S1[i] -> A[i]; }";
	r = "[N] -> { S1[i] -> A[i]; }";
	s = "[N] -> { S1[i] -> [0, i, 0] }";
#endif
	D = isl_union_set_read_from_str(ctx, d);
	W = isl_union_map_read_from_str(ctx, w);
	R = isl_union_map_read_from_str(ctx, r);
	S = isl_union_map_read_from_str(ctx, s);

	W = isl_union_map_intersect_domain(W, isl_union_set_copy(D));
	R = isl_union_map_intersect_domain(R, isl_union_set_copy(D));
	S = isl_union_map_intersect_domain(S, isl_union_set_copy(D));

	W_rev = isl_union_map_reverse(isl_union_map_copy(W));
	R_rev = isl_union_map_reverse(isl_union_map_copy(R));
	S_lt_S = isl_union_map_lex_lt_union_map(isl_union_map_copy(S), isl_union_map_copy(S));
	S_le_S = isl_union_map_lex_le_union_map(isl_union_map_copy(S), isl_union_map_copy(S));
	dep_raw = isl_union_map_apply_range(isl_union_map_copy(W), isl_union_map_copy(R_rev));
	dep_raw = isl_union_map_intersect(dep_raw, isl_union_map_copy(S_lt_S));
	dep_waw = isl_union_map_apply_range(isl_union_map_copy(W), isl_union_map_copy(W_rev));
	dep_waw = isl_union_map_intersect(dep_waw, isl_union_map_copy(S_lt_S));
	dep_war = isl_union_map_apply_range(isl_union_map_copy(R), isl_union_map_copy(W_rev));
	dep_war = isl_union_map_intersect(dep_war, isl_union_map_copy(S_le_S));

	printf("\nRAW Dependence:\n");
	zsy_dump_dependence(dep_raw, S);
	printf("\nWAW Dependence:\n");
	zsy_dump_dependence(dep_waw, S);
	printf("\nWAR Dependence:\n");
	zsy_dump_dependence(dep_war, S);

	dep_all = isl_union_map_union(isl_union_map_copy(dep_raw), isl_union_map_copy(dep_waw));
	dep_all = isl_union_map_union(dep_all, dep_war);
	zsy_compute_dep_graph(&dep_graph, D, dep_all);
	int is_recurrence = zsy_dep_graph_check_recurrence(&dep_graph);
	printf("Check Recurrence: %d\n", is_recurrence);
	return 0;
}

__isl_give isl_pw_qpolynomial *zsy_isl_pw_qpolynomial_get_value_one_with_same_space(__isl_keep isl_pw_qpolynomial *pw_qp)
{
	isl_space *space = isl_pw_qpolynomial_get_domain_space(pw_qp);
	return isl_pw_qpolynomial_from_qpolynomial(isl_qpolynomial_one_on_domain(space));
}

__isl_give isl_pw_qpolynomial *zsy_isl_pw_qpolynomial_substitute(
	__isl_take isl_pw_qpolynomial *pw_qp,
	enum isl_dim_type type, unsigned first, unsigned n,
	__isl_keep isl_qpolynomial **subs)
{
	isl_qpolynomial *qp = isl_pw_qpolynomial_as_qpolynomial(pw_qp);
	qp = isl_qpolynomial_substitute(qp, type, first, n, subs);
	return isl_pw_qpolynomial_from_qpolynomial(qp);
}

int zsy_test_aff1(isl_ctx *ctx)
{
	isl_pw_qpolynomial *one;
	isl_pw_qpolynomial *theta1 = isl_pw_qpolynomial_read_from_str(ctx,
								"[u1_0, u1_1, u1_2] -> { theta[i, j, n] -> (u1_0 + u1_1 * i + u1_2 * (n - i)) }");
	isl_pw_qpolynomial *theta2 = isl_pw_qpolynomial_read_from_str(ctx,
		"[u2_0, u2_1, u2_2, u2_3, u2_4] -> { theta[i, j, n] ->"
		" (u2_0 + u2_1 * i + u2_2 * (n - i) + u2_3 * j + u2_4 * (n - j)) }");
	isl_pw_qpolynomial *result1 = isl_pw_qpolynomial_sub(isl_pw_qpolynomial_copy(theta2), isl_pw_qpolynomial_copy(theta1));
	one = zsy_isl_pw_qpolynomial_get_value_one_with_same_space(result1);
	result1 = isl_pw_qpolynomial_sub(result1, one);
	isl_pw_qpolynomial *farkas1 = isl_pw_qpolynomial_read_from_str(ctx,
		"[r1_0, r1_1, r1_2, r1_3, r1_4, r1_5] -> { theta[i, j, n] -> "
		"(r1_0 + r1_1 * i + r1_2 * (n - i) + r1_3 * j + r1_4 * (n - j) - r1_5 * j) }");
	result1 = isl_pw_qpolynomial_sub(result1, farkas1);
	isl_pw_qpolynomial_dump(isl_pw_qpolynomial_coalesce(result1));

	isl_qpolynomial *h2_0 = isl_pw_qpolynomial_as_qpolynomial(isl_pw_qpolynomial_read_from_str(ctx,
								"[u2_0, u2_1, u2_2, u2_3, u2_4] -> { theta[i, j, n] -> (i) }"));
	isl_qpolynomial *h2_1 = isl_pw_qpolynomial_as_qpolynomial(isl_pw_qpolynomial_read_from_str(ctx,
								"[u2_0, u2_1, u2_2, u2_3, u2_4] -> { theta[i, j, n] -> (j - 1) }"));
	isl_pw_qpolynomial *theta2_minus1 = zsy_isl_pw_qpolynomial_substitute(isl_pw_qpolynomial_copy(theta2),
										isl_dim_in, 0, 1, &h2_0);
	theta2_minus1 = zsy_isl_pw_qpolynomial_substitute(theta2_minus1, isl_dim_in, 1, 1, &h2_1);
	isl_pw_qpolynomial *result2 = isl_pw_qpolynomial_sub(isl_pw_qpolynomial_copy(theta2), theta2_minus1);
	one = zsy_isl_pw_qpolynomial_get_value_one_with_same_space(result2);
	result2 = isl_pw_qpolynomial_sub(result2, one);
	isl_pw_qpolynomial_dump(result2);
}

int zsy_test_aff2(isl_ctx *ctx)
{
	isl_pw_qpolynomial *one;
	isl_pw_qpolynomial *theta1 = isl_pw_qpolynomial_read_from_str(ctx,
		"[u0, u1, u2, u3, u4] -> { theta[i, j, n] -> (u0 + u1 * i + u2 * (n - i) + u3 * j + u4 * (i - j)) }");
	isl_qpolynomial *h1_0 = isl_pw_qpolynomial_as_qpolynomial(isl_pw_qpolynomial_read_from_str(ctx,
								"[u0, u1, u2, u3, u4] -> { theta[i, j, n] -> (i) }"));
	isl_qpolynomial *h1_1 = isl_pw_qpolynomial_as_qpolynomial(isl_pw_qpolynomial_read_from_str(ctx,
								"[u0, u1, u2, u3, u4] -> { theta[i, j, n] -> (j - 1) }"));
	isl_pw_qpolynomial *theta1_dep1 = zsy_isl_pw_qpolynomial_substitute(isl_pw_qpolynomial_copy(theta1),
										isl_dim_in, 0, 1, &h1_0);
	theta1_dep1 = zsy_isl_pw_qpolynomial_substitute(theta1_dep1, isl_dim_in, 1, 1, &h1_1);
	isl_pw_qpolynomial *result1 = isl_pw_qpolynomial_sub(isl_pw_qpolynomial_copy(theta1), theta1_dep1);
	one = zsy_isl_pw_qpolynomial_get_value_one_with_same_space(result1);
	result1 = isl_pw_qpolynomial_sub(result1, one);
	isl_pw_qpolynomial_dump(result1);

	isl_qpolynomial *h2_0_dst = isl_pw_qpolynomial_as_qpolynomial(isl_pw_qpolynomial_read_from_str(ctx,
								"[u0, u1, u2, u3, u4] -> { theta[i, j, n] -> (i) }"));
	isl_qpolynomial *h2_1_dst = isl_pw_qpolynomial_as_qpolynomial(isl_pw_qpolynomial_read_from_str(ctx,
								"[u0, u1, u2, u3, u4] -> { theta[i, j, n] -> (0) }"));
	isl_pw_qpolynomial *theta1_dep2_dst = zsy_isl_pw_qpolynomial_substitute(isl_pw_qpolynomial_copy(theta1),
										isl_dim_in, 0, 1, &h2_0_dst);
	theta1_dep2_dst = zsy_isl_pw_qpolynomial_substitute(theta1_dep2_dst, isl_dim_in, 1, 1, &h2_1_dst);
	isl_pw_qpolynomial_dump(theta1_dep2_dst);
	isl_qpolynomial *h2_0_src = isl_pw_qpolynomial_as_qpolynomial(isl_pw_qpolynomial_read_from_str(ctx,
								"[u0, u1, u2, u3, u4] -> { theta[i, j, n] -> (i - 1) }"));
	isl_qpolynomial *h2_1_src = isl_pw_qpolynomial_as_qpolynomial(isl_pw_qpolynomial_read_from_str(ctx,
								"[u0, u1, u2, u3, u4] -> { theta[i, j, n] -> (i - 1) }"));
	isl_pw_qpolynomial *theta1_dep2_src = zsy_isl_pw_qpolynomial_substitute(isl_pw_qpolynomial_copy(theta1),
										isl_dim_in, 0, 1, &h2_0_src);
	theta1_dep2_src = zsy_isl_pw_qpolynomial_substitute(theta1_dep2_src, isl_dim_in, 1, 1, &h2_1_src);
	isl_pw_qpolynomial_dump(theta1_dep2_src);
	isl_pw_qpolynomial *result2 = isl_pw_qpolynomial_sub(theta1_dep2_dst, theta1_dep2_src);
	one = zsy_isl_pw_qpolynomial_get_value_one_with_same_space(result2);
	result2 = isl_pw_qpolynomial_sub(result2, one);
	isl_pw_qpolynomial *farkas1 = isl_pw_qpolynomial_read_from_str(ctx,
		"[r0, r1, r2, r3, r4] -> { theta[i, j, n] -> "
		"(r0 + r1 * (i - 1) + r2 * (n - i) + r3 * j - r4 * j) }");
	result2 = isl_pw_qpolynomial_sub(result2, farkas1);
	isl_pw_qpolynomial_dump(result2);
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

	printf("Feautrier Demo written by zhaosiying12138@Institute of Advanced YanJia"
				" Technology, LiuYueCity Academy of Science\n");
//	zsy_test_autovec(ctx);
//	zsy_test_schedule_tree1(ctx);
//	zsy_test_schedule_tree2(ctx);
//	zsy_test_check_recurrence(ctx);
	zsy_test_aff1(ctx);
	zsy_test_aff2(ctx);

	isl_ctx_free(ctx);
	return 0;
error:
	isl_ctx_free(ctx);
	return -1;
}
