#include <stdio.h>
#include <stdlib.h>
#include <time.h>

extern void test_c_rb();
extern void test_c_rb2(void);
void test_rbt_string(void);
void test_rbt_string2(void);

#if defined(_MSC_VER)
#if !defined(_CRTDBG_MAP_ALLOC)
#define _CRTDBG_MAP_ALLOC
#endif
#include <crtdbg.h>
#include <stdlib.h>

#define MEM_CHECK_BEGIN()                                             \
    do {                                                              \
        _CrtSetDbgFlag(_CRTDBG_ALLOC_MEM_DF | _CRTDBG_LEAK_CHECK_DF); \
    } while (0)
#define MEM_CHECK_BREAK_ALLOC(x) \
    do {                         \
        _CrtSetBreakAlloc(x);    \
    } while (0)
#define MEM_CHECK_DUMP_LEAKS() \
    do {                       \
        _CrtDumpMemoryLeaks(); \
    } while (0)
#else
#define MEM_CHECK_BEGIN() \
    do {                  \
    } while (0)
#define MEM_CHECK_BREAK_ALLOC(x) \
    do {                         \
        (void)x;                 \
    } while (0)
#define MEM_CHECK_DUMP_LEAKS() \
    do {                       \
    } while (0)
#endif

void on_atexit(void)
{
    MEM_CHECK_DUMP_LEAKS();
}

int main(int argc, char **argv)
{
    clock_t t = clock();
    (void)argc;
    (void)argv;
    MEM_CHECK_BEGIN();
    atexit(on_atexit);
    {
        printf("Performing test for red-black tree\n");
        test_c_rb();
        test_c_rb2();
        test_rbt_string();
        test_rbt_string2();
    }
    {
        /* in seconds */
        double time_taken = (((double)clock() - (double)t)) / CLOCKS_PER_SEC;
        printf("tests took %f seconds to execute \n", time_taken);
    }
    return 0;
}

#include "rb-tree.h"

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static const void *get_key(struct rbt_tree *tree, const struct rbt_node *node)
{
    (void)tree;
    if (node)
        return rbt_node_get_key(node);
    return (void *)0;
}

int compare_rb_e(const void *l, const void *r)
{
    int left  = *(int *)l;
    int right = *(int *)r;

    if (left < right) {
        return -1;
    } else if (left == right) {
        return 0;
    } else {
        return 1;
    }
}

typedef struct test_data_tree {
    int element;
    int left;
    int right;
    int parent;
    rbt_color color;
} TS;

static void retrieve_values(const struct rbt_node *v, TS *data,
                            struct rbt_tree *tree)
{
    struct rbt_node *x = NULL;
    data->element      = *(int *)get_key(tree, v);
    data->color        = rbt_node_get_color(v);
    if ((x = rbt_node_get_left(v)))
        data->left = *(int *)get_key(tree, x);
    if ((x = rbt_node_get_right(v)))
        data->right = *(int *)get_key(tree, x);
    if ((x = rbt_node_get_parent(v)))
        data->parent = *(int *)get_key(tree, x);
}

static void test_each_elements(TS *lhs, TS *rhs)
{
    assert(lhs->element == rhs->element);
    assert(lhs->color == rhs->color);
    assert(lhs->left == rhs->left);
    assert(lhs->right == rhs->right);
    assert(lhs->parent == rhs->parent);
    (void)lhs;
    (void)rhs;
}

static void test_all_elements(struct rbt_tree *tree, TS ts[], int size)
{
    int i = 0;
    for (i = 0; i < size; i++) {
        struct test_data_tree data;
        const struct rbt_node *v = rbt_tree_find(tree, &ts[i].element);
        memset(&data, 0, sizeof(data));
        retrieve_values(v, &data, tree);
        test_each_elements(&data, &ts[i]);
    }
}

static struct rbt_tree *create_tree(TS ts[], int size)
{
    int i                 = 0;
    struct rbt_tree *tree = rbt_tree_create(compare_rb_e, (rbt_node_destruct)0);
    for (i = 0; i < size; i++) {
        rbt_tree_insert(tree, &(ts[i].element), sizeof((ts[i].element)));
    }
    return tree;
}

void test_c_rb()
{
    int size;
    int size_after_delete;
    int i = 0;
    struct rbt_tree *tree;
    rbt_status s;

    TS ts[] = {
        { 15, 6, 18, 0, rbt_black },   { 6, 3, 9, 15, rbt_red },
        { 18, 17, 20, 15, rbt_black }, { 3, 2, 4, 6, rbt_black },
        { 7, 0, 0, 9, rbt_red },       { 17, 0, 0, 18, rbt_red },
        { 20, 0, 0, 18, rbt_red },     { 2, 0, 0, 3, rbt_red },
        { 4, 0, 0, 3, rbt_red },       { 13, 0, 0, 9, rbt_red },
        { 9, 7, 13, 6, rbt_black },
    };
    TS ts_delete_leaf_13[] = {
        { 15, 6, 18, 0, rbt_black },   { 6, 3, 9, 15, rbt_red },
        { 18, 17, 20, 15, rbt_black }, { 3, 2, 4, 6, rbt_black },
        { 7, 0, 0, 9, rbt_red },       { 17, 0, 0, 18, rbt_red },
        { 20, 0, 0, 18, rbt_red },     { 2, 0, 0, 3, rbt_red },
        { 4, 0, 0, 3, rbt_red },       { 9, 7, 0, 6, rbt_black },
    };
    TS ts_delete_9[] = {
        { 15, 6, 18, 0, rbt_black },   { 6, 3, 7, 15, rbt_red },
        { 18, 17, 20, 15, rbt_black }, { 3, 2, 4, 6, rbt_black },
        { 7, 0, 0, 6, rbt_black },     { 17, 0, 0, 18, rbt_red },
        { 20, 0, 0, 18, rbt_red },     { 2, 0, 0, 3, rbt_red },
        { 4, 0, 0, 3, rbt_red },
    };
    TS ts_delete_15[] = {
        { 6, 3, 7, 17, rbt_red },    { 18, 0, 20, 17, rbt_black },
        { 3, 2, 4, 6, rbt_black },   { 7, 0, 0, 6, rbt_black },
        { 17, 6, 18, 0, rbt_black }, { 20, 0, 0, 18, rbt_red },
        { 2, 0, 0, 3, rbt_red },     { 4, 0, 0, 3, rbt_red },
    };
    TS ts_insert_1[] = {
        { 6, 3, 17, 0, rbt_black }, { 18, 0, 20, 17, rbt_black },
        { 3, 2, 4, 6, rbt_red },    { 7, 0, 0, 17, rbt_black },
        { 17, 7, 18, 6, rbt_red },  { 20, 0, 0, 18, rbt_red },
        { 2, 1, 0, 3, rbt_black },  { 4, 0, 0, 3, rbt_black },
        { 1, 0, 0, 2, rbt_red },
    };

    size = (sizeof(ts) / sizeof(TS));
    tree = create_tree(ts, size);
    test_all_elements(tree, ts, size);
    {
        i                 = 13;
        size              = (sizeof(ts) / sizeof(TS));
        size_after_delete = (sizeof(ts_delete_leaf_13) / sizeof(TS));
        s                 = rbt_tree_remove_node(tree, &i);
        assert(s == RBT_STATUS_SUCCESS);
        test_all_elements(tree, ts_delete_leaf_13, size_after_delete);
    }
    {
        i                 = 9;
        size_after_delete = (sizeof(ts_delete_9) / sizeof(TS));
        s                 = rbt_tree_remove_node(tree, &i);
        assert(s == RBT_STATUS_SUCCESS);
        test_all_elements(tree, ts_delete_9, size_after_delete);
    }
    {
        i                 = 15;
        size_after_delete = (sizeof(ts_delete_15) / sizeof(TS));
        s                 = rbt_tree_remove_node(tree, &i);
        assert(s == RBT_STATUS_SUCCESS);
        test_all_elements(tree, ts_delete_15, size_after_delete);
    }
    {
        int i = 1;
        rbt_tree_insert(tree, &i, sizeof(i));
        size_after_delete = (sizeof(ts_insert_1) / sizeof(TS));
        test_all_elements(tree, ts_insert_1, size_after_delete);
    }
    {
        rbt_tree_destroy(tree);
    }
}

void test_c_rb2(void)
{
    struct rbt_node *node;
    int i;
    struct rbt_tree *t = rbt_tree_create(compare_rb_e, NULL);

    srand((unsigned int)time(NULL));

    for (i = 0; i < 5000; i++) {
        int x = rand() % 10000;
        if (RBT_STATUS_KEY_DUPLICATE == rbt_tree_insert(t, &x, sizeof(x))) {
            continue;
        }
        node = (struct rbt_node *)rbt_tree_find(t, &x);
        assert(*((int *)rbt_node_get_key(node)) == x);
    }
    for (i = 0; i < 60000; i++) {
        int x = rand() % 10000;
        rbt_tree_remove_node(t, &x);
    }
    rbt_tree_destroy(t);
}

char *strArr[] = {
    "abcd1234",
    "good_idea",
    "just",
    "ding",
};

int str_ptr_compare(const void *lhs, const void *rhs)
{
    char *left  = *(char **)lhs;
    char *right = *(char **)rhs;
    return strcmp(left, right);
}

void string_ptr_destroy(void *p)
{
    char *_p = *(char **)p;
    free(_p);
}

void node_walk_cb3(struct rbt_node *node, void *p)
{
    char *str = *(char **)rbt_node_get_key(node);
    printf("%s\n", str);
    (void)p;
}

void test_rbt_string(void)
{
    const struct rbt_node *node;
    size_t i;
    struct rbt_tree *t = rbt_tree_create(str_ptr_compare, string_ptr_destroy);
    for (i = 0; i < sizeof(strArr) / sizeof(strArr[0]); i++) {
        char *y;
        char *p = strdup(strArr[i]);
        if (0 != rbt_tree_insert(t, &p, sizeof(p))) {
            continue;
        }
        node = rbt_tree_find(t, &strArr[i]);
        y    = *(char **)rbt_node_get_key(node);
        assert(strcmp(y, strArr[i]) == 0);
    }

    printf("\n==== test_rbt_string ====\n");
    rbt_inorder_walk(t, node_walk_cb3, NULL);

    rbt_tree_destroy(t);
}

int string_ptr_compare2(const void *lhs, const void *rhs)
{
    return strcmp((char *)lhs, (char *)rhs);
}

void node_walk_cb4(struct rbt_node *node, void *p)
{
    char *str = (char *)rbt_node_get_key(node);
    printf("%s\n", str);
    (void)p;
}

void test_rbt_string2(void)
{
    const struct rbt_node *node;
    rbt_status s;
    size_t i;
    struct rbt_tree *t = rbt_tree_create(string_ptr_compare2, NULL);
    for (i = 0; i < sizeof(strArr) / sizeof(strArr[0]); i++) {
        char *y;
        char *p = strArr[i];
        if (RBT_STATUS_SUCCESS != rbt_tree_insert(t, p, strlen(p) + 1)) {
            continue;
        }
        node = rbt_tree_find(t, strArr[i]);
        y    = (char *)rbt_node_get_key(node);
        assert(strcmp(y, strArr[i]) == 0);
    }

    s = rbt_tree_remove_node(t, strArr[0]);
    assert(s == RBT_STATUS_SUCCESS);

    printf("\n==== test_rbt_string2 ====\n");
    rbt_inorder_walk(t, node_walk_cb4, NULL);

    rbt_tree_destroy(t);
}
