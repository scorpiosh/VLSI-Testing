#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>

/* ---------------- Node set (which node ids exist) ---------------- */
typedef struct {
    unsigned char *bits;  /* index by node id: 1 = present */
    size_t cap;           /* capacity (index 0 unused) */
} NodeSet;

static void die(const char *msg) { fprintf(stderr, "Error: %s\n", msg); exit(EXIT_FAILURE); }
static void *xrealloc(void *p, size_t n) { void *q = realloc(p, n); if (!q) die("out of memory"); return q; }

static void ns_init(NodeSet *s, size_t initial_cap) {
    s->cap = (initial_cap < 2 ? 2 : initial_cap);
    s->bits = (unsigned char*)calloc(s->cap, 1);
    if (!s->bits) die("out of memory");
}
static void ns_ensure(NodeSet *s, size_t need) {
    if (need < s->cap) return;
    size_t newcap = s->cap;
    while (newcap <= need) newcap *= 2;
    s->bits = (unsigned char*)xrealloc(s->bits, newcap);
    memset(s->bits + s->cap, 0, newcap - s->cap);
    s->cap = newcap;
}
static void ns_add(NodeSet *s, long id) {
    if (id <= 0) return;
    ns_ensure(s, (size_t)id + 1);
    s->bits[id] = 1;
}

/* ---------------- Fanout map: stem -> list of distinct branches ---------------- */
typedef struct FanList {
    long *v;
    size_t n, cap;
} FanList;

static FanList *fan_map = NULL;  /* index by node id */
static size_t fan_map_cap = 0;

static void fan_ensure(size_t need) {
    if (need < fan_map_cap) return;
    size_t newcap = (fan_map_cap ? fan_map_cap : 1024);
    while (newcap <= need) newcap *= 2;
    fan_map = (FanList*)xrealloc(fan_map, newcap * sizeof(FanList));
    /* init new range */
    for (size_t i = fan_map_cap; i < newcap; ++i) {
        fan_map[i].v = NULL; fan_map[i].n = 0; fan_map[i].cap = 0;
    }
    fan_map_cap = newcap;
}
static int fan_contains(const FanList *fl, long val) {
    for (size_t i = 0; i < fl->n; ++i) if (fl->v[i] == val) return 1;
    return 0;
}
static void fan_add_edge(long stem, long branch) {
    if (stem <= 0 || branch <= 0) return;
    fan_ensure((size_t)stem + 1);
    FanList *fl = &fan_map[stem];
    if (!fan_contains(fl, branch)) {
        if (fl->n >= fl->cap) {
            size_t newcap = fl->cap ? fl->cap * 2 : 4;
            fl->v = (long*)xrealloc(fl->v, newcap * sizeof(long));
            fl->cap = newcap;
        }
        fl->v[fl->n++] = branch;
    }
}

/* ---------------- Parsing helpers ---------------- */
static int is_gate_token(const char *t) {
    if (!t) return 0;
    char u[16]; size_t i=0;
    for (; t[i] && i+1 < sizeof(u); ++i) u[i] = (char)toupper((unsigned char)t[i]);
    u[i] = '\0';
    return (!strcmp(u,"AND") || !strcmp(u,"OR") || !strcmp(u,"NAND") || !strcmp(u,"NOR"));
}
static int is_kw(const char *t, const char *kw) {
    if (!t) return 0;
    char u[16]; size_t i=0;
    for (; t[i] && i+1 < sizeof(u); ++i) u[i] = (char)toupper((unsigned char)t[i]);
    u[i] = '\0';
    return !strcmp(u, kw);
}
static int parse_int(const char *tok, long *out) {
    if (!tok) return 0;
    char *end = NULL;
    long v = strtol(tok, &end, 10);
    if (end == tok || *end != '\0') return 0;
    *out = v; return 1;
}

/* ---------------- Main ---------------- */
int main(int argc, char **argv) {
    if (argc < 2) {
        fprintf(stderr,
            "Usage: %s <netlist.txt> [--quiet]\n"
            "Builds fault universe and prints derived fanout (stem -> branches).\n",
            argv[0]);
        return EXIT_FAILURE;
    }
    const char *path = argv[1];
    int quiet = (argc >= 3 && strcmp(argv[2], "--quiet") == 0);

    FILE *fp = fopen(path, "r");
    if (!fp) die("cannot open netlist file");

    NodeSet nodes; ns_init(&nodes, 4096);

    char line[1024];
    size_t lineno = 0;
    while (fgets(line, sizeof(line), fp)) {
        ++lineno;
        char *p = line;
        while (*p && isspace((unsigned char)*p)) ++p;
        if (*p == '\0' || *p == '#') continue;
        char *nl = strchr(p, '\n'); if (nl) *nl = '\0';

        char *save = NULL;
        char *tok = strtok_r(p, " \t\r", &save);
        if (!tok) continue;

        if (is_gate_token(tok)) {
            /* GATE OUT IN1 IN2 */
            long out_id=0, in1=0, in2=0;
            char *t1 = strtok_r(NULL," \t\r",&save);
            char *t2 = strtok_r(NULL," \t\r",&save);
            char *t3 = strtok_r(NULL," \t\r",&save);
            if (!parse_int(t1,&out_id) || !parse_int(t2,&in1) || !parse_int(t3,&in2)) {
                fprintf(stderr,"Line %zu: malformed gate\n", lineno);
                continue;
            }
            ns_add(&nodes, out_id);
            ns_add(&nodes, in1);
            ns_add(&nodes, in2);

            /* DERIVED fanout: each gate input net feeds this gate's output net */
            fan_add_edge(in1, out_id);
            fan_add_edge(in2, out_id);
            continue;
        }

        if (is_kw(tok,"INPUT") || is_kw(tok,"OUTPUT")) {
            char *t=NULL; long id=0;
            while ((t=strtok_r(NULL," \t\r",&save))) {
                if (parse_int(t,&id)) ns_add(&nodes,id);
            }
            continue;
        }

        if (is_kw(tok,"FANOUT")) {
            /* If explicit FANOUT exists, merge it too: "FANOUT stem b1 b2 ..." */
            char *stem_tok = strtok_r(NULL," \t\r",&save);
            long stem=0;
            if (!parse_int(stem_tok,&stem)) continue;
            ns_add(&nodes, stem);
            char *t=NULL; long br=0;
            while ((t=strtok_r(NULL," \t\r",&save))) {
                if (parse_int(t,&br)) {
                    ns_add(&nodes, br);
                    fan_add_edge(stem, br);
                }
            }
            continue;
        }

        /* ignore trailing labels or unknown lines */
    }
    fclose(fp);

    /* Fault universe */
    long max_id = (long)nodes.cap - 1;
    long line_count = 0;
    for (long i=1;i<=max_id;++i) if (nodes.bits[i]) ++line_count;
    long total_faults = line_count * 2;

    if (!quiet) {
        for (long i=1;i<=max_id;++i) {
            if (!nodes.bits[i]) continue;
            printf("sa0_%ld\n", i);
            printf("sa1_%ld\n", i);
        }
        printf("----\n");
    }
    printf("Distinct lines (nets): %ld\n", line_count);
    printf("Total single stuck-at faults: %ld\n", total_faults);

    /* Fanout report (derived + explicit) */
    printf("----\nFanout (stem -> branches):\n");
    for (long stem=1; stem <= (long)fan_map_cap-1; ++stem) {
        FanList *fl = &fan_map[stem];
        if (!fl->v || fl->n == 0) continue;
        printf("%ld ->", stem);
        for (size_t j=0; j<fl->n; ++j) printf(" %ld", fl->v[j]);
        printf("\n");
    }

    /* cleanup */
    for (size_t i=0; i<fan_map_cap; ++i) free(fan_map[i].v);
    free(fan_map);
    free(nodes.bits);
    return 0;
}
