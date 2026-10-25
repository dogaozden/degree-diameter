/* hubx.c: single-source BFS on the 693,100 graph with in-memory edits (c5 scratch tool).
   Loads an edge list (first line n, then "u v" lines) once, applies edits from an ops file, then BFS from SRC to
   depth D and reports the number of vertices at distance > D (misses), optionally dumping them.
   ops file lines:  "- u v" delete edge u-v (must exist), "+ u v" add edge u-v.
   Usage: hubx EDGES SRC D OPS|- [MISSDUMP]
   Build: cc -O2 -o hubx hubx.c
   Also prints the per-level miss counts (level = v / 132860 for main vertices, "hub" otherwise). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
static int32_t n; static int64_t *st; static int32_t *adj;
static int32_t **ov; static int32_t *ovlen;     /* overrides: full adjacency list of a touched vertex */
static int32_t *deg;
static int32_t *dist;
static int32_t *queue;
static int load_graph(const char *fn, int32_t **U_out, int32_t **W_out, int64_t *m_out) {
    FILE *f = fopen(fn, "r"); if (!f) return 0;
    long nn; if (fscanf(f, "%ld", &nn) != 1) return 0; n = (int32_t)nn;
    int64_t cap = 1 << 22, m = 0; int32_t *U = malloc(cap * 4), *W = malloc(cap * 4); long a, b;
    while (fscanf(f, "%ld %ld", &a, &b) == 2) {
        if (m == cap) { cap *= 2; U = realloc(U, cap * 4); W = realloc(W, cap * 4); }
        U[m] = (int32_t)a; W[m] = (int32_t)b; m++;
    }
    fclose(f); *U_out = U; *W_out = W; *m_out = m; return 1;
}
static int32_t *cur_list(int32_t v, int32_t *len) {
    if (ov[v]) { *len = ovlen[v]; return ov[v]; }
    *len = (int32_t)(st[v + 1] - st[v]); return adj + st[v];
}
/* make an override list for v (copy of current list) */
static void ensure_ov(int32_t v) {
    if (ov[v]) return;
    int32_t len = (int32_t)(st[v + 1] - st[v]);
    ov[v] = malloc((len + 16) * sizeof(int32_t)); memcpy(ov[v], adj + st[v], len * sizeof(int32_t)); ovlen[v] = len;
}
static void add_nb(int32_t v, int32_t w) { ensure_ov(v); ov[v][ovlen[v]++] = w; }
static void del_nb(int32_t v, int32_t w) {
    ensure_ov(v); int32_t i; for (i = 0; i < ovlen[v]; i++) if (ov[v][i] == w) break;
    if (i == ovlen[v]) { fprintf(stderr, "edge %d-%d not present at %d\n", v, w, v); exit(1); }
    ov[v][i] = ov[v][--ovlen[v]];
}
int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage: hubx EDGES SRC D OPS|- [MISSDUMP]\n"); return 2; }
    int32_t *U, *W; int64_t m;
    if (!load_graph(argv[1], &U, &W, &m)) { fprintf(stderr, "cannot read %s\n", argv[1]); return 2; }
    int32_t src = atoi(argv[2]); int D = atoi(argv[3]);
    deg = calloc(n + 1, 4);
    for (int64_t i = 0; i < m; i++) { deg[U[i]]++; deg[W[i]]++; }
    st = malloc((n + 1) * sizeof(int64_t)); st[0] = 0; for (int32_t v = 0; v < n; v++) st[v + 1] = st[v] + deg[v];
    adj = malloc(2 * m * 4); int64_t *pos = calloc(n, 8);
    for (int64_t i = 0; i < m; i++) { adj[st[U[i]] + pos[U[i]]++] = W[i]; adj[st[W[i]] + pos[W[i]]++] = U[i]; }
    free(pos); free(U); free(W);
    ov = calloc(n, sizeof(int32_t *)); ovlen = calloc(n, 4);
    if (strcmp(argv[4], "-") != 0) {
        FILE *f = fopen(argv[4], "r"); if (!f) { fprintf(stderr, "no ops\n"); return 2; }
        char op; long u, v;
        while (fscanf(f, " %c %ld %ld", &op, &u, &v) == 3) {
            if (op == '-') { del_nb((int32_t)u, (int32_t)v); del_nb((int32_t)v, (int32_t)u); }
            else if (op == '+') { add_nb((int32_t)u, (int32_t)v); add_nb((int32_t)v, (int32_t)u); }
            else { fprintf(stderr, "bad op %c\n", op); return 2; }
        }
        fclose(f);
    }
    dist = malloc(n * 4); queue = malloc(n * 4);
    for (int32_t v = 0; v < n; v++) dist[v] = -1;
    int64_t h = 0, t = 0; dist[src] = 0; queue[t++] = src;
    while (h < t) {
        int32_t x = queue[h++]; if (dist[x] >= D) continue;
        int32_t len; int32_t *L = cur_list(x, &len);
        for (int32_t i = 0; i < len; i++) { int32_t y = L[i]; if (dist[y] < 0) { dist[y] = dist[x] + 1; queue[t++] = y; } }
    }
    int64_t miss = n - t; int64_t perlev[6] = {0,0,0,0,0,0}; int64_t hubmiss = 0;
    for (int32_t v = 0; v < n; v++) if (dist[v] < 0) { if (v < 664300) perlev[v / 132860]++; else hubmiss++; }
    printf("src %d D %d: misses %lld  (main per level %lld %lld %lld %lld %lld, hubs %lld)  reached %lld of %d\n",
           src, D, (long long)miss, (long long)perlev[0], (long long)perlev[1], (long long)perlev[2], (long long)perlev[3],
           (long long)perlev[4], (long long)hubmiss, (long long)t, n);
    if (argc >= 6) {
        FILE *g = fopen(argv[5], "w");
        for (int32_t v = 0; v < n; v++) if (dist[v] < 0) fprintf(g, "%d\n", v);
        fclose(g);
    }
    return 0;
}
