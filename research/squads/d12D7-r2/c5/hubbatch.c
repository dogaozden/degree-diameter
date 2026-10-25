/* hubbatch.c (c5 scratch): like hubx, but loads the graph once and evaluates many edit scenarios from stdin.
   stdin: scenarios; each is a list of lines "- u v" / "+ u v", terminated by a line "=".
   stdout: one line per scenario: misses (pairs at distance > D from SRC).  Usage: hubbatch EDGES SRC D */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
static int32_t n; static int64_t *st; static int32_t *adj; static int32_t **ov; static int32_t *ovlen;
static int32_t *touched; static int ntouched = 0; static int32_t *tmark;
static int32_t *dist, *queue;
static void ensure_ov(int32_t v) {
    if (ov[v]) return;
    int32_t len = (int32_t)(st[v + 1] - st[v]);
    ov[v] = malloc((len + 32) * sizeof(int32_t)); memcpy(ov[v], adj + st[v], len * sizeof(int32_t)); ovlen[v] = len;
    touched[ntouched++] = v;
}
static void add_nb(int32_t v, int32_t w) { ensure_ov(v); ov[v][ovlen[v]++] = w; }
static int del_nb(int32_t v, int32_t w) {
    ensure_ov(v); int32_t i; for (i = 0; i < ovlen[v]; i++) if (ov[v][i] == w) break;
    if (i == ovlen[v]) return 0;
    ov[v][i] = ov[v][--ovlen[v]]; return 1;
}
int main(int argc, char **argv) {
    if (argc < 4) return 2;
    FILE *f = fopen(argv[1], "r"); long nn; if (!f || fscanf(f, "%ld", &nn) != 1) return 2; n = (int32_t)nn;
    int64_t cap = 1 << 23, m = 0; int32_t *U = malloc(cap * 4), *W = malloc(cap * 4); long a, b;
    while (fscanf(f, "%ld %ld", &a, &b) == 2) { if (m == cap) { cap *= 2; U = realloc(U, cap * 4); W = realloc(W, cap * 4); } U[m] = (int32_t)a; W[m] = (int32_t)b; m++; }
    fclose(f);
    int32_t src = atoi(argv[2]); int D = atoi(argv[3]);
    int32_t *deg = calloc(n + 1, 4);
    for (int64_t i = 0; i < m; i++) { deg[U[i]]++; deg[W[i]]++; }
    st = malloc((n + 1) * sizeof(int64_t)); st[0] = 0; for (int32_t v = 0; v < n; v++) st[v + 1] = st[v] + deg[v];
    adj = malloc(2 * m * 4); int64_t *pos = calloc(n, 8);
    for (int64_t i = 0; i < m; i++) { adj[st[U[i]] + pos[U[i]]++] = W[i]; adj[st[W[i]] + pos[W[i]]++] = U[i]; }
    free(pos); free(U); free(W);
    ov = calloc(n, sizeof(int32_t *)); ovlen = calloc(n, 4); touched = malloc(sizeof(int32_t) * (size_t)n * 0 + 4 * 1000000); 
    dist = malloc(n * 4); queue = malloc(n * 4);
    char line[256]; int nlines = 0; int errs = 0;
    while (fgets(line, sizeof line, stdin)) {
        if (line[0] == '=') {
            for (int32_t v = 0; v < n; v++) dist[v] = -1;
            int64_t h = 0, t = 0; dist[src] = 0; queue[t++] = src;
            while (h < t) {
                int32_t x = queue[h++]; if (dist[x] >= D) continue;
                int32_t len = ov[x] ? ovlen[x] : (int32_t)(st[x + 1] - st[x]); int32_t *L = ov[x] ? ov[x] : adj + st[x];
                for (int32_t i = 0; i < len; i++) { int32_t y = L[i]; if (dist[y] < 0) { dist[y] = dist[x] + 1; queue[t++] = y; } }
            }
            printf("%lld %d\n", (long long)(n - t), errs); fflush(stdout);
            for (int i = 0; i < ntouched; i++) { int32_t v = touched[i]; free(ov[v]); ov[v] = NULL; ovlen[v] = 0; }
            ntouched = 0; errs = 0; nlines = 0;
            continue;
        }
        char op; long u, v;
        if (sscanf(line, " %c %ld %ld", &op, &u, &v) != 3) continue;
        if (op == '-') { if (!del_nb((int32_t)u, (int32_t)v)) errs++; if (!del_nb((int32_t)v, (int32_t)u)) errs++; }
        else if (op == '+') { add_nb((int32_t)u, (int32_t)v); add_nb((int32_t)v, (int32_t)u); }
        nlines++;
    }
    return 0;
}
