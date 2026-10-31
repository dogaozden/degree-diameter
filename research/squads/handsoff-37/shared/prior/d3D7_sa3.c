/* sa3: simulated annealing over cubic bipartite graphs on n vertices (no symmetry imposed), D = 7 by default.
   Usage: sa3 n seed seconds [T0] [T1] [init.edges] [out.edges]
   Cost = number of ordered vertex pairs at distance > D (bit-parallel all-pairs BFS, ~5 us at n = 170).
   Move = edge switch (a1 b1, a2 b2) -> (a1 b2, a2 b1), keeps the graph cubic, bipartite and simple.
   Temperature falls geometrically from T0 to T1 over each restart cycle (default 2 -> 0.05, cycle 20 s).
   Writes out.edges (default best.edges) whenever a new best is found; prints FOUND on cost 0. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>

#define MAXN 512
#define W ((MAXN + 63) / 64)
static int n, m, D = 7, nb[MAXN][3], ea[MAXN * 3 / 2], eb[MAXN * 3 / 2], ne;
static uint64_t ra[MAXN][W], rb[MAXN][W];
static int nw;

static uint64_t rng = 88172645463325252ULL;
static inline uint64_t xr(void) { rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; return rng; }
static inline double ur(void) { return (xr() >> 11) * (1.0 / 9007199254740992.0); }

long cost(void) {
    uint64_t (*cur)[W] = ra, (*nx)[W] = rb;
    for (int x = 0; x < n; x++) { memset(cur[x], 0, nw * 8); cur[x][x >> 6] |= 1ULL << (x & 63); }
    for (int t = 0; t < D; t++) {
        for (int x = 0; x < n; x++) {
            const uint64_t *a = cur[nb[x][0]], *b = cur[nb[x][1]], *c = cur[nb[x][2]], *s = cur[x];
            for (int w = 0; w < nw; w++) nx[x][w] = s[w] | a[w] | b[w] | c[w];
        }
        uint64_t (*tmp)[W] = cur; cur = nx; nx = tmp;
    }
    long reached = 0;
    for (int x = 0; x < n; x++) for (int w = 0; w < nw; w++) reached += __builtin_popcountll(cur[x][w]);
    return (long)n * n - reached;
}

static void rebuild(void) {
    int dg[MAXN] = {0};
    for (int i = 0; i < ne; i++) { nb[ea[i]][dg[ea[i]]++] = eb[i]; nb[eb[i]][dg[eb[i]]++] = ea[i]; }
}
static int adj(int a, int b) { return nb[a][0] == b || nb[a][1] == b || nb[a][2] == b; }

static void random_graph(void) {
    /* random cubic bipartite simple graph: three random perfect matchings, retried until simple */
    for (;;) {
        int p[MAXN]; ne = 0;
        for (int k = 0; k < 3; k++) {
            for (int i = 0; i < m; i++) p[i] = i;
            for (int i = m - 1; i > 0; i--) { int j = xr() % (i + 1); int t = p[i]; p[i] = p[j]; p[j] = t; }
            for (int i = 0; i < m; i++) { ea[ne] = i; eb[ne] = m + p[i]; ne++; }
        }
        int ok = 1;
        for (int i = 0; i < ne && ok; i++) for (int j = i + 1; j < ne; j++) if (ea[i] == ea[j] && eb[i] == eb[j]) { ok = 0; break; }
        if (ok) break;
    }
    rebuild();
}

static void save(const char *path) {
    FILE *f = fopen(path, "w"); fprintf(f, "%d\n", n);
    for (int i = 0; i < ne; i++) fprintf(f, "%d %d\n", ea[i], eb[i]);
    fclose(f);
}

int main(int argc, char **argv) {
    if (argc < 4) { fprintf(stderr, "usage: sa3 n seed seconds [T0] [T1] [init.edges] [out.edges]\n"); return 2; }
    n = atoi(argv[1]); m = n / 2; rng ^= (uint64_t)atoll(argv[2]) * 0x9E3779B97F4A7C15ULL; xr(); xr();
    double secs = atof(argv[3]), T0 = argc > 4 ? atof(argv[4]) : 2.0, T1 = argc > 5 ? atof(argv[5]) : 0.05;
    const char *out = argc > 7 ? argv[7] : "best.edges";
    if (getenv("D")) D = atoi(getenv("D"));
    nw = (n + 63) / 64;
    if (argc > 6 && strcmp(argv[6], "-") != 0) {
        FILE *f = fopen(argv[6], "r"); int nn; if (fscanf(f, "%d", &nn) != 1 || nn != n) { fprintf(stderr, "bad init\n"); return 2; }
        ne = 0; int a, b; while (fscanf(f, "%d %d", &a, &b) == 2) { if (a > b) { int t = a; a = b; b = t; } ea[ne] = a; eb[ne] = b; ne++; }
        fclose(f); rebuild();
    } else random_graph();
    long c = cost(), best = c; save(out);
    clock_t st = clock(); double cyc = 20.0; long it = 0;
    printf("start cost %ld\n", c); fflush(stdout);
    for (;;) {
        double el = (double)(clock() - st) / CLOCKS_PER_SEC;
        if (el > secs) break;
        double fr = fmod(el, cyc) / cyc, T = T0 * pow(T1 / T0, fr);
        int i = xr() % ne, j = xr() % ne;
        int a1 = ea[i], b1 = eb[i], a2 = ea[j], b2 = eb[j];
        if (a1 == a2 || b1 == b2 || adj(a1, b2) || adj(a2, b1)) continue;
        eb[i] = b2; eb[j] = b1;
        for (int k = 0; k < 3; k++) { if (nb[a1][k] == b1) nb[a1][k] = b2; if (nb[a2][k] == b2) nb[a2][k] = b1;
                                      if (nb[b1][k] == a1) nb[b1][k] = a2; if (nb[b2][k] == a2) nb[b2][k] = a1; }
        long c2 = cost(); it++;
        if (c2 <= c || ur() < exp((c - c2) / T)) {
            c = c2;
            if (c < best) { best = c; save(out); printf("t=%.1f it=%ld best %ld\n", el, it, best); fflush(stdout); if (best == 0) { printf("FOUND\n"); break; } }
        } else {
            eb[i] = b1; eb[j] = b2;
            for (int k = 0; k < 3; k++) { if (nb[a1][k] == b2) nb[a1][k] = b1; if (nb[a2][k] == b1) nb[a2][k] = b2;
                                          if (nb[b1][k] == a2) nb[b1][k] = a1; if (nb[b2][k] == a1) nb[b2][k] = a2; }
        }
    }
    printf("end best %ld its %ld\n", best, it);
    return 0;
}
