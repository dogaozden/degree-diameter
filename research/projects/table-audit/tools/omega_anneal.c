/* omega_anneal.c (table-audit): does some labelling make Gomez's Omega H(q) (tools/omega_build.py) diameter 8?
   Same wiring as omega_build.py (alpha groups of 5 copies, types a/b, sigma = identity pairing p_x ~ l_x by index),
   plus a free relabelling of the points and of the lines of every copy (not in the thesis; this tests whether any
   labelling at all reaches D_1 + 2).  Moves: swap two points or two lines of one copy.  Cost: number of ordered
   vertex pairs at distance > D (bit-parallel BFS from every vertex).  Writes the edge list on cost 0.
   Env HUBONLY=1: score from the hub vertices only (the pairs that fail first); a cost-0 graph must still pass apsp.c.
   Usage: omega_anneal BASE_EDGES TYPES D seconds seed OUT */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>

static int N, B, A, NC, NT, D, n0, m0, *bu, *bv, *perm, *deg, *adj, maxdeg;
static char types[32];
static uint64_t rs = 0x9E3779B97F4A7C15ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline int cpv(int g, int c, int v) { int i = 5 * g + ((c % 5) + 5) % 5; return i * B + perm[i * B + v]; }
static void addE(int u, int v) { adj[u * maxdeg + deg[u]++] = v; adj[v * maxdeg + deg[v]++] = u; }
static void build(void) {
    memset(deg, 0, sizeof(int) * NT);
    for (int i = 0; i < NC; i++) for (int e = 0; e < m0; e++) addE(i * B + bu[e], i * B + bv[e]);
    int H0 = NC * B;
    for (int g = 0; g < A; g++) for (int k = 0; k < 5; k++) for (int x = 0; x < N; x++) {
        int p = x, l = N + x, nk = H0 + k * N + x, nb = H0 + 5 * N + k * N + x;
        if (types[g] == 'a') { addE(nb, cpv(g, k + 2, p)); addE(nb, cpv(g, k + 3, p)); addE(nk, cpv(g, k - 1, l)); addE(nk, cpv(g, k + 1, l)); }
        else { addE(nk, cpv(g, k + 3, p)); addE(nk, cpv(g, k + 4, p)); addE(nb, cpv(g, k - 1, l)); addE(nb, cpv(g, k + 1, l)); }
    }
}
static uint64_t *vis, *fr, *nx;
static int S0 = 0;
static long cost(void) {
    long bad = 0;
    for (int s0 = S0; s0 < NT; s0 += 64) {
        int ns = NT - s0 < 64 ? NT - s0 : 64; uint64_t full = ns == 64 ? ~0ULL : ((1ULL << ns) - 1);
        memset(vis, 0, 8L * NT); memset(fr, 0, 8L * NT);
        for (int k = 0; k < ns; k++) { vis[s0 + k] |= 1ULL << k; fr[s0 + k] |= 1ULL << k; }
        for (int lev = 0; lev < D; lev++) {
            for (int x = 0; x < NT; x++) { uint64_t acc = 0; for (int i = 0; i < deg[x]; i++) acc |= fr[adj[x * maxdeg + i]]; nx[x] = acc & ~vis[x]; }
            for (int x = 0; x < NT; x++) vis[x] |= nx[x];
            uint64_t *t = fr; fr = nx; nx = t;
        }
        for (int x = 0; x < NT; x++) bad += ns - __builtin_popcountll(vis[x] & full);
    }
    return bad;
}
int main(int argc, char **argv) {
    FILE *f = fopen(argv[1], "r"); strcpy(types, argv[2]); D = atoi(argv[3]); double secs = atof(argv[4]);
    rs ^= (uint64_t)atoi(argv[5]) * 0x2545F4914F6CDD1DULL;
    if (fscanf(f, "%d", &n0) != 1) return 2;
    bu = malloc(sizeof(int) * 8 * n0); bv = malloc(sizeof(int) * 8 * n0); m0 = 0;
    while (fscanf(f, "%d %d", &bu[m0], &bv[m0]) == 2) m0++;
    N = n0 / 2; B = n0; A = strlen(types); NC = 5 * A; NT = NC * B + 10 * N;
    maxdeg = 64; perm = malloc(sizeof(int) * NC * B);
    for (int i = 0; i < NC * B; i++) perm[i] = i % B;
    deg = malloc(sizeof(int) * NT); adj = malloc(sizeof(int) * NT * maxdeg);
    vis = malloc(8L * NT); fr = malloc(8L * NT); nx = malloc(8L * NT);
    if (getenv("HUBONLY")) S0 = NC * B;
    build(); long c = cost(), best = c; double T = 0.5 * c / NT + 1; clock_t t0 = clock(); long it = 0;
    fprintf(stderr, "start cost %ld (n = %d)\n", c, NT);
    while (c > 0 && (double)(clock() - t0) / CLOCKS_PER_SEC < secs) {
        it++;
        int i = rnd() % NC, side = rnd() % 2, a = side * N + rnd() % N, b = side * N + rnd() % N;
        if (a == b) continue;
        int t = perm[i * B + a]; perm[i * B + a] = perm[i * B + b]; perm[i * B + b] = t;
        build(); long c2 = cost();
        if (c2 <= c || exp((c - c2) / T) > (rnd() >> 11) * (1.0 / 9007199254740992.0)) { c = c2; if (c < best) { best = c; fprintf(stderr, "it %ld cost %ld T %.2f\n", it, c, T); } }
        else { t = perm[i * B + a]; perm[i * B + a] = perm[i * B + b]; perm[i * B + b] = t; }
        T *= 0.995; if (T < 0.2) T = 0.5 * c / NT + 1;
    }
    printf("RESULT types=%s D=%d n=%d cost=%ld best=%ld iters=%ld\n", types, D, NT, c, best, it);
    if (c == 0) {
        build(); FILE *o = fopen(argv[6], "w"); fprintf(o, "%d\n", NT);
        for (int x = 0; x < NT; x++) for (int k = 0; k < deg[x]; k++) if (adj[x * maxdeg + k] > x) fprintf(o, "%d %d\n", x, adj[x * maxdeg + k]);
        fclose(o); printf("wrote %s\n", argv[6]);
    }
    return 0;
}
