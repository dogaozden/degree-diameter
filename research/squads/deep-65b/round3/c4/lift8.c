/* lift8.c (deep-65b round 3, card c4): tabu over Z_N voltages of an 8-vertex split base
 * (4 A-vertices a = 0..3, 4 B-vertices b = 0..3 as base vertex 4+b; 24 darts = edges of the base multigraph).
 * usage: lift8 DARTS N SEED SECS [OUT.edges]
 *   DARTS: lines "a b w" (a, b as above; w = voltage A->B in Z_N; w < 0 = random start value).
 *   Lift: fibre (v,x), v in 0..7, x in Z_N; dart (a,b,w) gives edges (a,x)-(4+b,x+w).  Vertex id = v*N + x.
 *   Cost = #{(u, (v,x)): u in 0..7 a base source at fibre 0 and (v,x) at distance > 5 from (u,0)} (bit-parallel BFS over
 *   the 8N lift vertices, 8 sources at once). Cost 0 <=> diameter <= 5 (the lift is bipartite, 6-regular, and
 *   simple because darts in the same bundle keep distinct voltages).
 *   Gauge: a spanning tree of the base gets voltage 0 (the start is shifted to that gauge); tree darts never move.
 *   Moves: one free dart to any other value (no duplicate inside a bundle); tabu on (dart, old value), tenure 6..15,
 *   aspiration if the move beats the best; restart (3 random moves) after 400 steps without a new best.
 * prints: RES n=<8N> lift=N seed=S best=COST t_best=SEC steps=K sec=SEC_TOTAL
 * if best = 0 and OUT is given, writes the 8N-vertex edge list (first line 8N) of the best state. */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define NB 8
#define MAXD 64
#define MAXN 256
static int D, N, A[MAXD], B[MAXD], W[MAXD], tree[MAXD], deg[NB];
static int nbv[NB][8], dl[NB][8];
static uint8_t *vis, *fr, *nx;
static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndi(int k) { return (int)(rnd() % (uint64_t)k); }
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }

static void build_nb(void) {
    for (int v = 0; v < NB; v++) deg[v] = 0;
    for (int d = 0; d < D; d++) {
        int a = A[d], b = 4 + B[d], w = ((W[d] % N) + N) % N;
        int k = deg[a]++; nbv[a][k] = b; dl[a][k] = w;
        k = deg[b]++; nbv[b][k] = a; dl[b][k] = (N - w) % N;
    }
}
/* BFS on the lift with bitsets over the fibre: VIS[v][u] = set of x with (v,x) within the current distance of source (u,0).
   A neighbour step from (v,x) along dart shift dl gives x + dl, i.e. the set is rotated down by dl (mod N). */
typedef unsigned __int128 u128;
static u128 VIS[NB][NB], FRB[NB][NB], NXB[NB][NB];
static u128 MASKN;
static inline u128 rotdown(u128 S, int dl_) {
    if (dl_ == 0) return S;
    return ((S >> dl_) | (S << (N - dl_))) & MASKN;
}
static int cost(void) {
    build_nb();
    MASKN = (((u128)1) << N) - 1;
    for (int v = 0; v < NB; v++) for (int u = 0; u < NB; u++) VIS[v][u] = (v == u) ? (u128)1 : (u128)0;
    memcpy(FRB, VIS, sizeof VIS);
    for (int lev = 1; lev <= 5; lev++) {
        for (int v = 0; v < NB; v++)
            for (int u = 0; u < NB; u++) {
                u128 acc = 0;
                for (int k = 0; k < deg[v]; k++) acc |= rotdown(FRB[nbv[v][k]][u], dl[v][k]);
                NXB[v][u] = acc & ~VIS[v][u] & MASKN;
            }
        for (int v = 0; v < NB; v++) for (int u = 0; u < NB; u++) VIS[v][u] |= NXB[v][u];
        memcpy(FRB, NXB, sizeof NXB);
    }
    int c = 0;
    for (int v = 0; v < NB; v++) for (int u = 0; u < NB; u++) {
        u128 miss = ~VIS[v][u] & MASKN;
        c += __builtin_popcountll((uint64_t)miss) + __builtin_popcountll((uint64_t)(miss >> 64));
    }
    return c;
}
static int dup_ok(int d, int val) {
    for (int e = 0; e < D; e++) if (e != d && A[e] == A[d] && B[e] == B[d] && W[e] == val) return 0;
    return 1;
}
static int tabu[MAXD][MAXN];
static int freed[MAXD], F;

int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage: lift8 DARTS N SEED SECS [OUT]\n"); return 2; }
    FILE *f = fopen(argv[1], "r"); if (!f) return 2;
    N = atoi(argv[2]); uint64_t seed = strtoull(argv[3], 0, 10); double secs = atof(argv[4]);
    const char *out = argc > 5 ? argv[5] : NULL;
    if (N > MAXN) return 2;
    D = 0; int a, b, w;
    while (fscanf(f, "%d %d %d", &a, &b, &w) == 3) { A[D] = a; B[D] = b; W[D] = w; D++; }
    fclose(f);
    rs ^= (seed + 1) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 20; i++) rnd();
    for (int d = 0; d < D; d++) if (W[d] >= 0) W[d] %= N;
    /* random values for darts given as -1 (no duplicate inside a bundle) */
    for (int d = 0; d < D; d++) if (W[d] < 0) { int val; do val = rndi(N); while (!dup_ok(d, val)); W[d] = val; }
    /* spanning forest of the base; gauge shift c[v] makes tree darts 0 */
    int c[NB], seen[NB] = {0}, q[NB], qh = 0, qt = 0; memset(tree, 0, sizeof tree);
    for (int r = 0; r < NB; r++) if (!seen[r]) {
        seen[r] = 1; c[r] = 0; q[qt++] = r;
        while (qh < qt) {
            int v = q[qh++];
            for (int d = 0; d < D; d++) {
                int o = -1, sg = 0;
                if (v == A[d]) { o = 4 + B[d]; sg = -1; } else if (v == 4 + B[d]) { o = A[d]; sg = 1; } else continue;
                if (seen[o]) continue;
                seen[o] = 1; tree[d] = 1; c[o] = ((c[v] + sg * W[d]) % N + N) % N; q[qt++] = o;
            }
        }
    }
    for (int d = 0; d < D; d++) W[d] = ((W[d] + c[4 + B[d]] - c[A[d]]) % N + 2 * N) % N;
    for (int d = 0; d < D; d++) if (tree[d] && W[d] != 0) { fprintf(stderr, "gauge error\n"); return 3; }
    F = 0; for (int d = 0; d < D; d++) if (!tree[d]) freed[F++] = d;
    for (int v = 0; v < NB; v++) { int k = 0; for (int d = 0; d < D; d++) if (A[d] == v || 4 + B[d] == v) k++; deg[v] = k; }
    for (int v = 0; v < NB; v++) if (deg[v] != 6) { fprintf(stderr, "base not 6-regular\n"); return 3; }
    vis = malloc(NB * N); fr = malloc(NB * N); nx = malloc(NB * N);
    int cur = cost(), best = cur; int bestW[MAXD]; memcpy(bestW, W, sizeof W);
    double t0 = now(), tbest = 0; long steps = 0; int stall = 0;
    while (best > 0 && now() - t0 < secs) {
        steps++;
        int bc = 1 << 30, bd = -1, bv = -1, nt = 0;
        for (int i = 0; i < F; i++) {
            int d = freed[i], old = W[d];
            for (int val = 0; val < N; val++) {
                if (val == old || !dup_ok(d, val)) continue;
                W[d] = val; int cc = cost(); W[d] = old;
                if (tabu[d][val] >= steps && cc >= best) continue;
                if (cc < bc) { bc = cc; bd = d; bv = val; nt = 1; }
                else if (cc == bc) { nt++; if (rndi(nt) == 0) { bd = d; bv = val; } }
            }
        }
        if (bd < 0) continue;
        tabu[bd][W[bd]] = (int)steps + 6 + rndi(10);
        W[bd] = bv; cur = bc;
        if (cur < best) { best = cur; memcpy(bestW, W, sizeof W); tbest = now() - t0; stall = 0; }
        else stall++;
        if (stall > 400) {
            for (int k = 0; k < 3; k++) {
                int d = freed[rndi(F)], val;
                do val = rndi(N); while (!dup_ok(d, val));
                W[d] = val;
            }
            stall = 0; cur = cost();
        }
    }
    printf("RES n=%d lift=%d seed=%llu best=%d t_best=%.2f steps=%ld sec=%.1f\n", NB * N, N, (unsigned long long)seed,
           best, tbest, steps, now() - t0);
    if (out && (best == 0 || secs <= 0)) {
        memcpy(W, bestW, sizeof W);
        FILE *g = fopen(out, "w"); fprintf(g, "%d\n", NB * N);
        for (int d = 0; d < D; d++) for (int x = 0; x < N; x++)
            fprintf(g, "%d %d\n", A[d] * N + x, (4 + B[d]) * N + (x + W[d]) % N);
        fclose(g);
        printf("WROTE %s\n", out);
    }
    return 0;
}
