/* Wildcard worker 8: simulated annealing over Z_M voltage lifts of a bipartite multigraph.
   Base: K X-vertices, K Y-vertices, D-regular (multi)graph, edges (i,j,a): lift (X,i,g) ~ (Y,j,g+a).
   Lift has 2*K*M vertices, degree D. Cost = number of (base source s, lift target (y,g)) pairs with no walk of
   length <= 5 from s to y with voltage g (sum over all base sources; lift is Z_M-invariant so this is exact).
   Usage: lift_sa K M D iters seed T0 T1 [init_file] > best_file   (best base written to stdout as "K M D" + edges)
   Compile: gcc -O2 -o lift_sa lift_sa.c */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdint.h>
typedef unsigned __int128 u128;
static int K, M, D, NE;
static int *ei, *ej, *ea;          /* edges */
static uint64_t rs;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline int rndint(int n) { return (int)(rnd() % (uint64_t)n); }
static u128 MASK;
static inline u128 rot(u128 S, int a) {
    if (a == 0) return S;
    return ((S << a) & MASK) | (S >> (M - a));
}
static inline int pc(u128 S) { return __builtin_popcountll((uint64_t)S) + __builtin_popcountll((uint64_t)(S >> 64)); }
/* directed edge arrays for DP */
static int *dfrom, *dto, *dsh;
static void build_directed(void) {
    int n = 0;
    for (int e = 0; e < NE; e++) {
        dfrom[n] = ei[e]; dto[n] = K + ej[e]; dsh[n] = ea[e]; n++;          /* X -> Y : +a */
        dfrom[n] = K + ej[e]; dto[n] = ei[e]; dsh[n] = (M - ea[e]) % M; n++; /* Y -> X : -a */
    }
}
static long cost_eval(void) {
    static u128 cur[1024 * 2], nxt[1024 * 2], tot[1024 * 2];
    int V = 2 * K, ND = 2 * NE;
    build_directed();
    long cost = 0;
    for (int s = 0; s < V; s++) {
        memset(cur, 0, sizeof(u128) * V);
        cur[s] = 1; tot[s] = 1;
        for (int v = 0; v < V; v++) if (v != s) tot[v] = 0;
        for (int step = 0; step < 5; step++) {
            memset(nxt, 0, sizeof(u128) * V);
            for (int d = 0; d < ND; d++) if (cur[dfrom[d]]) nxt[dto[d]] |= rot(cur[dfrom[d]], dsh[d]);
            for (int v = 0; v < V; v++) tot[v] |= nxt[v];
            memcpy(cur, nxt, sizeof(u128) * V);
        }
        for (int v = 0; v < V; v++) cost += M - pc(tot[v]);
    }
    return cost;
}
static int dup_check(int i, int j, int a, int skip1, int skip2) {
    for (int e = 0; e < NE; e++) if (e != skip1 && e != skip2 && ei[e] == i && ej[e] == j && ea[e] == a) return 1;
    return 0;
}
static void write_base(FILE *f) {
    fprintf(f, "%d %d %d\n", K, M, D);
    for (int e = 0; e < NE; e++) fprintf(f, "%d %d %d\n", ei[e], ej[e], ea[e]);
}
int main(int argc, char **argv) {
    if (argc < 8) { fprintf(stderr, "usage: lift_sa K M D iters seed T0 T1 [init]\n"); return 1; }
    K = atoi(argv[1]); M = atoi(argv[2]); D = atoi(argv[3]);
    long iters = atol(argv[4]); rs = strtoull(argv[5], 0, 10) * 2654435761ULL + 88172645463325252ULL;
    double T0 = atof(argv[6]), T1 = atof(argv[7]);
    MASK = (((u128)1) << M) - 1;
    NE = K * D;
    ei = malloc(NE * sizeof(int)); ej = malloc(NE * sizeof(int)); ea = malloc(NE * sizeof(int));
    dfrom = malloc(2 * NE * sizeof(int)); dto = malloc(2 * NE * sizeof(int)); dsh = malloc(2 * NE * sizeof(int));
    if (argc > 8) {
        FILE *f = fopen(argv[8], "r"); int k2, m2, d2;
        if (fscanf(f, "%d %d %d", &k2, &m2, &d2) != 3 || k2 != K || m2 != M || d2 != D) { fprintf(stderr, "init mismatch\n"); return 1; }
        for (int e = 0; e < NE; e++) if (fscanf(f, "%d %d %d", &ei[e], &ej[e], &ea[e]) != 3) return 1;
        fclose(f);
    } else {
        int *perm = malloc(K * sizeof(int));
        for (int t = 0; t < D; t++) {
            for (int i = 0; i < K; i++) perm[i] = i;
            for (int i = K - 1; i > 0; i--) { int r = rndint(i + 1), x = perm[i]; perm[i] = perm[r]; perm[r] = x; }
            for (int i = 0; i < K; i++) {
                int e = t * K + i; ei[e] = i; ej[e] = perm[i]; ea[e] = rndint(M);
                while (dup_check(ei[e], ej[e], ea[e], e, -1)) ea[e] = rndint(M);
            }
        }
    }
    long cur = cost_eval(), best = cur;
    fprintf(stderr, "initial cost %ld\n", cur);
    for (long it = 0; it < iters && cur > 0; it++) {
        double T = T0 * pow(T1 / T0, (double)it / iters);
        int e1 = rndint(NE), e2 = -1, mv = rndint(2);
        int oi1 = ei[e1], oj1 = ej[e1], oa1 = ea[e1], oi2 = 0, oj2 = 0, oa2 = 0;
        if (mv == 0) {                       /* voltage change */
            int na = rndint(M);
            if (na == oa1) continue;
            if (dup_check(oi1, oj1, na, e1, -1)) continue;
            ea[e1] = na;
        } else {                             /* double edge switch: (i1,j2),(i2,j1) with fresh voltages */
            e2 = rndint(NE);
            oi2 = ei[e2]; oj2 = ej[e2]; oa2 = ea[e2];
            if (oi1 == oi2 || oj1 == oj2) continue;
            int b1 = rndint(M), b2 = rndint(M);
            if (dup_check(oi1, oj2, b1, e1, e2) || dup_check(oi2, oj1, b2, e1, e2)) continue;
            if (oi1 == oi2 || oj1 == oj2) continue;
            ej[e1] = oj2; ea[e1] = b1; ei[e2] = oi2; ej[e2] = oj1; ea[e2] = b2;
        }
        long nc = cost_eval();
        if (nc <= cur || exp(-(double)(nc - cur) / T) > (rnd() >> 11) * (1.0 / 9007199254740992.0)) {
            cur = nc;
            if (cur < best) { best = cur; fprintf(stderr, "it %ld T %.3f best %ld\n", it, T, best); }
        } else {
            if (mv == 0) ea[e1] = oa1;
            else { ei[e1] = oi1; ej[e1] = oj1; ea[e1] = oa1; ei[e2] = oi2; ej[e2] = oj2; ea[e2] = oa2; }
        }
        if (it % 2000 == 0) fprintf(stderr, "it %ld T %.3f cur %ld best %ld\n", it, T, cur, best);
    }
    fprintf(stderr, "final best %ld cur %ld\n", best, cur);
    if (cur == 0) { fprintf(stderr, "ZERO COST: diameter-5 lift found\n"); }
    write_base(stdout);
    return cur == 0 ? 0 : 2;
}
