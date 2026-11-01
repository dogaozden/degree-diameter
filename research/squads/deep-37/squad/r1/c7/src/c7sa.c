/* c7sa: simulated annealing at n = 169 (or any n) over bipartite graphs with max degree 3, started from a given edge list.
   Moves: (M1) 2-switch on two edges a1b1, a2b2 -> a1b2, a2b1 (degrees kept); (M2) deficiency move: a vertex a' of degree
   < 3 on side A takes an extra neighbour b (of side B) from a neighbour a'' of degree 3 (which drops to 2), keeping b's degree.
   Objective: far = #unordered pairs at distance > 7 (bit-parallel BFS). Side of each vertex from the start graph's bipartition.
   usage: c7sa START ITERS SEED T0 T1 OUT   (writes best graph to OUT, prints best far and final far) */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#define MAXN 200
#define NW 4
typedef uint64_t u64;
static int N, nb[MAXN][3], dg[MAXN], col[MAXN];
static u64 rng_s[2];
static inline u64 rnd(void) { u64 s1 = rng_s[0]; const u64 s0 = rng_s[1]; rng_s[0] = s0; s1 ^= s1 << 23; rng_s[1] = s1 ^ s0 ^ (s1 >> 17) ^ (s0 >> 26); return rng_s[1] + s0; }
static inline int rndn(int k) { return (int)(rnd() % (u64)k); }

static long far_count(void) {
    static u64 R[MAXN][NW], F[MAXN][NW], G[MAXN][NW];
    int nw = (N + 63) / 64;
    for (int v = 0; v < N; v++) for (int w = 0; w < nw; w++) { R[v][w] = 0; F[v][w] = 0; }
    for (int v = 0; v < N; v++) { R[v][v >> 6] |= 1ULL << (v & 63); F[v][v >> 6] |= 1ULL << (v & 63); }
    for (int step = 0; step < 7; step++) {
        for (int v = 0; v < N; v++) {
            for (int w = 0; w < nw; w++) G[v][w] = 0;
            for (int j = 0; j < dg[v]; j++) { int u = nb[v][j]; for (int w = 0; w < nw; w++) G[v][w] |= F[u][w]; }
            for (int w = 0; w < nw; w++) G[v][w] &= ~R[v][w];
        }
        for (int v = 0; v < N; v++) for (int w = 0; w < nw; w++) { F[v][w] = G[v][w]; R[v][w] |= G[v][w]; }
    }
    long reached = 0;
    for (int v = 0; v < N; v++) for (int w = 0; w < nw; w++) reached += __builtin_popcountll(R[v][w]);
    return ((long)N * (N - 1) - (reached - N)) / 2;
}
static int has_edge(int a, int b) { for (int j = 0; j < dg[a]; j++) if (nb[a][j] == b) return 1; return 0; }
static void del_edge(int a, int b) {
    for (int j = 0; j < dg[a]; j++) if (nb[a][j] == b) { nb[a][j] = nb[a][--dg[a]]; break; }
    for (int j = 0; j < dg[b]; j++) if (nb[b][j] == a) { nb[b][j] = nb[b][--dg[b]]; break; }
}
static void add_edge(int a, int b) { nb[a][dg[a]++] = b; nb[b][dg[b]++] = a; }

int main(int argc, char **argv) {
    if (argc < 7) { fprintf(stderr, "usage: c7sa START ITERS SEED T0 T1 OUT\n"); return 2; }
    FILE *f = fopen(argv[1], "r"); int m = 0, a, b; static int ea[1000], eb[1000];
    if (fscanf(f, "%d", &N) != 1) return 2;
    while (fscanf(f, "%d %d", &a, &b) == 2) { ea[m] = a; eb[m] = b; m++; }
    fclose(f);
    long iters = atol(argv[2]); u64 seed = strtoull(argv[3], 0, 10);
    double T0 = atof(argv[4]), T1 = atof(argv[5]);
    rng_s[0] = seed * 0x9E3779B97F4A7C15ULL + 1; rng_s[1] = seed ^ 0xD1B54A32D192ED03ULL; for (int i = 0; i < 20; i++) rnd();
    memset(dg, 0, sizeof dg);
    for (int i = 0; i < m; i++) add_edge(ea[i], eb[i]);
    for (int v = 0; v < N; v++) col[v] = -1;
    static int q[MAXN]; int h = 0, t = 0; col[0] = 0; q[t++] = 0;
    while (h < t) { int v = q[h++]; for (int j = 0; j < dg[v]; j++) { int u = nb[v][j]; if (col[u] < 0) { col[u] = 1 - col[v]; q[t++] = u; } } }
    long cur = far_count(), best = cur;
    static int bnb[MAXN][3], bdg[MAXN]; memcpy(bnb, nb, sizeof nb); memcpy(bdg, dg, sizeof dg);
    fprintf(stderr, "start far %ld\n", cur);
    for (long it = 0; it < iters; it++) {
        double T = T0 * pow(T1 / T0, (double)it / (double)iters);
        int mv = rndn(10) < 7 ? 1 : 2;
        if (mv == 1) {
            /* pick a1 b1 edge and a2 b2 edge (a in side 0 and b side 1 or reversed) */
            int a1 = rndn(N); if (dg[a1] == 0) continue; int b1 = nb[a1][rndn(dg[a1])];
            int a2 = rndn(N); if (dg[a2] == 0) continue; int b2 = nb[a2][rndn(dg[a2])];
            if (col[a1] == col[a2] || a1 == a2 || b1 == b2) continue;
            if (col[a1] == 1) { int tmp = a1; a1 = b1; b1 = tmp; }   /* ensure a1 in side 0 */
            if (col[a2] == 1) { int tmp = a2; a2 = b2; b2 = tmp; }
            if (has_edge(a1, b2) || has_edge(a2, b1)) continue;
            del_edge(a1, b1); del_edge(a2, b2); add_edge(a1, b2); add_edge(a2, b1);
            long nw_ = far_count();
            double u = (double)(rnd() >> 11) / 9007199254740992.0;
            if (nw_ <= cur || u < exp(-(double)(nw_ - cur) / T)) { cur = nw_; }
            else { del_edge(a1, b2); del_edge(a2, b1); add_edge(a1, b1); add_edge(a2, b2); }
        } else {
            /* deficiency move: a' with dg<3 (side 0 preferred), take neighbour b of a'' (dg 3) where a'' side 0 and a' not adj b */
            int defl[MAXN], nd = 0; for (int v = 0; v < N; v++) if (dg[v] < 3 && col[v] == 0) defl[nd++] = v;
            if (nd == 0) continue; int ap = defl[rndn(nd)];
            int bb = rndn(N); if (col[bb] != 1 || dg[bb] == 0) continue;
            int app = -1; for (int j = 0; j < dg[bb]; j++) if (dg[nb[bb][j]] == 3 && nb[bb][j] != ap) { app = nb[bb][j]; break; }
            if (app < 0 || has_edge(ap, bb)) continue;
            del_edge(app, bb); add_edge(ap, bb);
            long nw_ = far_count();
            double u = (double)(rnd() >> 11) / 9007199254740992.0;
            if (nw_ <= cur || u < exp(-(double)(nw_ - cur) / T)) { cur = nw_; }
            else { del_edge(ap, bb); add_edge(app, bb); }
        }
        if (cur < best) { best = cur; memcpy(bnb, nb, sizeof nb); memcpy(bdg, dg, sizeof dg);
            if (best == 0) break; }
    }
    memcpy(nb, bnb, sizeof nb); memcpy(dg, bdg, sizeof dg);
    fprintf(stderr, "final best %ld\n", best);
    FILE *o = fopen(argv[6], "w"); fprintf(o, "%d\n", N);
    for (int v = 0; v < N; v++) for (int j = 0; j < dg[v]; j++) if (nb[v][j] > v) fprintf(o, "%d %d\n", v, nb[v][j]);
    fclose(o);
    printf("best %ld\n", best);
    return 0;
}
