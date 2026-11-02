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

static int EXC = 0; static long last_far = 0;
static long far_count(void) {
    /* EXC=0: far = unordered pairs at distance > 7. EXC=1: excess = sum over pairs of max(0, dist - 7) (smoother). */
    static u64 R[MAXN][NW], F[MAXN][NW], G[MAXN][NW];
    int nw = (N + 63) / 64;
    for (int v = 0; v < N; v++) for (int w = 0; w < nw; w++) { R[v][w] = 0; F[v][w] = 0; }
    for (int v = 0; v < N; v++) { R[v][v >> 6] |= 1ULL << (v & 63); F[v][v >> 6] |= 1ULL << (v & 63); }
    long excess = 0, far7 = 0;
    for (int step = 1; step <= 12; step++) {
        for (int v = 0; v < N; v++) {
            for (int w = 0; w < nw; w++) G[v][w] = 0;
            for (int j = 0; j < dg[v]; j++) { int u = nb[v][j]; for (int w = 0; w < nw; w++) G[v][w] |= F[u][w]; }
            for (int w = 0; w < nw; w++) G[v][w] &= ~R[v][w];
        }
        for (int v = 0; v < N; v++) for (int w = 0; w < nw; w++) { F[v][w] = G[v][w]; R[v][w] |= G[v][w]; }
        long reached = 0;
        for (int v = 0; v < N; v++) for (int w = 0; w < nw; w++) reached += __builtin_popcountll(R[v][w]);
        long unreached = (long)N * (N - 1) - (reached - N);   /* ordered pairs at distance > step */
        if (step == 7) far7 = unreached / 2;
        if (step >= 7) excess += unreached;
        if (unreached == 0) break;
    }
    last_far = far7;
    if (EXC) return excess / 2;
    return far7;
}

static int has_edge(int a, int b) { for (int j = 0; j < dg[a]; j++) if (nb[a][j] == b) return 1; return 0; }
static void del_edge(int a, int b) {
    for (int j = 0; j < dg[a]; j++) if (nb[a][j] == b) { nb[a][j] = nb[a][--dg[a]]; break; }
    for (int j = 0; j < dg[b]; j++) if (nb[b][j] == a) { nb[b][j] = nb[b][--dg[b]]; break; }
}
static void add_edge(int a, int b) { nb[a][dg[a]++] = b; nb[b][dg[b]++] = a; }

int main(int argc, char **argv) {
    /* c7scan FILE : exhaustive scan of all 2-switches and deficiency moves; prints the best far reachable in one move */
    FILE *f = fopen(argv[1], "r"); int m = 0, a, b; static int ea[1000], eb[1000];
    if (fscanf(f, "%d", &N) != 1) return 2;
    while (fscanf(f, "%d %d", &a, &b) == 2) { ea[m] = a; eb[m] = b; m++; }
    fclose(f);
    memset(dg, 0, sizeof dg);
    for (int i = 0; i < m; i++) add_edge(ea[i], eb[i]);
    for (int v = 0; v < N; v++) col[v] = -1;
    static int q[MAXN]; int h = 0, t = 0; col[0] = 0; q[t++] = 0;
    while (h < t) { int v = q[h++]; for (int j = 0; j < dg[v]; j++) { int u = nb[v][j]; if (col[u] < 0) { col[u] = 1 - col[v]; q[t++] = u; } } }
    long cur = far_count();
    printf("start far %ld\n", cur);
    static int E1[1000], E2[1000], ne = 0;
    for (int v = 0; v < N; v++) if (col[v] == 0) for (int j = 0; j < dg[v]; j++) { E1[ne] = v; E2[ne] = nb[v][j]; ne++; }
    long bestm = 1L << 40; long nmoves = 0, nsame = 0;
    for (int i = 0; i < ne; i++) for (int j = i + 1; j < ne; j++) {
        int a1 = E1[i], b1 = E2[i], a2 = E1[j], b2 = E2[j];
        if (a1 == a2 || b1 == b2) continue;
        if (has_edge(a1, b2) || has_edge(a2, b1)) continue;
        del_edge(a1, b1); del_edge(a2, b2); add_edge(a1, b2); add_edge(a2, b1);
        long v = far_count(); nmoves++;
        if (v < bestm) { bestm = v; printf("M1 %d-%d %d-%d -> far %ld\n", a1, b1, a2, b2, v); }
        if (v == cur) nsame++;
        del_edge(a1, b2); del_edge(a2, b1); add_edge(a1, b1); add_edge(a2, b2);
    }
    /* deficiency moves */
    for (int ap = 0; ap < N; ap++) { if (col[ap] != 0 || dg[ap] >= 3) continue;
        for (int bb = 0; bb < N; bb++) { if (col[bb] != 1 || dg[bb] == 0 || has_edge(ap, bb)) continue;
            for (int j = 0; j < dg[bb]; j++) { int app = nb[bb][j]; if (dg[app] != 3) continue;
                del_edge(app, bb); add_edge(ap, bb); long v = far_count(); nmoves++;
                if (v < bestm) { bestm = v; printf("M2 %d-%d from %d -> far %ld\n", ap, bb, app, v); }
                del_edge(ap, bb); add_edge(app, bb);
            } } }
    printf("scanned %ld moves, best one-move far %ld, start %ld\n", nmoves, bestm, cur);
    return 0;
}
