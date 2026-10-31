/* hfree.c: "Haar + free matching". Vertices: (g,0) = g, (g,1) = 343 + g, g in Z_7^3 (index a*49+b*7+c).
 * Edges: Haar part (g,0) ~ (g+s,1) for s in S (|S| = K, default 5), plus a free perfect matching (g,0) ~ (sigma(g),1).
 * sigma is annealed by 2-switches (swap sigma(x), sigma(y)); a move is rejected if it creates a duplicate edge
 * (sigma(g) in g+S). Cost = number of unordered vertex pairs at distance > 5 (exact BFS from all 686 vertices).
 * usage: hfree SEED SECS K [SFILE] [OUT]   (SFILE: optional K group elements to use, else random)
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
static double wall(void) { struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts); return ts.tv_sec + 1e-9 * ts.tv_nsec; }
#define N 343
#define V 686
static int S[8], K, sig[N], isig[N];
static int adj[V][8], deg[V];
static unsigned long long rng = 88172645463325252ULL;
static unsigned long long xr(void) { rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; return rng; }
static int add7(int x, int y) {  /* Z_7^3 addition, index a*49+b*7+c */
    int a = x / 49 + y / 49, b = (x / 7) % 7 + (y / 7) % 7, c = x % 7 + y % 7;
    return ((a % 7) * 49) + ((b % 7) * 7) + (c % 7);
}
static int dup(int g, int t) { for (int i = 0; i < K; i++) if (add7(g, S[i]) == t) return 1; return 0; }
static void build(void) {
    for (int v = 0; v < V; v++) deg[v] = 0;
    for (int g = 0; g < N; g++) {
        for (int i = 0; i < K; i++) { int t = N + add7(g, S[i]); adj[g][deg[g]++] = t; adj[t][deg[t]++] = g; }
        int t = N + sig[g]; adj[g][deg[g]++] = t; adj[t][deg[t]++] = g;
    }
}
#define W 11   /* 686 bits = 11 words */
static unsigned long long R0[V][W], R1[V][W];
static long cost(void) {   /* unordered pairs at distance > 5, bitset ball growth (radius 5) */
    for (int v = 0; v < V; v++) { memset(R0[v], 0, sizeof R0[v]); R0[v][v >> 6] |= 1ULL << (v & 63); }
    for (int k = 0; k < 5; k++) {
        for (int v = 0; v < V; v++) {
            for (int w = 0; w < W; w++) R1[v][w] = R0[v][w];
            for (int j = 0; j < deg[v]; j++) { int u = adj[v][j];
                for (int w = 0; w < W; w++) R1[v][w] |= R0[u][w]; }
        }
        memcpy(R0, R1, sizeof R0);
    }
    long miss = 0;
    for (int v = 0; v < V; v++) { int c = 0; for (int w = 0; w < W; w++) c += __builtin_popcountll(R0[v][w]); miss += V - c; }
    return miss / 2;
}

int main(int argc, char **argv) {
    /* usage: haarmin SEED TRIALS  -- random 6-subsets S of Z_7^3, Haar graph H(Z_7^3,S) (6 matchings), min bad */
    rng ^= (unsigned long long)atoll(argv[1]) * 2654435761ULL; for (int i = 0; i < 10; i++) xr();
    long trials = atol(argv[2]); K = 6; long bestc = 1L << 60; int bestS[6];
    for (long tr = 0; tr < trials; tr++) {
        for (int i = 0; i < 6; i++) { int ok; do { S[i] = (int)(xr() % N); ok = S[i] != 0; for (int j = 0; j < i; j++) if (S[i] == S[j]) ok = 0; } while (!ok); }
        /* Haar-6 graph: vertices (g,0)-(g+s,1) for 6 s; encode via adj directly */
        for (int v = 0; v < V; v++) deg[v] = 0;
        for (int g = 0; g < N; g++) for (int i = 0; i < 6; i++) { int t = N + add7(g, S[i]); adj[g][deg[g]++] = t; adj[t][deg[t]++] = g; }
        long c = cost();
        if (c < bestc) { bestc = c; memcpy(bestS, S, sizeof bestS); printf("trial %ld bad %ld S", tr, c); for (int i = 0; i < 6; i++) printf(" %d", S[i]); printf("\n"); fflush(stdout); }
    }
    return 0;
}
