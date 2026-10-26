/* h12: direct simulated annealing on bipartite cubic graphs (no group, no lift).
 * State: simple bipartite cubic graph on sides A={0..k-1}, B={k..2k-1}.
 * Move: bipartition-preserving 2-switch (a1b1,a2b2 -> a1b2,a2b1), rejected if it creates a multi-edge.
 * Cost: number of unordered pairs at distance > D, via bitset reach sets (R_t+1[v] = R_t[v] | OR_u~v R_t[u]).
 * Usage: anneal k D SECONDS SEED OUT.edges T0 T1
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1100
#define MAXW 18   /* 64*18 = 1152 >= MAXN */

static int K, N, D, W;
static int adj[MAXN][3];
static int ea[MAXN*3 / 2 + 8], eb[MAXN*3 / 2 + 8]; /* edge list: a in A, b in B */
static int M;
static uint64_t R[2][MAXN][MAXW];

static uint64_t rng_s[2];
static inline uint64_t rnd(void) {
    uint64_t s1 = rng_s[0]; const uint64_t s0 = rng_s[1];
    rng_s[0] = s0; s1 ^= s1 << 23;
    rng_s[1] = s1 ^ s0 ^ (s1 >> 17) ^ (s0 >> 26);
    return rng_s[1] + s0;
}
static inline double urand(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int has_edge(int a, int b) {
    return adj[a][0] == b || adj[a][1] == b || adj[a][2] == b;
}
static void rep(int v, int old, int nw) {
    for (int t = 0; t < 3; t++) if (adj[v][t] == old) { adj[v][t] = nw; return; }
    fprintf(stderr, "rep fail\n"); exit(1);
}

/* 2-switch on edges i=(a1,b1), j=(a2,b2) -> i=(a1,b2), j=(a2,b1). Involution in (i,j). */
static void do_switch(int i, int j) {
    int a1 = ea[i], b1 = eb[i], a2 = ea[j], b2 = eb[j];
    rep(a1, b1, b2); rep(b1, a1, a2);
    rep(a2, b2, b1); rep(b2, a2, a1);
    eb[i] = b2; eb[j] = b1;
}

static int far_pairs(void) {
    int cur = 0, nxt = 1;
    memset(R[cur], 0, sizeof(R[cur]));
    for (int v = 0; v < N; v++) R[cur][v][v >> 6] |= 1ULL << (v & 63);
    for (int step = 0; step < D; step++) {
        for (int v = 0; v < N; v++) {
            for (int w = 0; w < W; w++) {
                uint64_t x = R[cur][v][w];
                for (int t = 0; t < 3; t++) x |= R[cur][adj[v][t]][w];
                R[nxt][v][w] = x;
            }
        }
        cur ^= 1; nxt ^= 1;
    }
    long long reach = 0;
    for (int v = 0; v < N; v++)
        for (int w = 0; w < W; w++) reach += __builtin_popcountll(R[cur][v][w]);
    long long far_ordered = (long long)N * N - reach;
    return (int)(far_ordered / 2);
}

static int random_start(void) {
    /* configuration model with retries until simple */
    static int stubA[3 * MAXN], stubB[3 * MAXN];
    for (int attempt = 0; attempt < 100000; attempt++) {
        for (int i = 0; i < 3 * K; i++) { stubA[i] = i / 3; stubB[i] = K + i / 3; }
        for (int i = 3 * K - 1; i > 0; i--) { int j = rnd() % (i + 1); int t = stubB[i]; stubB[i] = stubB[j]; stubB[j] = t; }
        for (int v = 0; v < N; v++) adj[v][0] = adj[v][1] = adj[v][2] = -1;
        int ok = 1;
        M = 0;
        for (int i = 0; i < 3 * K && ok; i++) {
            int a = stubA[i], b = stubB[i];
            if (has_edge(a, b)) { ok = 0; break; }
            ea[M] = a; eb[M] = b; M++;
            for (int t = 0; t < 3; t++) if (adj[a][t] < 0) { adj[a][t] = b; break; }
            for (int t = 0; t < 3; t++) if (adj[b][t] < 0) { adj[b][t] = a; break; }
        }
        if (ok) return 1;
    }
    return 0;
}

static void write_edges(const char *fn) {
    FILE *f = fopen(fn, "w");
    if (!f) { perror("open"); exit(1); }
    fprintf(f, "%d\n", N);
    for (int i = 0; i < M; i++) fprintf(f, "%d %d\n", ea[i], eb[i]);
    fclose(f);
}

int main(int argc, char **argv) {
    if (argc < 8) { fprintf(stderr, "usage: anneal k D SECONDS SEED OUT.edges T0 T1\n"); return 1; }
    K = atoi(argv[1]); D = atoi(argv[2]);
    double secs = atof(argv[3]);
    uint64_t seed = strtoull(argv[4], NULL, 10);
    const char *out = argv[5];
    double T0 = atof(argv[6]), T1 = atof(argv[7]);
    N = 2 * K; W = (N + 63) / 64;
    if (N > MAXN) { fprintf(stderr, "too big\n"); return 1; }
    rng_s[0] = seed * 0x9E3779B97F4A7C15ULL + 1; rng_s[1] = seed ^ 0xD1B54A32D192ED03ULL;
    for (int i = 0; i < 20; i++) rnd();

    if (!random_start()) { fprintf(stderr, "no simple start\n"); return 1; }
    int cost = far_pairs();
    int best = cost;
    fprintf(stderr, "start n=%d D=%d cost=%d\n", N, D, cost);

    clock_t c0 = clock();
    long long iters = 0, acc = 0;
    double T = T0;
    while (1) {
        if ((iters & 255) == 0) {
            double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
            if (el >= secs) break;
            double fr = el / secs;
            T = T0 * pow(T1 / T0, fr);
        }
        iters++;
        int i = rnd() % M, j = rnd() % M;
        if (i == j) continue;
        int a1 = ea[i], b1 = eb[i], a2 = ea[j], b2 = eb[j];
        if (a1 == a2 || b1 == b2) continue;
        if (has_edge(a1, b2) || has_edge(a2, b1)) continue;
        do_switch(i, j);
        int nc = far_pairs();
        int delta = nc - cost;
        if (delta <= 0 || urand() < exp(-delta / T)) {
            cost = nc; acc++;
            if (cost < best) {
                best = cost;
                write_edges(out);
                if (best == 0) break;
            }
        } else {
            do_switch(i, j);
        }
    }
    double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
    fprintf(stderr, "done iters=%lld acc=%lld cpu=%.1fs best=%d final=%d\n", iters, acc, el, best, cost);
    /* best written already; ensure file exists even if never improved */
    if (best == cost && cost == 0) {}
    printf("RESULT n=%d k=%d D=%d best_far_pairs=%d miss=%.4f\n", N, K, D, best, 2.0 * best / N);
    return 0;
}
