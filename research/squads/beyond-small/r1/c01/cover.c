/* c01: cover one side of the (16,5) graph by radius-3 balls of the other side.
   usage: cover SIDE K ITERS SEED T0 T1 [edges]
   SIDE 0: universe = A (ids 0..16895), candidates = B (16896..33791)
   SIDE 1: universe = B, candidates = A.
   Prints greedy size first, then simulated annealing for K sets, writes cover_side<S>_k<K>.txt if cost 0. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>

#define NH 16896
#define NN 33792
#define DEG 16
#define W 264

static int adj[NN][DEG];
static int stamp[NN];
static int curstamp = 0;
static int uoff, coff;

static int ball(int c, int *out) {
    curstamp++;
    int n = 0;
    for (int i = 0; i < DEG; i++) {
        int a = adj[c][i];
        if (stamp[a] != curstamp) { stamp[a] = curstamp; out[n++] = a - uoff; }
    }
    for (int i = 0; i < DEG; i++) {
        int a1 = adj[c][i];
        for (int j = 0; j < DEG; j++) {
            int b2 = adj[a1][j];
            for (int k = 0; k < DEG; k++) {
                int a3 = adj[b2][k];
                if (stamp[a3] != curstamp) { stamp[a3] = curstamp; out[n++] = a3 - uoff; }
            }
        }
    }
    return n;
}

static uint64_t bits[NH][W];

static uint64_t rng_s = 88172645463325252ULL;
static inline uint64_t rnd(void) {
    rng_s ^= rng_s << 13; rng_s ^= rng_s >> 7; rng_s ^= rng_s << 17; return rng_s;
}
static inline double urand(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

int main(int argc, char **argv) {
    if (argc < 7) { fprintf(stderr, "usage: cover SIDE K ITERS SEED T0 T1 [edges]\n"); return 1; }
    int side = atoi(argv[1]);
    int K = atoi(argv[2]);
    long long iters = atoll(argv[3]);
    rng_s ^= (uint64_t)atoll(argv[4]) * 0x9E3779B97F4A7C15ULL; if (!rng_s) rng_s = 1;
    double T0 = atof(argv[5]), T1 = atof(argv[6]);
    const char *path = argc > 7 ? argv[7] : "/home/user/degree-diameter/research/squads/beyond-small/data/d16D5_n33792.edges";
    uoff = side == 0 ? 0 : NH;
    coff = side == 0 ? NH : 0;

    FILE *f = fopen(path, "r");
    if (!f) { perror("open"); return 1; }
    int n; if (fscanf(f, "%d", &n) != 1 || n != NN) { fprintf(stderr, "bad n\n"); return 1; }
    static int deg[NN];
    for (int e = 0; e < NN * DEG / 2; e++) {
        int u, v; if (fscanf(f, "%d %d", &u, &v) != 2) { fprintf(stderr, "short\n"); return 1; }
        adj[u][deg[u]++] = v; adj[v][deg[v]++] = u;
    }
    fclose(f);
    for (int v = 0; v < NN; v++) if (deg[v] != DEG) { fprintf(stderr, "deg\n"); return 1; }

    /* precompute bitsets of candidate balls (for greedy) */
    int *buf = malloc(sizeof(int) * NN);
    int bsz_min = 1 << 30, bsz_max = 0;
    for (int j = 0; j < NH; j++) {
        int c = coff + j;
        int m = ball(c, buf);
        if (m < bsz_min) bsz_min = m;
        if (m > bsz_max) bsz_max = m;
        for (int t = 0; t < m; t++) bits[j][buf[t] >> 6] |= 1ULL << (buf[t] & 63);
    }
    fprintf(stderr, "ball sizes min %d max %d\n", bsz_min, bsz_max);

    /* greedy */
    uint64_t U[W];
    memset(U, 0xff, sizeof U);
    int used[NH]; memset(used, 0, sizeof used);
    int gsz = 0;
    while (1) {
        int bestj = -1, bestg = -1;
        for (int j = 0; j < NH; j++) {
            if (used[j]) continue;
            int g = 0;
            for (int w = 0; w < W; w++) g += __builtin_popcountll(bits[j][w] & U[w]);
            if (g > bestg) { bestg = g; bestj = j; }
        }
        if (bestg <= 0) break;
        used[bestj] = 1; gsz++;
        for (int w = 0; w < W; w++) U[w] &= ~bits[bestj][w];
        int rem = 0; for (int w = 0; w < W; w++) rem += __builtin_popcountll(U[w]);
        fprintf(stderr, "greedy step %d: cand %d gain %d, uncovered %d\n", gsz, coff + bestj, bestg, rem);
        if (rem == 0) break;
    }
    printf("greedy size %d\n", gsz);
    fflush(stdout);

    /* simulated annealing with K sets */
    static int cnt[NH];
    static int inset[NH];
    int chosen[64];
    memset(cnt, 0, sizeof cnt); memset(inset, 0, sizeof inset);
    for (int i = 0; i < K; i++) {
        int j;
        do { j = rnd() % NH; } while (inset[j]);
        inset[j] = 1; chosen[i] = j;
    }
    int cost = NH;
    static int bufS[NN], bufT[NN];
    for (int i = 0; i < K; i++) {
        int m = ball(coff + chosen[i], buf);
        for (int t = 0; t < m; t++) if (cnt[buf[t]]++ == 0) cost--;
    }
    int bestcost = cost;
    int bestchosen[64]; memcpy(bestchosen, chosen, sizeof chosen);
    for (long long it = 0; it < iters && cost > 0; it++) {
        double T = T0 * pow(T1 / T0, (double)it / (double)iters);
        int i = rnd() % K;
        int s = chosen[i];
        int t;
        do { t = rnd() % NH; } while (inset[t]);
        int nS = ball(coff + s, bufS);
        int nT = ball(coff + t, bufT);
        int d = 0;
        for (int q = 0; q < nS; q++) if (--cnt[bufS[q]] == 0) d++;
        for (int q = 0; q < nT; q++) if (cnt[bufT[q]]++ == 0) d--;
        if (d <= 0 || urand() < exp(-d / T)) {
            chosen[i] = t; inset[s] = 0; inset[t] = 1; cost += d;
            if (cost < bestcost) { bestcost = cost; memcpy(bestchosen, chosen, sizeof chosen); }
        } else {
            for (int q = 0; q < nT; q++) --cnt[bufT[q]];
            for (int q = 0; q < nS; q++) cnt[bufS[q]]++;
        }
        if ((it & 0x3ffff) == 0) fprintf(stderr, "it %lld T %.3f cost %d best %d\n", it, T, cost, bestcost);
    }
    printf("K %d best_cost %d (last cost %d)\n", K, bestcost, cost);
    char fn[256];
    snprintf(fn, sizeof fn, "cover_side%d_k%d.txt", side, K);
    FILE *o = fopen(fn, "w");
    for (int i = 0; i < K; i++) fprintf(o, "%d\n", coff + bestchosen[i]);
    fclose(o);
    printf("wrote %s\n", fn);
    return 0;
}
