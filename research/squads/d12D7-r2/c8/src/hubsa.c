/* hubsa.c: simulated annealing for one hub side at q=3 (card c8).
   Slots: s = fi*5 + i (fi a freed point, i a level); each slot takes at most 2 hubs (2 free edge slots per vertex).
   A hub = one slot per level (5 main edges). Hub-hub same-side compatibility: some slot of h and some slot of g
   at distance <= 4 in the main graph (then both hubs are within 7). Coverage: every main vertex within 6 of some slot of h.
   Usage: hubsa DIST.bin VID.txt K ITERS SEED OUT.txt
   DIST.bin: 560 x 3640 uint8 distances from slot vertices; VID.txt: 560 slot vertex ids (in the main graph). */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#define NS 560
#define NV 3640
#define NLV 5
#define W9 9      /* words for 560 bits */
#define WV 57     /* words for 3640 bits */
#define MAXK 400
static uint64_t closeb[NS][W9];
static uint64_t cov6[NS][WV];
static uint8_t *DIST;
static int K, a[MAXK][NLV], cnt[NS];
static uint64_t U[MAXK][W9];
static uint64_t rng_s;
static inline uint64_t rnd(void) { rng_s ^= rng_s << 13; rng_s ^= rng_s >> 7; rng_s ^= rng_s << 17; return rng_s; }
static inline double urand(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
static void make_U(int h) { memset(U[h], 0, sizeof U[h]); for (int i = 0; i < NLV; i++) for (int w = 0; w < W9; w++) U[h][w] |= closeb[a[h][i]][w]; }
static inline int compat(int h, int g) { for (int j = 0; j < NLV; j++) { int s = a[g][j]; if ((U[h][s >> 6] >> (s & 63)) & 1) return 1; } return 0; }
static int uncov(int h) {
    int miss = 0;
    for (int w = 0; w < WV; w++) { uint64_t o = 0; for (int i = 0; i < NLV; i++) o |= cov6[a[h][i]][w];
        uint64_t full = (w == WV - 1) ? ((1ULL << (NV - 64 * (WV - 1))) - 1) : ~0ULL; miss += __builtin_popcountll(~o & full); }
    return miss;
}
static int uncovflag(int h) { return uncov(h) > 0; }
/* cost contributions */
static int cost_hub(int h) { /* incompatible pairs (h,g) for all g != h, and coverage flag */
    int c = 0; for (int g = 0; g < K; g++) if (g != h && !compat(h, g)) c++;
    return c;
}
int main(int argc, char **argv) {
    if (argc < 7) { fprintf(stderr, "usage: hubsa DIST.bin VID.txt K ITERS SEED OUT\n"); return 2; }
    K = atoi(argv[3]); long iters = atol(argv[4]); rng_s = 88172645463325252ULL ^ (uint64_t)atol(argv[5]) * 2654435761ULL; for (int k = 0; k < 10; k++) rnd();
    DIST = malloc((size_t)NS * NV); FILE *f = fopen(argv[1], "rb"); if (!f || fread(DIST, 1, (size_t)NS * NV, f) != (size_t)NS * NV) { fprintf(stderr, "bad dist\n"); return 1; } fclose(f);
    int vid[NS]; f = fopen(argv[2], "r"); for (int s = 0; s < NS; s++) if (fscanf(f, "%d", &vid[s]) != 1) return 1; fclose(f);
    memset(closeb, 0, sizeof closeb); memset(cov6, 0, sizeof cov6);
    for (int s = 0; s < NS; s++) {
        for (int t = 0; t < NS; t++) if (DIST[(size_t)s * NV + vid[t]] <= 4) closeb[s][t >> 6] |= 1ULL << (t & 63);
        for (int x = 0; x < NV; x++) if (DIST[(size_t)s * NV + x] <= 6) cov6[s][x >> 6] |= 1ULL << (x & 63);
    }
    /* random initial assignment respecting capacity 2 per slot */
    memset(cnt, 0, sizeof cnt);
    for (int i = 0; i < NLV; i++) {
        int fis = 112; int *pool = malloc(sizeof(int) * 2 * fis); int m = 0;
        for (int fi = 0; fi < fis; fi++) { pool[m++] = fi * 5 + i; pool[m++] = fi * 5 + i; }
        for (int k = m - 1; k > 0; k--) { int r = rnd() % (k + 1); int t = pool[k]; pool[k] = pool[r]; pool[r] = t; }
        for (int h = 0; h < K; h++) { a[h][i] = pool[h]; cnt[pool[h]]++; }   /* K <= 224 per level */
        free(pool);
    }
    for (int h = 0; h < K; h++) make_U(h);
    /* energy: number of incompatible pairs + W * hubs not covering all vertices */
    const int W = 4; int E = 0;
    for (int h = 0; h < K; h++) for (int g = h + 1; g < K; g++) if (!compat(h, g)) E++;
    int nunc = 0; for (int h = 0; h < K; h++) nunc += uncovflag(h); E += W * nunc;
    fprintf(stderr, "K=%d initial E=%d (uncovered hubs %d)\n", K, E, nunc);
    double T0 = 2.0, T1 = 0.02; int bestE = E;
    int *bestA = malloc(sizeof(int) * K * NLV); memcpy(bestA, a, sizeof(int) * K * NLV);
    for (long it = 0; it < iters && E > 0; it++) {
        double T = T0 * pow(T1 / T0, (double)it / iters);
        int i = rnd() % NLV; int h = rnd() % K; int g = rnd() % K;
        int oldh = a[h][i], oldg = a[g][i];
        int mv = rnd() % 4;
        if (mv < 3 || cnt[oldh] >= 0) {
            /* swap level-i slots of h and g (h != g) */
            if (h == g) continue;
            /* energy before: pairs involving h or g, coverage flags of h and g */
            int before = 0, after = 0;
            int fh = uncovflag(h), fg = uncovflag(g);
            before = W * (fh + fg);
            for (int x = 0; x < K; x++) { if (x != h && !compat(h, x)) before++; }
            for (int x = 0; x < K; x++) { if (x != g && x != h && !compat(g, x)) before++; }
            /* apply */
            a[h][i] = oldg; a[g][i] = oldh; make_U(h); make_U(g);
            int aft_pairs = 0; int nfh = uncovflag(h), nfg = uncovflag(g);
            for (int x = 0; x < K; x++) { if (x != h && !compat(h, x)) aft_pairs++; }
            for (int x = 0; x < K; x++) { if (x != g && x != h && !compat(g, x)) aft_pairs++; }
            after = aft_pairs + W * (nfh + nfg);
            int dE = after - before;
            if (dE <= 0 || urand() < exp(-dE / T)) { E += dE; }
            else { a[h][i] = oldh; a[g][i] = oldg; make_U(h); make_U(g); }
        }
        if (E < bestE) { bestE = E; memcpy(bestA, a, sizeof(int) * K * NLV); }
        if ((it & ((1 << 22) - 1)) == 0) fprintf(stderr, "it %ld T %.3f E %d best %d\n", it, T, E, bestE);
    }
    /* recount exactly from bestA */
    memcpy(a, bestA, sizeof(int) * K * NLV); for (int h = 0; h < K; h++) make_U(h);
    int pairs = 0; for (int h = 0; h < K; h++) for (int g = h + 1; g < K; g++) if (!compat(h, g)) pairs++;
    int nu = 0; for (int h = 0; h < K; h++) nu += uncovflag(h);
    fprintf(stderr, "result K=%d: incompatible pairs %d, uncovered hubs %d\n", K, pairs, nu);
    f = fopen(argv[6], "w"); fprintf(f, "%d\n", K);
    for (int h = 0; h < K; h++) { for (int i = 0; i < NLV; i++) fprintf(f, "%d ", a[h][i]); fprintf(f, "\n"); }
    fclose(f);
    printf("K %d incompatible %d uncovered %d %s\n", K, pairs, nu, (pairs == 0 && nu == 0) ? "FEASIBLE" : "infeasible");
    return 0;
}
