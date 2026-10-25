/* hubsa2.c: annealing for one hub side with hubs of arbitrary level sets (card c8, q=3).
   Hub h has a level mask M_h (bit i = level i used, one main edge per used level). Slot s = fi*5+i.
   Capacity: each slot at most 2 hubs. Same-side compatibility: some used slot of h and some used slot of g at
   distance <= 4 in the main graph. Coverage: every main vertex within 6 of some used slot of h.
   Usage: hubsa2 DIST.bin VID.txt MASKS.txt ITERS SEED OUT.txt   (MASKS: K, then K masks as integers 1..31)
   Output: K, then per hub 5 ints: slot id per level (-1 when the level is not used). */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#define NS 560
#define NV 3640
#define NLV 5
#define W9 9
#define WV 57
#define MAXK 800
static uint64_t closeb[NS][W9];
static uint64_t cov6[NS][WV];
static uint8_t *DIST;
static int K, a[MAXK][NLV], msk[MAXK], cap[NS];
static uint64_t U[MAXK][W9];
static uint64_t rng_s;
static inline uint64_t rnd(void) { rng_s ^= rng_s << 13; rng_s ^= rng_s >> 7; rng_s ^= rng_s << 17; return rng_s; }
static inline double urand(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
static void make_U(int h) { memset(U[h], 0, sizeof U[h]); for (int i = 0; i < NLV; i++) if (msk[h] >> i & 1) for (int w = 0; w < W9; w++) U[h][w] |= closeb[a[h][i]][w]; }
static inline int compat(int h, int g) { for (int j = 0; j < NLV; j++) if (msk[g] >> j & 1) { int s = a[g][j]; if ((U[h][s >> 6] >> (s & 63)) & 1) return 1; } return 0; }
static int uncov(int h) {
    int miss = 0;
    for (int w = 0; w < WV; w++) { uint64_t o = 0; for (int i = 0; i < NLV; i++) if (msk[h] >> i & 1) o |= cov6[a[h][i]][w];
        uint64_t full = (w == WV - 1) ? ((1ULL << (NV - 64 * (WV - 1))) - 1) : ~0ULL; miss += __builtin_popcountll(~o & full); }
    return miss;
}
int main(int argc, char **argv) {
    if (argc < 7) { fprintf(stderr, "usage: hubsa2 DIST.bin VID.txt MASKS ITERS SEED OUT\n"); return 2; }
    long iters = atol(argv[4]); rng_s = 88172645463325252ULL ^ ((uint64_t)atol(argv[5]) * 2654435761ULL + 12345); for (int k = 0; k < 10; k++) rnd();
    DIST = malloc((size_t)NS * NV); FILE *f = fopen(argv[1], "rb"); if (!f || fread(DIST, 1, (size_t)NS * NV, f) != (size_t)NS * NV) { fprintf(stderr, "bad dist\n"); return 1; } fclose(f);
    int vid[NS]; f = fopen(argv[2], "r"); for (int s = 0; s < NS; s++) if (fscanf(f, "%d", &vid[s]) != 1) return 1; fclose(f);
    f = fopen(argv[3], "r"); if (!f || fscanf(f, "%d", &K) != 1 || K > MAXK) return 1; for (int h = 0; h < K; h++) if (fscanf(f, "%d", &msk[h]) != 1) return 1; fclose(f);
    memset(closeb, 0, sizeof closeb); memset(cov6, 0, sizeof cov6);
    for (int s = 0; s < NS; s++) {
        for (int t = 0; t < NS; t++) if (DIST[(size_t)s * NV + vid[t]] <= 4) closeb[s][t >> 6] |= 1ULL << (t & 63);
        for (int x = 0; x < NV; x++) if (DIST[(size_t)s * NV + x] <= 6) cov6[s][x >> 6] |= 1ULL << (x & 63);
    }
    /* initial assignment: per level, the hubs using it get distinct slot copies (capacity 2 each) */
    for (int i = 0; i < NLV; i++) {
        int need = 0; for (int h = 0; h < K; h++) if (msk[h] >> i & 1) need++;
        if (need > 2 * 112) { fprintf(stderr, "level %d over capacity (%d)\n", i, need); return 1; }
        int *pool = malloc(sizeof(int) * 224); int m = 0; for (int fi = 0; fi < 112; fi++) { pool[m++] = fi * 5 + i; pool[m++] = fi * 5 + i; }
        for (int k = m - 1; k > 0; k--) { int r = rnd() % (k + 1); int t = pool[k]; pool[k] = pool[r]; pool[r] = t; }
        int c = 0; for (int h = 0; h < K; h++) if (msk[h] >> i & 1) a[h][i] = pool[c++];
        for (int h = 0; h < K; h++) if (!(msk[h] >> i & 1)) a[h][i] = -1;
        free(pool);
    }
    for (int h = 0; h < K; h++) make_U(h);
    const int W = 4; int E = 0;
    for (int h = 0; h < K; h++) for (int g = h + 1; g < K; g++) if (!compat(h, g)) E++;
    int nunc = 0; for (int h = 0; h < K; h++) if (uncov(h) > 0) nunc++; E += W * nunc;
    fprintf(stderr, "K=%d initial E=%d (uncovered hubs %d)\n", K, E, nunc);
    /* level-wise membership lists for swap moves */
    double T0 = 2.0, T1 = 0.02; int bestE = E;
    static int bestA[MAXK][NLV]; memcpy(bestA, a, sizeof a);
    int *mem[NLV]; int nmem[NLV];
    for (int i = 0; i < NLV; i++) { mem[i] = malloc(sizeof(int) * K); nmem[i] = 0; for (int h = 0; h < K; h++) if (msk[h] >> i & 1) mem[i][nmem[i]++] = h; }
    for (long it = 0; it < iters && E > 0; it++) {
        double T = T0 * pow(T1 / T0, (double)it / iters);
        int i = rnd() % NLV; if (nmem[i] < 2) continue;
        int h = mem[i][rnd() % nmem[i]], g = mem[i][rnd() % nmem[i]]; if (h == g) continue;
        int fh = uncov(h) > 0, fg = uncov(g) > 0; int before = W * (fh + fg);
        for (int x = 0; x < K; x++) if (x != h && !compat(h, x)) before++;
        for (int x = 0; x < K; x++) if (x != g && x != h && !compat(g, x)) before++;
        int oh = a[h][i], og = a[g][i];
        a[h][i] = og; a[g][i] = oh; make_U(h); make_U(g);
        int after = 0; int nfh = uncov(h) > 0, nfg = uncov(g) > 0; after = W * (nfh + nfg);
        for (int x = 0; x < K; x++) if (x != h && !compat(h, x)) after++;
        for (int x = 0; x < K; x++) if (x != g && x != h && !compat(g, x)) after++;
        int dE = after - before;
        if (dE <= 0 || urand() < exp(-dE / T)) { E += dE; }
        else { a[h][i] = oh; a[g][i] = og; make_U(h); make_U(g); }
        if (E < bestE) { bestE = E; memcpy(bestA, a, sizeof a); }
        if ((it & ((1 << 22) - 1)) == 0) fprintf(stderr, "it %ld T %.3f E %d best %d\n", it, T, E, bestE);
    }
    memcpy(a, bestA, sizeof a); for (int h = 0; h < K; h++) make_U(h);
    int pairs = 0; for (int h = 0; h < K; h++) for (int g = h + 1; g < K; g++) if (!compat(h, g)) pairs++;
    int nu = 0; for (int h = 0; h < K; h++) if (uncov(h) > 0) nu++;
    fprintf(stderr, "result K=%d: incompatible pairs %d, uncovered hubs %d (best E %d)\n", K, pairs, nu, bestE);
    f = fopen(argv[6], "w"); fprintf(f, "%d\n", K);
    for (int h = 0; h < K; h++) { for (int i = 0; i < NLV; i++) fprintf(f, "%d ", (msk[h] >> i & 1) ? a[h][i] : -1); fprintf(f, "\n"); }
    fclose(f);
    printf("K %d incompatible %d uncovered %d %s\n", K, pairs, nu, (pairs == 0 && nu == 0) ? "FEASIBLE" : "infeasible");
    return 0;
}
