/* hubsa4.c (card c8, q=3): annealer for one hub side, hubs with arbitrary level sets (masks), reslot + swap moves.
   Energy = PW * (#incompatible same-side pairs) + sum over hubs of (#main vertices not within 6 of a used slot).
   (Coverage counted in vertices, so the search has a gradient; hubsa2 used a per-hub flag and stalled.)
   Slot s = fi*5 + i; a slot holds at most 2 hubs. Compatibility: some used slot of h and some used slot of g at
   main-graph distance <= 4.   Usage: hubsa4 DIST.bin VID.txt MASKS ITERS SEED OUT */
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
#define MAXK 400
#define PW 16
static uint64_t closeb[NS][W9], cov6[NS][WV];
static uint8_t *DIST;
static int K, a[MAXK][NLV], msk[MAXK], cnt[NS];
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
static int hub_pairs(int h) { int c = 0; for (int x = 0; x < K; x++) if (x != h && !compat(h, x)) c++; return c; }
int main(int argc, char **argv) {
    if (argc < 7) { fprintf(stderr, "usage: hubsa4 DIST.bin VID.txt MASKS ITERS SEED OUT\n"); return 2; }
    long iters = atol(argv[4]); rng_s = 88172645463325252ULL ^ ((uint64_t)atol(argv[5]) * 2654435761ULL + 777); for (int k = 0; k < 10; k++) rnd();
    DIST = malloc((size_t)NS * NV); FILE *f = fopen(argv[1], "rb"); if (!f || fread(DIST, 1, (size_t)NS * NV, f) != (size_t)NS * NV) return 1; fclose(f);
    int vid[NS]; f = fopen(argv[2], "r"); for (int s = 0; s < NS; s++) if (fscanf(f, "%d", &vid[s]) != 1) return 1; fclose(f);
    f = fopen(argv[3], "r"); if (!f || fscanf(f, "%d", &K) != 1 || K > MAXK) return 1; for (int h = 0; h < K; h++) if (fscanf(f, "%d", &msk[h]) != 1) return 1; fclose(f);
    memset(closeb, 0, sizeof closeb); memset(cov6, 0, sizeof cov6);
    for (int s = 0; s < NS; s++) {
        for (int t = 0; t < NS; t++) if (DIST[(size_t)s * NV + vid[t]] <= 4) closeb[s][t >> 6] |= 1ULL << (t & 63);
        for (int x = 0; x < NV; x++) if (DIST[(size_t)s * NV + x] <= 6) cov6[s][x >> 6] |= 1ULL << (x & 63);
    }
    memset(cnt, 0, sizeof cnt);
    for (int i = 0; i < NLV; i++) {
        int need = 0; for (int h = 0; h < K; h++) if (msk[h] >> i & 1) need++;
        if (need > 224) { fprintf(stderr, "level %d over capacity\n", i); return 1; }
        int pool[224], m = 0; for (int fi = 0; fi < 112; fi++) { pool[m++] = fi * 5 + i; pool[m++] = fi * 5 + i; }
        for (int k = m - 1; k > 0; k--) { int r = rnd() % (k + 1); int t = pool[k]; pool[k] = pool[r]; pool[r] = t; }
        int c = 0; for (int h = 0; h < K; h++) { if (msk[h] >> i & 1) { a[h][i] = pool[c]; cnt[pool[c]]++; c++; } else a[h][i] = -1; }
    }
    for (int h = 0; h < K; h++) make_U(h);
    long E = 0; for (int h = 0; h < K; h++) { for (int g = h + 1; g < K; g++) if (!compat(h, g)) E += PW; E += uncov(h); }
    fprintf(stderr, "K=%d initial E=%ld\n", K, E);
    long bestE = E; static int bestA[MAXK][NLV]; memcpy(bestA, a, sizeof a);
    int *mem[NLV], nmem[NLV];
    for (int i = 0; i < NLV; i++) { mem[i] = malloc(sizeof(int) * K); nmem[i] = 0; for (int h = 0; h < K; h++) if (msk[h] >> i & 1) mem[i][nmem[i]++] = h; }
    double T0 = 12.0, T1 = 0.15;
    for (long it = 0; it < iters && E > 0; it++) {
        double T = T0 * pow(T1 / T0, (double)it / iters);
        int i = rnd() % NLV; if (nmem[i] < 1) continue;
        if (rnd() & 1) {   /* reslot: hub h takes a free copy of a level-i slot */
            int h = mem[i][rnd() % nmem[i]]; int t = (int)(rnd() % 112) * 5 + i; if (cnt[t] >= 2 || t == a[h][i]) continue;
            long before = PW * 0 + uncov(h) + PW * hub_pairs(h);
            int oh = a[h][i]; a[h][i] = t; make_U(h);
            long after = uncov(h) + PW * hub_pairs(h);
            long dE = after - before;
            if (dE <= 0 || urand() < exp(-dE / T)) { E += dE; cnt[oh]--; cnt[t]++; }
            else { a[h][i] = oh; make_U(h); }
        } else {           /* swap the level-i slots of two hubs (counts unchanged) */
            if (nmem[i] < 2) continue;
            int h = mem[i][rnd() % nmem[i]], g = mem[i][rnd() % nmem[i]]; if (h == g) continue;
            /* pair terms: hubs h and g against all others and each other (count pairs once) */
            long before = uncov(h) + uncov(g) + PW * (hub_pairs(h) + hub_pairs(g) - (!compat(h, g) ? 1 : 0));
            int oh = a[h][i], og = a[g][i];
            a[h][i] = og; a[g][i] = oh; make_U(h); make_U(g);
            long after = uncov(h) + uncov(g) + PW * (hub_pairs(h) + hub_pairs(g) - (!compat(h, g) ? 1 : 0));
            long dE = after - before;
            if (dE <= 0 || urand() < exp(-dE / T)) { E += dE; }
            else { a[h][i] = oh; a[g][i] = og; make_U(h); make_U(g); }
        }
        if (E < bestE) { bestE = E; memcpy(bestA, a, sizeof a); }
        if ((it & ((1 << 22) - 1)) == 0) fprintf(stderr, "it %ld T %.3f E %ld best %ld\n", it, T, E, bestE);
    }
    memcpy(a, bestA, sizeof a); for (int h = 0; h < K; h++) make_U(h);
    int pairs = 0; for (int h = 0; h < K; h++) for (int g = h + 1; g < K; g++) if (!compat(h, g)) pairs++;
    int unc = 0, nu = 0; for (int h = 0; h < K; h++) { int u = uncov(h); unc += u; if (u) nu++; }
    fprintf(stderr, "result K=%d: incompatible pairs %d, uncovered hubs %d, uncovered vertex-sum %d (best E %ld)\n", K, pairs, nu, unc, bestE);
    f = fopen(argv[6], "w"); fprintf(f, "%d\n", K);
    for (int h = 0; h < K; h++) { for (int i = 0; i < NLV; i++) fprintf(f, "%d ", (msk[h] >> i & 1) ? a[h][i] : -1); fprintf(f, "\n"); }
    fclose(f);
    printf("K %d incompatible %d uncovered_hubs %d %s\n", K, pairs, nu, (pairs == 0 && nu == 0) ? "FEASIBLE" : "infeasible");
    return 0;
}
