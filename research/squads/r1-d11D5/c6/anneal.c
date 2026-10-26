/* Simulated annealing over Z4 voltages on the 1782-vertex base (AS(9)+2 quadrics, 11-regular bipartite).
   Cost = #uncovered (ordered same-side pair, Z4 element) over non-backtracking walks of length 2 and 4
   (closed 4-walks for x=y), weight 2 per unordered off-diagonal pair, 1 per diagonal entry.
   Cross-side pairs are not in the cost (checked afterwards with liftcheck).
   usage: anneal base.txt iters seed out_lift.txt T0 T1 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdint.h>
#define NV 1782
#define MAXE 9801
#define MAXD 12
static int NE, eA[MAXE], eB[MAXE], sideOf[NV], degc[NV], adjv[NV][MAXD], adje[NV][MAXD];
static int32_t *pid; static int P; static int *wtP; static uint16_t (*cov)[4];
static int32_t *wpair; static int32_t (*wed)[4]; static int8_t (*wsg)[4]; static uint8_t *wval;
static int32_t *incoff, *inc, *cntInc, *fillc;
static int64_t nW = 0; static int mode = 0;
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rng(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline double urand(void) { return (rng() >> 11) * (1.0 / 9007199254740992.0); }
static void rec(int x, int y, int len, const int *e, const int *s) {
    if (mode == 0) { nW++; for (int k = 0; k < len; k++) cntInc[e[k]]++; return; }
    int64_t w = nW++;
    wpair[w] = pid[x * NV + y];
    for (int k = 0; k < 4; k++) { wed[w][k] = k < len ? e[k] : -1; wsg[w][k] = k < len ? (int8_t)s[k] : 0; }
    for (int k = 0; k < len; k++) { int ed = e[k]; inc[incoff[ed] + fillc[ed]++] = (int32_t)(w * 4 + k); }
}
static void walk_from(int x) {
    int e[4], s[4];
    for (int i = 0; i < degc[x]; i++) {
        int w1 = adjv[x][i], e1 = adje[x][i], s1 = sideOf[x] == 0 ? 1 : -1;
        for (int j = 0; j < degc[w1]; j++) {
            int w2 = adjv[w1][j]; if (w2 == x) continue;
            int e2 = adje[w1][j], s2 = sideOf[w1] == 0 ? 1 : -1;
            if (w2 > x) { e[0] = e1; s[0] = s1; e[1] = e2; s[1] = s2; rec(x, w2, 2, e, s); }
            for (int k = 0; k < degc[w2]; k++) {
                int w3 = adjv[w2][k]; if (w3 == w1) continue;
                int e3 = adje[w2][k], s3 = sideOf[w2] == 0 ? 1 : -1;
                for (int l = 0; l < degc[w3]; l++) {
                    int w4 = adjv[w3][l]; if (w4 == w2 || w4 < x) continue;
                    int e4 = adje[w3][l], s4 = sideOf[w3] == 0 ? 1 : -1;
                    e[0] = e1; s[0] = s1; e[1] = e2; s[1] = s2; e[2] = e3; s[2] = s3; e[3] = e4; s[3] = s4;
                    rec(x, w4, 4, e, s);
                }
            }
        }
    }
}
int main(int argc, char **argv) {
    if (argc < 8) { fprintf(stderr, "usage: anneal base.txt iters seed out_lift.txt T0 T1 init(0 random|1 zero)\n"); return 1; }
    long iters = atol(argv[2]); rs ^= (uint64_t)atoll(argv[3]) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 10; i++) rng();
    double T0 = atof(argv[5]), T1 = atof(argv[6]);
    FILE *f = fopen(argv[1], "r"); NE = 0;
    while (NE < MAXE && fscanf(f, "%d %d", &eA[NE], &eB[NE]) == 2) NE++;
    fclose(f);
    for (int i = 0; i < NE; i++) {
        int a = eA[i], b = eB[i];
        sideOf[a] = 0; sideOf[b] = 1;
        adjv[a][degc[a]] = b; adje[a][degc[a]++] = i;
        adjv[b][degc[b]] = a; adje[b][degc[b]++] = i;
    }
    pid = malloc(sizeof(int32_t) * NV * NV);
    P = 0;
    for (int x = 0; x < NV; x++) for (int y = x; y < NV; y++) if (sideOf[x] == sideOf[y]) { pid[x * NV + y] = pid[y * NV + x] = P++; }
    wtP = malloc(sizeof(int) * P); cov = calloc(P, sizeof(*cov));
    for (int x = 0; x < NV; x++) for (int y = x; y < NV; y++) if (sideOf[x] == sideOf[y]) wtP[pid[x * NV + y]] = (x == y) ? 1 : 2;
    for (int x = 0; x < NV; x++) cov[pid[x * NV + x]][0] = 1;   /* trivial walk */
    mode = 0; nW = 0; cntInc = calloc(NE, sizeof(int32_t));
    for (int x = 0; x < NV; x++) walk_from(x);
    wpair = malloc(sizeof(int32_t) * nW); wed = malloc(sizeof(*wed) * nW); wsg = malloc(sizeof(*wsg) * nW); wval = malloc(nW);
    incoff = malloc(sizeof(int32_t) * (NE + 1)); incoff[0] = 0;
    for (int i = 0; i < NE; i++) incoff[i + 1] = incoff[i] + cntInc[i];
    inc = malloc(sizeof(int32_t) * incoff[NE]); fillc = calloc(NE, sizeof(int32_t));
    mode = 1; nW = 0;
    for (int x = 0; x < NV; x++) walk_from(x);
    fprintf(stderr, "pairs P=%d walks=%ld incidences=%d\n", P, (long)nW, incoff[NE]);
    int phi[MAXE], best_phi[MAXE];
    for (int i = 0; i < NE; i++) phi[i] = argv[7][0] == '1' ? 0 : (int)(rng() & 3);
    for (int64_t w = 0; w < nW; w++) {
        int v = 0;
        for (int k = 0; k < 4; k++) if (wed[w][k] >= 0) v += wsg[w][k] * phi[wed[w][k]];
        wval[w] = (uint8_t)(((v % 4) + 4) % 4);
        cov[wpair[w]][wval[w]]++;
    }
    int64_t cost = 0;
    for (int p = 0; p < P; p++) for (int h = 0; h < 4; h++) if (cov[p][h] == 0) cost += wtP[p];
    int64_t best = cost; memcpy(best_phi, phi, sizeof(phi));
    fprintf(stderr, "initial same-side cost (ordered) = %ld\n", (long)cost);
    for (long it = 0; it < iters; it++) {
        double T = T0 * pow(T1 / T0, (double)it / (double)iters);
        int ed = (int)(rng() % NE), old = phi[ed], nw = (old + 1 + (int)(rng() % 3)) & 3, d = (nw - old) & 3;
        int64_t delta = 0; int32_t *lst = inc + incoff[ed]; int cnt = incoff[ed + 1] - incoff[ed];
        for (int q = 0; q < cnt; q++) {
            int32_t o = lst[q]; int w = o >> 2, pos = o & 3, sg = wsg[w][pos];
            int v = wval[w], nv = (v + (sg > 0 ? d : 4 - d)) & 3, p = wpair[w];
            if (--cov[p][v] == 0) delta += wtP[p];
            if (cov[p][nv]++ == 0) delta -= wtP[p];
            wval[w] = (uint8_t)nv;
        }
        if (delta <= 0 || urand() < exp(-(double)delta / T)) {
            phi[ed] = nw; cost += delta;
            if (cost < best) { best = cost; memcpy(best_phi, phi, sizeof(phi)); }
        } else {
            for (int q = 0; q < cnt; q++) {
                int32_t o = lst[q]; int w = o >> 2, pos = o & 3, sg = wsg[w][pos];
                int nv = wval[w], v = (nv - (sg > 0 ? d : 4 - d)) & 3, p = wpair[w];
                cov[p][nv]--; cov[p][v]++; wval[w] = (uint8_t)v;
            }
        }
        if ((it + 1) % 200000 == 0) fprintf(stderr, "it %ld T %.4f cost %ld best %ld\n", it + 1, T, (long)cost, (long)best);
    }
    /* write best voltages in liftcheck format */
    int idxA[NV], idxB[NV], na = 0, nb = 0;
    for (int v = 0; v < NV; v++) { if (sideOf[v] == 0) idxA[v] = na++; else idxB[v] = nb++; }
    FILE *g = fopen(argv[4], "w");
    fprintf(g, "%d %d 4\n", na, nb);
    for (int i = 0; i < NE; i++) fprintf(g, "%d %d %d\n", idxA[eA[i]], idxB[eB[i]], best_phi[i]);
    fclose(g);
    printf("BEST same-side cost (ordered, Z4, walk-based) = %ld  final = %ld\n", (long)best, (long)cost);
    return 0;
}
