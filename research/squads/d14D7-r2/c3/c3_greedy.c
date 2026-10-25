/* c3_greedy.c: least-blocking (min-degree) greedy for flag packings in GH(q). Card c3, squad d14D7-r2.
   Zones and disjointness exactly as in cell147/units/pack.c: point zone of flag (p,l) = {p} + W (q^2+1 points),
   line zone = {l} + K (q^2+1 lines). A flag is FREE when its zones meet no placed zone.
   D(f) = number of free flags g != f whose zones meet f's zones (the blocking cost of f).
     proxy (default): sum over f's zone elements x of (number of free flags containing x in their zone) - 1,
       kept up to date in counters FP[point], FL[line]; it double counts flags meeting f in several elements.
     EXACT=k: the k smallest proxies are re-ranked by the exact union count (stamp-based).
   MODE=0: uniform random free flag (control). MODE=1: minimum D, ties broken at random.
   SAMPLE=s: score only s random free flags per step (0 = all free flags).
   Usage: c3_greedy GHFILE SEED OUTFLAGS     Output lines "p l" (flag = point p, line l incident with p).
   Build: gcc -O3 -march=native -o c3_greedy c3_greedy.c */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>

static int P, q, Q1, ZN, NF, nFree = 0;
static int32_t *LP, *PL, *POS;   /* LP[l*Q1+k] = k-th point of line l; PL[p*Q1+a] = a-th line through p;
                                    POS[l*Q1+k] = index of l in PL[LP[l*Q1+k]] */
static uint64_t rs = 0x9E3779B97F4A7C15ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline int rndi(int n) { return (int)(rnd() % (uint64_t)n); }

static uint8_t *occP, *occL, *freeF;     /* occupancy of placed zones; free flag bit */
static uint16_t *FP, *FL;                /* free flags whose point / line zone contains the element */
static int32_t *fList, *fPos;            /* compact list of free flags */
static uint32_t *stamp; static uint32_t curStamp = 0;
static int32_t enumBuf[4096];

/* flag id f = p*Q1 + a, the flag (p, PL[p*Q1+a]) */
static int zoneP(int p, int l, int *out) { int c = 0; out[c++] = p;
    for (int a = 0; a < Q1; a++) { int L = PL[p * Q1 + a]; if (L == l) continue;
        for (int b = 0; b < Q1; b++) { int w = LP[L * Q1 + b]; if (w != p) out[c++] = w; } }
    return c; }
static int zoneL(int p, int l, int *out) { int c = 0; out[c++] = l;
    for (int k = 0; k < Q1; k++) { int x = LP[l * Q1 + k]; if (x == p) continue;
        for (int b = 0; b < Q1; b++) { int K = PL[x * Q1 + b]; if (K != l) out[c++] = K; } }
    return c; }
/* all flags whose point zone contains point x (1464 = Q1 + Q1*q*q of them) */
static int ptFlags(int x, int32_t *out) { int c = 0;
    for (int a = 0; a < Q1; a++) out[c++] = x * Q1 + a;
    for (int a = 0; a < Q1; a++) { int M = PL[x * Q1 + a];
        for (int b = 0; b < Q1; b++) { int pp = LP[M * Q1 + b]; if (pp == x) continue;
            for (int cc = 0; cc < Q1; cc++) { int ll = PL[pp * Q1 + cc]; if (ll == M) continue; out[c++] = pp * Q1 + cc; } } }
    return c; }
/* all flags whose line zone contains line y (1464 of them) */
static int lnFlags(int y, int32_t *out) { int c = 0;
    for (int k = 0; k < Q1; k++) out[c++] = LP[y * Q1 + k] * Q1 + POS[y * Q1 + k];
    for (int k = 0; k < Q1; k++) { int x = LP[y * Q1 + k];
        for (int a = 0; a < Q1; a++) { int ll = PL[x * Q1 + a]; if (ll == y) continue;
            for (int d = 0; d < Q1; d++) { int pp = LP[ll * Q1 + d]; if (pp == x) continue; out[c++] = pp * Q1 + POS[ll * Q1 + d]; } } }
    return c; }

static int zpd[256], zld[256], zpf[256], zlf[256], zpS[256], zlS[256], zpE[256], zlE[256];

/* f leaves the free set: remove it from the list and withdraw its zone from the counters */
static void dropFree(int f) {
    freeF[f] = 0; int i = fPos[f]; int last = fList[--nFree]; fList[i] = last; fPos[last] = i; fPos[f] = -1;
    int p = f / Q1, l = PL[p * Q1 + f % Q1];
    zoneP(p, l, zpd); for (int j = 0; j < ZN; j++) FP[zpd[j]]--;
    zoneL(p, l, zld); for (int j = 0; j < ZN; j++) FL[zld[j]]--;
}
/* place flag f: occupy its zones and block every free flag whose zones meet them */
static void placeFlag(int f) {
    int p = f / Q1, l = PL[p * Q1 + f % Q1];
    dropFree(f);
    zoneP(p, l, zpf); zoneL(p, l, zlf);
    for (int j = 0; j < ZN; j++) { occP[zpf[j]] = 1; occL[zlf[j]] = 1; }
    for (int j = 0; j < ZN; j++) { int n = ptFlags(zpf[j], enumBuf); for (int i = 0; i < n; i++) if (freeF[enumBuf[i]]) dropFree(enumBuf[i]); }
    for (int j = 0; j < ZN; j++) { int n = lnFlags(zlf[j], enumBuf); for (int i = 0; i < n; i++) if (freeF[enumBuf[i]]) dropFree(enumBuf[i]); }
}
static int proxyD(int f) { int p = f / Q1, l = PL[p * Q1 + f % Q1]; zoneP(p, l, zpS); zoneL(p, l, zlS); int s = 0;
    for (int j = 0; j < ZN; j++) s += (int)FP[zpS[j]] - 1 + (int)FL[zlS[j]] - 1; return s; }
static int exactD(int f) { int p = f / Q1, l = PL[p * Q1 + f % Q1]; curStamp++; int cnt = 0;
    zoneP(p, l, zpE); zoneL(p, l, zlE);
    for (int j = 0; j < ZN; j++) { int n = ptFlags(zpE[j], enumBuf); for (int i = 0; i < n; i++) { int g = enumBuf[i];
        if (g != f && freeF[g] && stamp[g] != curStamp) { stamp[g] = curStamp; cnt++; } } }
    for (int j = 0; j < ZN; j++) { int n = lnFlags(zlE[j], enumBuf); for (int i = 0; i < n; i++) { int g = enumBuf[i];
        if (g != f && freeF[g] && stamp[g] != curStamp) { stamp[g] = curStamp; cnt++; } } }
    return cnt; }

int main(int argc, char **argv) {
    if (argc < 4) { fprintf(stderr, "usage: c3_greedy GHFILE SEED OUTFLAGS\n"); return 2; }
    FILE *f = fopen(argv[1], "r"); if (!f || fscanf(f, "%d %d", &P, &q) != 2) return 2; Q1 = q + 1; ZN = q * q + 1;
    LP = malloc(sizeof(int32_t) * (size_t)P * Q1); PL = malloc(sizeof(int32_t) * (size_t)P * Q1); POS = malloc(sizeof(int32_t) * (size_t)P * Q1);
    for (size_t i = 0; i < (size_t)P * Q1; i++) if (fscanf(f, "%d", &LP[i]) != 1) return 2;
    fclose(f);
    { int *c = calloc(P, sizeof(int)); for (int l = 0; l < P; l++) for (int k = 0; k < Q1; k++) { int p = LP[l * Q1 + k];
        POS[l * Q1 + k] = c[p]; PL[p * Q1 + c[p]++] = l; } free(c); }
    rs ^= strtoull(argv[2], 0, 10) * 0x2545F4914F6CDD1DULL; if (!rs) rs = 1;
    int mode = getenv("MODE") ? atoi(getenv("MODE")) : 1;
    int sample = getenv("SAMPLE") ? atoi(getenv("SAMPLE")) : 0;
    int K = getenv("EXACT") ? atoi(getenv("EXACT")) : 0;
    NF = P * Q1;
    freeF = malloc(NF); fList = malloc(sizeof(int32_t) * NF); fPos = malloc(sizeof(int32_t) * NF); stamp = calloc(NF, sizeof(uint32_t));
    occP = calloc(P, 1); occL = calloc(P, 1); FP = calloc(P, 2); FL = calloc(P, 2);
    for (int i = 0; i < NF; i++) { freeF[i] = 1; fList[i] = i; fPos[i] = i; }
    nFree = NF;
    /* every point (and line) lies in exactly Q1 + Q1*q*q flag zones (ptFlags / lnFlags), so the counters start there */
    for (int x = 0; x < P; x++) { FP[x] = (uint16_t)(Q1 + Q1 * q * q); FL[x] = (uint16_t)(Q1 + Q1 * q * q); }
    if (getenv("CHECKINIT")) { long bad = 0; for (int x = 0; x < P; x += 97) {
        int n = ptFlags(x, enumBuf); int m = lnFlags(x, enumBuf); bad += (n != Q1 + Q1 * q * q) + (m != Q1 + Q1 * q * q); }
        fprintf(stderr, "CHECKINIT bad %ld\n", bad); }
    fprintf(stderr, "init: P=%d q=%d flags=%d FP=FL=%d\n", P, q, NF, Q1 + Q1 * q * q);

    int32_t *placed = malloc(sizeof(int32_t) * (size_t)P * 2); int np = 0;
    int32_t *tf = malloc(sizeof(int32_t) * (K + 1)), *td = malloc(sizeof(int32_t) * (K + 1));
    clock_t c0 = clock();
    while (nFree > 0) {
        int chosen = -1;
        if (mode == 0) chosen = fList[rndi(nFree)];
        else {
            int ns = sample > 0 ? sample : nFree; int nt = 0;
            int best = 1 << 30, bestF = -1, nties = 0;
            for (int s = 0; s < ns; s++) {
                int ff = sample > 0 ? fList[rndi(nFree)] : fList[s];
                int d = proxyD(ff);
                if (K > 0) {
                    if (nt < K || d < td[nt - 1]) {
                        int pos = nt < K ? nt++ : nt - 1;
                        while (pos > 0 && td[pos - 1] > d) { td[pos] = td[pos - 1]; tf[pos] = tf[pos - 1]; pos--; }
                        td[pos] = d; tf[pos] = ff;
                    }
                } else {
                    if (d < best) { best = d; bestF = ff; nties = 1; }
                    else if (d == best) { nties++; if (rndi(nties) == 0) bestF = ff; }
                }
            }
            if (K > 0) {
                int bestE = 1 << 30; nties = 0;
                for (int i = 0; i < nt; i++) { int e = exactD(tf[i]);
                    if (e < bestE) { bestE = e; bestF = tf[i]; nties = 1; }
                    else if (e == bestE) { nties++; if (rndi(nties) == 0) bestF = tf[i]; } }
                best = bestE;
            }
            chosen = bestF;
        }
        if (chosen < 0) break;
        placeFlag(chosen);
        placed[2 * np] = chosen / Q1; placed[2 * np + 1] = PL[(chosen / Q1) * Q1 + chosen % Q1]; np++;
        if (np % 20 == 0) fprintf(stderr, "step %d free %d (%.1fs)\n", np, nFree, (double)(clock() - c0) / CLOCKS_PER_SEC);
    }
    /* independent re-check of the placed set: occupancy must hold each zone element once */
    { static uint8_t *cp, *cl; cp = calloc(P, 1); cl = calloc(P, 1); long bad = 0;
      for (int i = 0; i < np; i++) { int p = placed[2 * i], l = placed[2 * i + 1]; zoneP(p, l, zpE); zoneL(p, l, zlE);
        for (int j = 0; j < ZN; j++) { if (cp[zpE[j]]++) bad++; if (cl[zlE[j]]++) bad++; } }
      fprintf(stderr, "placed %d flags, zone collisions %ld\n", np, bad); }
    f = fopen(argv[3], "w"); if (!f) return 2;
    for (int i = 0; i < np; i++) fprintf(f, "%d %d\n", placed[2 * i], placed[2 * i + 1]);
    fclose(f);
    printf("placed %d\n", np);
    return 0;
}
