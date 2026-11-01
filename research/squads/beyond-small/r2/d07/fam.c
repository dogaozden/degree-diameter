/* d07 fam: structured hub family from one new A-controller vertex u* (fibre F4^4, 256 hubs).
 * Group g in 0..3 owns 4 B-fibres v[g][k] with invertible F4-matrices M[g][k] (columns col[0..3]).
 * Hub (g,w), w in W0 = {x : x3 = 0} (64 values), joins the 4 lines M[g][k](w + F4 e3) = {M w ^ scal(lam, col3)}
 * in fibres v[g][k]. Within a group the 64 hubs use distinct cosets in every fibre (disjoint); groups use distinct
 * fibres. Coverage (ball over A of radius 3), compatibility (d2 test, as in hubpack) and disjointness from the
 * existing A-hubs are checked; a max clique over the admissible hubs is found by randomized greedy.
 * usage: fam EDGES EXISTING_HUBS_OR_DASH OUT_PREFIX TRIALS SECS SEED
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#define H 16896
#define W 264
#define NHUB 256
static int MUL4[4][4] = {{0,0,0,0},{0,1,2,3},{0,2,3,1},{0,3,1,2}};
static int adjA[H][16], adjB[H][16];
static uint64_t *ball, *d2;
static unsigned long long rs = 88172645463325252ULL;
static inline unsigned rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return (unsigned)(rs >> 11); }
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }
static int scal(int l, int a) { int r = 0; for (int k = 0; k < 4; k++) r |= MUL4[l][(a >> (2 * k)) & 3] << (2 * k); return r; }
static int applyM(const int *col, int x) { int r = 0; for (int i = 0; i < 4; i++) r ^= scal((x >> (2 * i)) & 3, col[i]); return r; }

static int nex = 0, exN[1024][16];
static int N[NHUB][16];
static int valid[NHUB], nvalid;
static int vid[NHUB];
static uint64_t R[NHUB][W];
static unsigned char C[NHUB][NHUB];

static int compat(int i, const int *Ni, const uint64_t *Ri) {   /* hubs i and Ni: disjoint and some d2 meeting */
    int meet = 0;
    for (int k = 0; k < 16; k++) { int t = Ni[k]; if ((Ri[t >> 6] >> (t & 63)) & 1) meet = 1; }
    return meet;
}

int main(int argc, char **argv) {
    if (argc < 7) { fprintf(stderr, "usage: fam EDGES EXISTING|- OUT_PREFIX TRIALS SECS SEED\n"); return 2; }
    int trials = atoi(argv[4]); double secs = atof(argv[5]);
    rs ^= (unsigned long long)atoll(argv[6]) * 0x9E3779B97F4A7C15ULL;
    FILE *f = fopen(argv[1], "r"); long n, u, v; if (fscanf(f, "%ld", &n) != 1 || n != 2 * H) return 3;
    static int da[H], db[H];
    while (fscanf(f, "%ld %ld", &u, &v) == 2) { if (u > v) { long t = u; u = v; v = t; } v -= H; adjA[u][da[u]++] = v; adjB[v][db[v]++] = u; }
    fclose(f);
    for (int i = 0; i < H; i++) if (da[i] != 16 || db[i] != 16) { fprintf(stderr, "not 16-regular\n"); return 3; }
    double t0 = now();
    ball = calloc((size_t)H * W, 8); d2 = calloc((size_t)H * W, 8);
    for (int t = 0; t < H; t++) {   /* T = B side: ball over A (radius 3), d2 over B (radius 2) */
        uint64_t *bl = ball + (size_t)t * W, *dd = d2 + (size_t)t * W;
        dd[t >> 6] |= 1ULL << (t & 63);
        for (int i = 0; i < 16; i++) { int s = adjB[t][i]; bl[s >> 6] |= 1ULL << (s & 63);
            for (int j = 0; j < 16; j++) { int t2 = adjA[s][j]; dd[t2 >> 6] |= 1ULL << (t2 & 63); } }
        for (int w = 0; w < W; w++) { uint64_t m = dd[w]; while (m) { int b = __builtin_ctzll(m); m &= m - 1; int t2 = w * 64 + b;
            for (int i = 0; i < 16; i++) { int s = adjB[t2][i]; bl[s >> 6] |= 1ULL << (s & 63); } } }
    }
    fprintf(stderr, "balls %.1fs\n", now() - t0);
    static int used[H];
    if (strcmp(argv[2], "-") != 0) {
        FILE *h = fopen(argv[2], "r"); char line[4096];
        while (fgets(line, sizeof line, h)) { char *p = line; int k = 0, val, off;
            while (sscanf(p, "%d%n", &val, &off) == 1) { p += off; exN[nex][k++] = val - H; }
            if (k) { for (int a = 0; a < k; a++) used[exN[nex][a]] = 1; nex++; } }
        fclose(h);
    }
    fprintf(stderr, "%d existing hubs\n", nex);
    /* free-line count per fibre (for choosing fibres) */
    int bestTotal = -1; int bestFib[16]; int bestM[16][4];
    int bestN[NHUB][16]; int bestSel[NHUB], bestNsel = 0; int nvalid_best = 0;
    long tr = 0;
    while (tr < trials && now() - t0 < secs) {
        tr++;
        int fib[16]; int used_f[66] = {0};
        for (int g = 0; g < 16; g++) { int c; do { c = rnd() % 66; } while (used_f[c]); used_f[c] = 1; fib[g] = c; }
        int M[16][4];
        for (int g = 0; g < 16; g++) {
            for (;;) { int ok = 1;
                for (int i = 0; i < 4; i++) M[g][i] = 1 + rnd() % 255;
                for (int x = 1; x < 256 && ok; x++) if (applyM(M[g], x) == 0) ok = 0;
                if (ok) break; }
        }
        /* hubs */
        for (int g = 0; g < 4; g++) for (int w = 0; w < 64; w++) {
            int h = g * 64 + w;
            for (int k = 0; k < 4; k++) { int gk = g * 4 + k; int base = applyM(M[gk], w), c3 = M[gk][3];
                for (int lam = 0; lam < 4; lam++) N[h][k * 4 + lam] = fib[gk] * 256 + (base ^ scal(lam, c3)); }
        }
        /* coverage + existing-disjointness */
        nvalid = 0; int mincov = 1 << 30; long sumcov = 0;
        for (int h = 0; h < NHUB; h++) {
            int ok = 1; for (int k = 0; k < 16 && ok; k++) if (used[N[h][k]]) ok = 0;
            if (ok) { uint64_t cov[W]; memset(cov, 0, sizeof cov);
                for (int k = 0; k < 16; k++) { uint64_t *b = ball + (size_t)N[h][k] * W; for (int w = 0; w < W; w++) cov[w] |= b[w]; }
                int unc = 0; for (int w = 0; w < W; w++) unc += __builtin_popcountll(~cov[w]);
                if (unc < mincov) mincov = unc; sumcov += unc;
                for (int w = 0; w < W && ok; w++) if (cov[w] != ~0ULL) ok = 0; }
            if (ok) for (int e = 0; e < nex && ok; e++) { /* compat with each existing hub: d2 meeting, disjoint */
                int dis = 1; for (int k = 0; k < 16 && dis; k++) for (int q = 0; q < 16; q++) if (N[h][k] == exN[e][q]) { dis = 0; break; }
                if (!dis) { ok = 0; break; }
                uint64_t Rt[W]; memset(Rt, 0, sizeof Rt);
                for (int q = 0; q < 16; q++) { uint64_t *dd = d2 + (size_t)exN[e][q] * W; for (int w = 0; w < W; w++) Rt[w] |= dd[w]; }
                if (!compat(h, N[h], Rt)) ok = 0; }
            if (ok) vid[nvalid++] = h;
        }
        if (tr <= 3) fprintf(stderr, "trial %ld: min uncovered %d mean %.1f valid %d\n", tr, mincov, sumcov / (double)NHUB, nvalid);
        if (nvalid == 0) continue;
        /* R sets and compatibility among valid hubs */
        for (int a = 0; a < nvalid; a++) { int h = vid[a]; memset(R[a], 0, sizeof R[a]);
            for (int k = 0; k < 16; k++) { uint64_t *dd = d2 + (size_t)N[h][k] * W; for (int w = 0; w < W; w++) R[a][w] |= dd[w]; } }
        for (int a = 0; a < nvalid; a++) for (int b = 0; b < nvalid; b++) C[a][b] = 0;
        for (int a = 0; a < nvalid; a++) for (int b = a + 1; b < nvalid; b++) {
            int hb = vid[b], dis = 1; for (int k = 0; k < 16 && dis; k++) for (int q = 0; q < 16; q++) if (N[vid[a]][k] == N[hb][q]) { dis = 0; break; }
            if (dis && compat(0, N[hb], R[a])) C[a][b] = C[b][a] = 1; }
        /* randomized greedy max clique over valid hubs */
        int best = 0, bestSet[NHUB];
        for (int rep = 0; rep < 300 && now() - t0 < secs; rep++) {
            int order[NHUB], in[NHUB] = {0}, cnt = 0, sel[NHUB];
            for (int a = 0; a < nvalid; a++) order[a] = a;
            for (int a = nvalid - 1; a > 0; a--) { int b = rnd() % (a + 1), t = order[a]; order[a] = order[b]; order[b] = t; }
            for (int ii = 0; ii < nvalid; ii++) { int a = order[ii]; int ok = 1;
                for (int s = 0; s < cnt && ok; s++) if (!C[a][sel[s]]) ok = 0;
                if (ok) sel[cnt++] = a; }
            if (cnt > best) { best = cnt; memcpy(bestSet, sel, sizeof(int) * cnt); }
        }
        int total = nex + best;
        if (total > bestTotal) {
            bestTotal = total; nvalid_best = nvalid; bestNsel = best;
            memcpy(bestFib, fib, sizeof fib); memcpy(bestM, M, sizeof M);
            for (int s = 0; s < best; s++) { memcpy(bestN[s], N[vid[bestSet[s]]], sizeof(int) * 16); bestSel[s] = vid[bestSet[s]]; }
            fprintf(stderr, "trial %ld: valid %d clique %d total %d (%.1fs)\n", tr, nvalid, best, total, now() - t0);
        }
    }
    printf("trials %ld best_total %d (existing %d + family %d) valid_best %d\n", tr, bestTotal, nex, bestNsel, nvalid_best);
    /* outputs: hub file with the family hubs (global B ids), parameters */
    char fn[512];
    snprintf(fn, sizeof fn, "%s_hubs.txt", argv[3]); FILE *o = fopen(fn, "w");
    for (int s = 0; s < bestNsel; s++) { for (int k = 0; k < 16; k++) fprintf(o, "%d ", bestN[s][k] + H); fprintf(o, "\n"); }
    fclose(o);
    snprintf(fn, sizeof fn, "%s_params.txt", argv[3]); o = fopen(fn, "w");
    for (int g = 0; g < 16; g++) fprintf(o, "group %d fibre %d cols %d %d %d %d\n", g / 4, bestFib[g], bestM[g][0], bestM[g][1], bestM[g][2], bestM[g][3]);
    fclose(o);
    return 0;
}
