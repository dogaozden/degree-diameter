/* orblocal.c: k disjoint dominating classes in the 2-ball hypergraph of H(q) that are unions of orbits of a
   collineation group T = <h> (classes constant on T-orbits).
   polylev job (Opus), 2026-10-28.

   Since h maps 2-balls to 2-balls and fixes every class, B2(x) meets every class iff B2(h x) does, so one ball per
   orbit suffices. Local search on the orbit colours (focused moves as in domlocal.c).
   Usage: orblocal HEXBIN PERM lines|points k SEED SECONDS OUT     (OUT: int32 colour per element) */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>

static int q, N, Q1, B, K, NO;
static int *LP, *PL, *perm, *orb, *rep;
static int *bo;             /* bo[b*B + t]: orbit of the t-th element of the ball of rep[b] */
static int *os, *ob;        /* occurrences of orbit o: ob[os[o]..os[o+1]) = balls (with multiplicity) */
static int *cnt, *missn, *col; static long cost;
static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }

int main(int argc, char **argv) {
    if (argc < 8) { fprintf(stderr, "usage\n"); return 1; }
    FILE *f = fopen(argv[1], "rb"); int32_t h[3]; if (!f || fread(h, 4, 3, f) != 3) return 1;
    q = h[0]; N = h[1]; Q1 = q + 1; B = q * q + q + 1;
    LP = malloc(sizeof(int) * (size_t)N * Q1); if (fread(LP, 4, (size_t)N * Q1, f) != (size_t)N * Q1) return 1; fclose(f);
    PL = malloc(sizeof(int) * (size_t)N * Q1); int *c0 = calloc(N, sizeof(int));
    for (int l = 0; l < N; l++) for (int a = 0; a < Q1; a++) { int p = LP[l * Q1 + a]; PL[p * Q1 + c0[p]++] = l; }
    perm = malloc(sizeof(int) * N); f = fopen(argv[2], "rb"); if (fread(perm, 4, N, f) != (size_t)N) return 1; fclose(f);
    int lines = strcmp(argv[3], "lines") == 0; K = atoi(argv[4]);
    rs ^= (uint64_t)atoll(argv[5]) * 0x9E3779B97F4A7C15ULL; double secs = atof(argv[6]);
    orb = malloc(sizeof(int) * N); rep = malloc(sizeof(int) * N); for (int i = 0; i < N; i++) orb[i] = -1;
    NO = 0;
    for (int x0 = 0; x0 < N; x0++) { if (orb[x0] >= 0) continue; int x = x0; while (orb[x] < 0) { orb[x] = NO; x = perm[x]; } rep[NO++] = x0; }
    bo = malloc(sizeof(int) * (size_t)NO * B); int *mark = calloc(N, sizeof(int)), stamp = 0;
    for (int b = 0; b < NO; b++) {
        int x = rep[b], c = 0; stamp++; mark[x] = stamp; bo[(size_t)b * B + c++] = orb[x];
        for (int a = 0; a < Q1; a++) { int m = lines ? LP[x * Q1 + a] : PL[x * Q1 + a];
            for (int e = 0; e < Q1; e++) { int y = lines ? PL[m * Q1 + e] : LP[m * Q1 + e]; if (mark[y] != stamp) { mark[y] = stamp; bo[(size_t)b * B + c++] = orb[y]; } } }
    }
    os = calloc(NO + 1, sizeof(int));
    for (size_t t = 0; t < (size_t)NO * B; t++) os[bo[t] + 1]++;
    for (int o = 0; o < NO; o++) os[o + 1] += os[o];
    ob = malloc(sizeof(int) * (size_t)NO * B); int *fill = calloc(NO, sizeof(int));
    for (int b = 0; b < NO; b++) for (int t = 0; t < B; t++) { int o = bo[(size_t)b * B + t]; ob[os[o] + fill[o]++] = b; }
    col = malloc(sizeof(int) * NO); for (int o = 0; o < NO; o++) col[o] = rnd() % K;
    cnt = calloc((size_t)NO * K, sizeof(int)); missn = calloc(NO, sizeof(int));
    for (int b = 0; b < NO; b++) for (int t = 0; t < B; t++) cnt[(size_t)b * K + col[bo[(size_t)b * B + t]]]++;
    cost = 0; for (int b = 0; b < NO; b++) { for (int c = 0; c < K; c++) if (!cnt[(size_t)b * K + c]) missn[b]++; cost += missn[b]; }
    fprintf(stderr, "q=%d %s k=%d: %d orbits, initial cost %ld\n", q, argv[3], K, NO, cost);
    long best = cost, it = 0; int *bestc = malloc(sizeof(int) * NO); memcpy(bestc, col, sizeof(int) * NO);
    long *tabu = calloc(NO, sizeof(long)); int *ml = malloc(sizeof(int) * K);
    clock_t t0 = clock();
    while (cost > 0) {
        it++;
        if ((it & 1023) == 0 && (double)(clock() - t0) / CLOCKS_PER_SEC > secs) break;
        int b; do b = (int)(rnd() % NO); while (!missn[b]);
        int nm = 0; for (int c = 0; c < K; c++) if (!cnt[(size_t)b * K + c]) ml[nm++] = c;
        int c = ml[rnd() % nm], noise = (rnd() % 100) < 2;
        long bd = 1L << 40; int bx = -1, ties = 0;
        for (int t = 0; t < B; t++) {
            int o = bo[(size_t)b * B + t], a = col[o]; long d = 0;
            /* moving orbit o from a to c: per occurrence ball (with multiplicity) */
            for (int u = os[o]; u < os[o + 1]; u++) { int z = ob[u]; cnt[(size_t)z * K + a]--; if (cnt[(size_t)z * K + a] == 0) d++; if (cnt[(size_t)z * K + c]++ == 0) d--; }
            for (int u = os[o]; u < os[o + 1]; u++) { int z = ob[u]; cnt[(size_t)z * K + a]++; cnt[(size_t)z * K + c]--; }
            if (noise) { if (rnd() % (++ties) == 0) { bx = o; bd = d; } continue; }
            if (tabu[o] > it && cost + d >= best) continue;
            if (d < bd) { bd = d; bx = o; ties = 1; } else if (d == bd && rnd() % (++ties) == 0) bx = o;
        }
        if (bx < 0) continue;
        int a = col[bx];
        for (int u = os[bx]; u < os[bx + 1]; u++) { int z = ob[u];
            if (--cnt[(size_t)z * K + a] == 0) { missn[z]++; cost++; }
            if (cnt[(size_t)z * K + c]++ == 0) { missn[z]--; cost--; } }
        col[bx] = c; tabu[bx] = it + 3 + rnd() % 8;
        if (cost < best) { best = cost; memcpy(bestc, col, sizeof(int) * NO);
            if ((it & 8191) == 0 || best < 20) fprintf(stderr, "it %ld cost %ld (%.0fs)\n", it, cost, (double)(clock() - t0) / CLOCKS_PER_SEC); }
    }
    printf("q=%d %s k=%d orbits=%d best cost %ld (%ld iterations, %.0fs)\n", q, argv[3], K, NO, best, it, (double)(clock() - t0) / CLOCKS_PER_SEC);
    if (best == 0) { int *ce = malloc(sizeof(int) * N); for (int x = 0; x < N; x++) ce[x] = bestc[orb[x]];
        f = fopen(argv[7], "wb"); fwrite(ce, 4, N, f); fclose(f); }
    return 0;
}
