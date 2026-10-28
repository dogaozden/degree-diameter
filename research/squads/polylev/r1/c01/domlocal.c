/* domlocal.c: k disjoint dominating classes in the s-ball hypergraph of H(q) (points or lines), by local search.
   polylev job (Opus), 2026-10-28.

   Every element gets a colour in 0..k-1. Cost = sum over elements y of the number of colours missing from the ball
   B_s(y) (elements of the same type at distance <= s, s = 2 or 4). Focused moves: a random ball with a missing colour
   c, recolour one of its elements to c (best non-tabu; 2% random). When cost 0 is reached the classes are pruned: an
   element is uncoloured (-1) when every ball containing it still sees its colour (greedy, random order), so that the
   classes are close to minimal and point and line classes can be balanced (domcheck.py).
   Usage: domlocal HEXBIN lines|points k s SEED SECONDS OUT [bal]   (OUT: int32 colour per element, -1 = free)
   bal: every colour class has exactly floor(N/k) elements, the rest are free (-1); moves are swaps (x to c,
   a random element x' of colour c to x's old colour), so point and line classes have equal sizes. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
/* card c01: the time budget is wall-clock seconds (shared machine), otherwise this file is the original */
static double wall(void) { struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts); return ts.tv_sec + ts.tv_nsec * 1e-9; }

static int q, N, Q1, K, S, BS;
static int *LP, *PL, *ballv, *col;
static uint16_t *cnt;
static int *missn; static long cost;
static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }

static int nbr(int x, int lines, int a) { return lines ? LP[x * Q1 + a] : PL[x * Q1 + a]; }       /* other type */
static int nbr2(int m, int lines, int b) { return lines ? PL[m * Q1 + b] : LP[m * Q1 + b]; }     /* back */

static void make_ball(int x, int lines, int *out) {
    static int *mark = NULL, stamp = 0; if (!mark) mark = calloc(N, sizeof(int));
    stamp++; int c = 0; out[c++] = x; mark[x] = stamp;
    int lo = 0;
    for (int r = 0; r < S / 2; r++) {
        int hi = c;
        for (int i = lo; i < hi; i++) for (int a = 0; a < Q1; a++) { int m = nbr(out[i], lines, a);
            for (int b = 0; b < Q1; b++) { int y = nbr2(m, lines, b); if (mark[y] != stamp) { mark[y] = stamp; out[c++] = y; } } }
        lo = hi;
    }
    if (c != BS) { fprintf(stderr, "ball size %d != %d\n", c, BS); exit(1); }
}

int main(int argc, char **argv) {
    if (argc < 8) { fprintf(stderr, "usage\n"); return 1; }
    FILE *f = fopen(argv[1], "rb"); int32_t h[3]; if (!f || fread(h, 4, 3, f) != 3) return 1;
    q = h[0]; N = h[1]; Q1 = q + 1;
    LP = malloc(sizeof(int) * (size_t)N * Q1); if (fread(LP, 4, (size_t)N * Q1, f) != (size_t)N * Q1) return 1; fclose(f);
    PL = malloc(sizeof(int) * (size_t)N * Q1); int *c0 = calloc(N, sizeof(int));
    for (int l = 0; l < N; l++) for (int a = 0; a < Q1; a++) { int p = LP[l * Q1 + a]; PL[p * Q1 + c0[p]++] = l; }
    int lines = strcmp(argv[2], "lines") == 0; K = atoi(argv[3]); S = atoi(argv[4]);
    rs ^= (uint64_t)atoll(argv[5]) * 0x9E3779B97F4A7C15ULL; double secs = atof(argv[6]);
    BS = (S == 2) ? q * q + q + 1 : 1 + q * (q + 1) + q * q * q * (q + 1);
    ballv = malloc(sizeof(int) * (size_t)N * BS);
    for (int x = 0; x < N; x++) make_ball(x, lines, ballv + (size_t)x * BS);
    int bal = argc > 8 && strcmp(argv[8], "bal") == 0, T = N / K;
    col = malloc(sizeof(int) * N);
    if (!bal) for (int x = 0; x < N; x++) col[x] = rnd() % K;
    else { int *ord = malloc(sizeof(int) * N); for (int i = 0; i < N; i++) ord[i] = i;
        for (int i = N - 1; i > 0; i--) { int j = rnd() % (i + 1), t = ord[i]; ord[i] = ord[j]; ord[j] = t; }
        for (int i = 0; i < N; i++) col[ord[i]] = i < T * K ? i % K : -1; free(ord); }
    /* per-colour element lists (colour -1 stored at index K) */
    int *lst = malloc(sizeof(int) * N), *lpos = malloc(sizeof(int) * N), *lstart = calloc(K + 2, sizeof(int)), *lfill = calloc(K + 1, sizeof(int));
    for (int x = 0; x < N; x++) lstart[(col[x] < 0 ? K : col[x]) + 1]++;
    for (int c = 0; c <= K; c++) lstart[c + 1] += lstart[c];
    for (int x = 0; x < N; x++) { int c = col[x] < 0 ? K : col[x]; lpos[x] = lstart[c] + lfill[c]++; lst[lpos[x]] = x; }
    cnt = calloc((size_t)N * K, sizeof(uint16_t)); missn = calloc(N, sizeof(int));
    for (int y = 0; y < N; y++) for (int t = 0; t < BS; t++) { int a = col[ballv[(size_t)y * BS + t]]; if (a >= 0) cnt[(size_t)y * K + a]++; }
    cost = 0; for (int y = 0; y < N; y++) { for (int c = 0; c < K; c++) if (!cnt[(size_t)y * K + c]) missn[y]++; cost += missn[y]; }
    fprintf(stderr, "q=%d %s k=%d s=%d ball=%d initial cost %ld\n", q, argv[2], K, S, BS, cost);
    long best = cost, it = 0; int *bestc = malloc(sizeof(int) * N); memcpy(bestc, col, sizeof(int) * N);
    long *tabu = calloc((size_t)N, sizeof(long)); int *ml = malloc(sizeof(int) * K);
    /* list of balls with missing colours, maintained lazily by sampling */
    double t0 = wall();
    while (cost > 0) {
        it++;
        if ((it & 255) == 0 && wall() - t0 > secs) break;
        int y; do y = (int)(rnd() % N); while (!missn[y]);
        int nm = 0; for (int c = 0; c < K; c++) if (!cnt[(size_t)y * K + c]) ml[nm++] = c;
        int c = ml[rnd() % nm];
        int noise = (rnd() % 100) < 2;
        long bd = 1L << 40; int bx = -1, bp = -1, ties = 0;
        for (int t = 0; t < BS; t++) {
            int x = ballv[(size_t)y * BS + t]; int a = col[x];
            if (a == c) continue;
            int xp = -1;
            if (bal) { int n_c = lstart[c + 1] - lstart[c]; xp = lst[lstart[c] + rnd() % n_c]; }
            /* delta of x: a -> c, then x': c -> a (sequentially, with temporary updates) */
            long d = 0;
            for (int u = 0; u < BS; u++) { int z = ballv[(size_t)x * BS + u];
                if (a >= 0 && cnt[(size_t)z * K + a] == 1) d++;
                if (cnt[(size_t)z * K + c] == 0) d--; }
            if (bal) {
                for (int u = 0; u < BS; u++) { int z = ballv[(size_t)x * BS + u]; if (a >= 0) cnt[(size_t)z * K + a]--; cnt[(size_t)z * K + c]++; }
                for (int u = 0; u < BS; u++) { int z = ballv[(size_t)xp * BS + u];
                    if (cnt[(size_t)z * K + c] == 1) d++;
                    if (a >= 0 && cnt[(size_t)z * K + a] == 0) d--; }
                for (int u = 0; u < BS; u++) { int z = ballv[(size_t)x * BS + u]; if (a >= 0) cnt[(size_t)z * K + a]++; cnt[(size_t)z * K + c]--; }
            }
            if (noise) { if (rnd() % (++ties) == 0) { bx = x; bp = xp; bd = d; } continue; }
            if (tabu[x] > it && cost + d >= best) continue;
            if (d < bd) { bd = d; bx = x; bp = xp; ties = 1; } else if (d == bd && rnd() % (++ties) == 0) { bx = x; bp = xp; }
        }
        if (bx < 0) continue;
        int a = col[bx];
        /* recolour helper */
        #define RECOLOUR(X, FROM, TO) do { int X_ = (X); \
            for (int u = 0; u < BS; u++) { int z = ballv[(size_t)X_ * BS + u]; \
                if ((FROM) >= 0 && --cnt[(size_t)z * K + (FROM)] == 0) { missn[z]++; cost++; } \
                if ((TO) >= 0 && cnt[(size_t)z * K + (TO)]++ == 0) { missn[z]--; cost--; } } \
            int fi = (FROM) < 0 ? K : (FROM), ti = (TO) < 0 ? K : (TO); \
            /* move X_ from list fi to list ti: swap with the last of fi, shift boundaries */ \
            (void)fi; (void)ti; col[X_] = (TO); } while (0)
        RECOLOUR(bx, a, c);
        if (bal) RECOLOUR(bp, c, a);
        if (bal) { /* swap list entries of bx and bp (they exchange colours) */
            int pb = lpos[bx], pp = lpos[bp]; lst[pb] = bp; lst[pp] = bx; lpos[bx] = pp; lpos[bp] = pb; }
        tabu[bx] = it + 5 + rnd() % 10; if (bal) tabu[bp] = it + 5 + rnd() % 10;
        if (cost < best) { best = cost; memcpy(bestc, col, sizeof(int) * N);
            if ((it & 4095) == 0 || best < 30) fprintf(stderr, "it %ld cost %ld (%.0fs)\n", it, cost, wall() - t0); }
    }
    printf("q=%d %s k=%d s=%d best cost %ld (%ld iterations, %.0fs)\n", q, argv[2], K, S, best, it, wall() - t0);
    if (best == 0) {
        memcpy(col, bestc, sizeof(int) * N);
        memset(cnt, 0, sizeof(uint16_t) * (size_t)N * K);
        for (int y = 0; y < N; y++) for (int t = 0; t < BS; t++) { int a = col[ballv[(size_t)y * BS + t]]; if (a >= 0) cnt[(size_t)y * K + a]++; }
        int *ord = malloc(sizeof(int) * N); for (int i = 0; i < N; i++) ord[i] = i;
        for (int i = N - 1; i > 0; i--) { int j = rnd() % (i + 1), t = ord[i]; ord[i] = ord[j]; ord[j] = t; }
        int freed = 0;
        for (int i = 0; i < N && !bal; i++) { int x = ord[i], a = col[x], ok = 1; if (a < 0) continue;
            for (int u = 0; u < BS && ok; u++) if (cnt[(size_t)ballv[(size_t)x * BS + u] * K + a] < 2) ok = 0;
            if (ok) { for (int u = 0; u < BS; u++) cnt[(size_t)ballv[(size_t)x * BS + u] * K + a]--; col[x] = -1; freed++; } }
        printf("%s: %d elements free, %d coloured (%.1f per colour)\n", bal ? "balanced" : "pruned", bal ? N - T * K : freed, bal ? T * K : N - freed, bal ? (double)T : (double)(N - freed) / K);
        f = fopen(argv[7], "wb"); fwrite(col, 4, N, f); fclose(f);
    }
    return 0;
}
