/* cwlocal.c: clause-weighting variant of domlocal.c (polylev squad r1, card c01).
   Usage: cwlocal HEXBIN lines|points k s SEED SECONDS OUT [bal|-] [SMOOTH]
   Same ball/colour model, start colouring, focused move and output as domlocal. Differences:
   - every pair (y,c), y an element and c a colour that misses ball B_s(y), has weight w[y*K+c] starting at 1;
     the weighted delta of a move is the weight of the pairs it makes missing minus the weight of those it covers;
   - local minimum: when no candidate of the focused neighbourhood (one element of the ball of a random incomplete
     element y, recoloured to a missing colour c of y) has a negative weighted delta, the weight of every currently
     missing pair is raised by 1 (breakout / clause weighting); the focused move is taken anyway;
   - SMOOTH > 0: every SMOOTH weight increases, all weights above 1 are lowered by 1 (back toward 1);
   - cost, best, aspiration and the stop test use the unweighted number of missing pairs, as in domlocal.
   The missing pairs and the incomplete elements are kept in lists, so bumps and the focused choice are O(size).
   Compile: gcc -O2 -o cwlocal cwlocal.c */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#include <limits.h>
/* the time budget is wall-clock seconds (the 4 cores are shared by ~16 cards, so CPU time runs far slower than wall time) */
static double wall(void) { struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts); return ts.tv_sec + ts.tv_nsec * 1e-9; }

static int q, N, Q1, K, S, BS;
static int *LP, *PL, *ballv, *col;
static uint16_t *cnt;
static int32_t *w;                       /* pair weights, id = y*K + c */
static int *missn; static long cost;     /* unweighted number of missing pairs */
static int *mlist, *mpos, nm = 0;        /* list of missing pair ids */
static int *yl, *ypos, nyl = 0;          /* list of elements with at least one missing colour */
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

/* pair (z,c) becomes missing / covered: maintains cost and the two lists */
static void pair_missing(int z, int c) {
    int id = z * K + c;
    missn[z]++; cost++;
    mpos[id] = nm; mlist[nm++] = id;
    if (missn[z] == 1) { ypos[z] = nyl; yl[nyl++] = z; }
}
static void pair_covered(int z, int c) {
    int id = z * K + c;
    missn[z]--; cost--;
    int i = mpos[id], last = mlist[--nm];
    mlist[i] = last; mpos[last] = i; mpos[id] = -1;
    if (missn[z] == 0) { int i2 = ypos[z], lz = yl[--nyl]; yl[i2] = lz; ypos[lz] = i2; ypos[z] = -1; }
}

/* recolour element X from colour `from` to colour `to` (-1 = uncoloured) */
static void recolour(int X, int from, int to) {
    for (int u = 0; u < BS; u++) { int z = ballv[(size_t)X * BS + u];
        if (from >= 0 && --cnt[(size_t)z * K + from] == 0) pair_missing(z, from);
        if (to >= 0 && cnt[(size_t)z * K + to]++ == 0) pair_covered(z, to); }
    col[X] = to;
}

/* weighted delta dw and unweighted delta du of x: a -> c, and (if xp >= 0, balanced mode) xp: c -> a, sequentially */
static void delta(int x, int a, int c, int xp, long *dw, long *du) {
    long W = 0, U = 0; const int *bx_ = ballv + (size_t)x * BS;
    for (int u = 0; u < BS; u++) { int z = bx_[u];
        if (a >= 0 && cnt[(size_t)z * K + a] == 1) { W += w[(size_t)z * K + a]; U++; }
        if (cnt[(size_t)z * K + c] == 0) { W -= w[(size_t)z * K + c]; U--; } }
    if (xp >= 0) {
        for (int u = 0; u < BS; u++) { int z = bx_[u]; if (a >= 0) cnt[(size_t)z * K + a]--; cnt[(size_t)z * K + c]++; }
        const int *bp_ = ballv + (size_t)xp * BS;
        for (int u = 0; u < BS; u++) { int z = bp_[u];
            if (cnt[(size_t)z * K + c] == 1) { W += w[(size_t)z * K + c]; U++; }
            if (a >= 0 && cnt[(size_t)z * K + a] == 0) { W -= w[(size_t)z * K + a]; U--; } }
        for (int u = 0; u < BS; u++) { int z = bx_[u]; if (a >= 0) cnt[(size_t)z * K + a]++; cnt[(size_t)z * K + c]--; }
    }
    *dw = W; *du = U;
}

static long recount(void) {
    memset(cnt, 0, sizeof(uint16_t) * (size_t)N * K);
    for (int y = 0; y < N; y++) for (int t = 0; t < BS; t++) { int a = col[ballv[(size_t)y * BS + t]]; if (a >= 0) cnt[(size_t)y * K + a]++; }
    long m = 0; for (size_t i = 0; i < (size_t)N * K; i++) if (!cnt[i]) m++;
    return m;
}

int main(int argc, char **argv) {
    if (argc < 8) { fprintf(stderr, "usage: cwlocal HEXBIN lines|points k s SEED SECONDS OUT [bal|-] [SMOOTH]\n"); return 1; }
    FILE *f = fopen(argv[1], "rb"); int32_t h[3]; if (!f || fread(h, 4, 3, f) != 3) return 1;
    q = h[0]; N = h[1]; Q1 = q + 1;
    LP = malloc(sizeof(int) * (size_t)N * Q1); if (fread(LP, 4, (size_t)N * Q1, f) != (size_t)N * Q1) return 1; fclose(f);
    PL = malloc(sizeof(int) * (size_t)N * Q1); int *c0 = calloc(N, sizeof(int));
    for (int l = 0; l < N; l++) for (int a = 0; a < Q1; a++) { int p = LP[l * Q1 + a]; PL[p * Q1 + c0[p]++] = l; }
    int lines = strcmp(argv[2], "lines") == 0; K = atoi(argv[3]); S = atoi(argv[4]);
    rs ^= (uint64_t)atoll(argv[5]) * 0x9E3779B97F4A7C15ULL; double secs = atof(argv[6]);
    long SMOOTH = argc > 9 ? atol(argv[9]) : 0;
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
    /* counts, weights (all 1), missing pair and incomplete element lists */
    cnt = calloc((size_t)N * K, sizeof(uint16_t)); missn = calloc(N, sizeof(int));
    for (int y = 0; y < N; y++) for (int t = 0; t < BS; t++) { int a = col[ballv[(size_t)y * BS + t]]; if (a >= 0) cnt[(size_t)y * K + a]++; }
    w = malloc(sizeof(int32_t) * (size_t)N * K); for (size_t i = 0; i < (size_t)N * K; i++) w[i] = 1;
    mlist = malloc(sizeof(int) * (size_t)N * K); mpos = malloc(sizeof(int) * (size_t)N * K);
    yl = malloc(sizeof(int) * N); ypos = malloc(sizeof(int) * N);
    cost = 0;
    for (int y = 0; y < N; y++) { ypos[y] = -1;
        for (int c = 0; c < K; c++) { int id = y * K + c; mpos[id] = -1;
            if (!cnt[id]) { missn[y]++; cost++; mpos[id] = nm; mlist[nm++] = id; } }
        if (missn[y]) { ypos[y] = nyl; yl[nyl++] = y; } }
    fprintf(stderr, "q=%d %s k=%d s=%d ball=%d initial cost %ld smooth=%ld\n", q, argv[2], K, S, BS, cost, SMOOTH);
    long best = cost, it = 0, bumps = 0, smooths = 0;
    int *bestc = malloc(sizeof(int) * N); memcpy(bestc, col, sizeof(int) * N);
    long *tabu = calloc((size_t)N, sizeof(long)); int *ml = malloc(sizeof(int) * K);
    double t0 = wall();
    while (cost > 0) {
        it++;
        if ((it & 255) == 0 && wall() - t0 > secs) break;
        int y = yl[rnd() % nyl];
        int nmc = 0; for (int c = 0; c < K; c++) if (!cnt[(size_t)y * K + c]) ml[nmc++] = c;
        int c = ml[rnd() % nmc];
        int noise = (rnd() % 100) < 2;
        long minall = LONG_MAX, bd = LONG_MAX; int bx = -1, bp = -1, ties = 0;
        for (int t = 0; t < BS; t++) {
            int x = ballv[(size_t)y * BS + t]; int a = col[x];
            if (a == c) continue;
            int xp = -1;
            if (bal) { int n_c = lstart[c + 1] - lstart[c]; xp = lst[lstart[c] + rnd() % n_c]; }
            long dw, du; delta(x, a, c, xp, &dw, &du);
            if (dw < minall) minall = dw;
            if (noise) { if (rnd() % (++ties) == 0) { bx = x; bp = xp; bd = dw; } continue; }
            if (tabu[x] > it && cost + du >= best) continue;
            if (dw < bd) { bd = dw; bx = x; bp = xp; ties = 1; } else if (dw == bd && rnd() % (++ties) == 0) { bx = x; bp = xp; }
        }
        if (bx < 0) continue;
        if (minall >= 0) {   /* local minimum of the weighted cost: raise the weight of every missing pair */
            for (int i = 0; i < nm; i++) w[mlist[i]]++;
            bumps++;
            if (SMOOTH > 0 && bumps % SMOOTH == 0) {
                for (size_t i = 0; i < (size_t)N * K; i++) if (w[i] > 1) w[i]--;
                smooths++;
            }
        }
        int a = col[bx];
        recolour(bx, a, c);
        if (bal) recolour(bp, c, a);
        if (bal) { /* swap list entries of bx and bp (they exchange colours) */
            int pb = lpos[bx], pp = lpos[bp]; lst[pb] = bp; lst[pp] = bx; lpos[bx] = pp; lpos[bp] = pb; }
        tabu[bx] = it + 5 + rnd() % 10; if (bal) tabu[bp] = it + 5 + rnd() % 10;
        if (cost < best) { best = cost; memcpy(bestc, col, sizeof(int) * N);
            if ((it & 4095) == 0 || best < 30) fprintf(stderr, "it %ld cost %ld (%.0fs)\n", it, cost, wall() - t0); }
    }
    long maxw = 0; for (size_t i = 0; i < (size_t)N * K; i++) if (w[i] > maxw) maxw = w[i];
    printf("q=%d %s k=%d s=%d best cost %ld (%ld iterations, %.0fs, bumps %ld, smooths %ld, max weight %ld)\n",
           q, argv[2], K, S, best, it, wall() - t0, bumps, smooths, maxw);
    if (best == 0) {
        memcpy(col, bestc, sizeof(int) * N);
        long chk = recount(); if (chk != 0) { printf("CHECK FAILED: %ld missing pairs\n", chk); return 1; }
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
