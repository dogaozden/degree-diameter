/* translocal.c: local search for a T-equivariant dominating colouring (same problem as transsat.py).
   polylev job (Opus), 2026-10-28.

   T = <h> semiregular of order k on the points (or lines) of H(q). Orbit O has representative b_O; the element
   h^j b_O gets colour j + s_O (mod k). Cost = sum over orbit representatives x of the number of colours missing
   from the 2-ball B2(x) (it is the same for every element of the orbit). Tabu search on the s_O: each step moves the
   orbit/value pair with the best cost change among the orbits that touch an incomplete ball, with a tabu tenure.
   Usage: translocal HEXBIN PERM lines|points SEED SECONDS OUT [A] [fixed]
   fixed: the number of orbits in each block is kept equal (orbit o starts in block o mod A; blocks change only by
   swapping the blocks of two orbits), so every colour class has exactly (orbits)/A elements; colourings of points
   and lines found this way have equal class sizes (needed by the lift).
   With A > 1 blocks: k = A*d colours (d = |T|); orbit O gets a block a_O and a shift s_O, h^j b_O has colour
   a_O*d + (j + s_O mod d), so T permutes the colours of each block cyclically (classes are T-translates within a block).
   Writes OUT (int32 colour per element) when cost 0 is reached; prints the best cost. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>

static int q, N, Q1, B, K, NO;
static int *LP, *PL, *perm, *orb, *idx, *rep;
static int *ball;               /* ball[o*B + t]: elements of the 2-ball of rep[o] */
static int *occ_start, *occ_b, *occ_j;   /* occurrences of orbit O in rep balls: (ball, idx of the element) */
static int *cnt;                /* cnt[b*K + c] */
static int *s;                  /* s[O] = a_O*D + shift */
static int D, A;               /* group order, blocks; K = A*D colours */
static int *miss;               /* miss[b] = number of colours with cnt 0 */
static long cost;
static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }

static void build_ball(int x, int lines, int *out) {
    static int *mark = NULL; static int stamp = 0;
    if (!mark) mark = calloc(N, sizeof(int));
    stamp++; int c = 0; out[c++] = x; mark[x] = stamp;
    for (int a = 0; a < Q1; a++) {
        int m = lines ? LP[x * Q1 + a] : PL[x * Q1 + a];
        for (int b = 0; b < Q1; b++) { int y = lines ? PL[m * Q1 + b] : LP[m * Q1 + b]; if (mark[y] != stamp) { mark[y] = stamp; out[c++] = y; } }
    }
}

#define COLOR(j, v) (((v) / D) * D + ((j) + (v)) % D)
static long delta_of(int o, int v) {   /* cost change of setting s[o] = v */
    if (v == s[o]) return 0;
    long dc = 0;
    /* apply then revert */
    for (int t = occ_start[o]; t < occ_start[o + 1]; t++) {
        int b = occ_b[t], c0 = COLOR(occ_j[t], s[o]), c1 = COLOR(occ_j[t], v);
        if (--cnt[b * K + c0] == 0) dc++;
        if (cnt[b * K + c1]++ == 0) dc--;
    }
    for (int t = occ_start[o]; t < occ_start[o + 1]; t++) {
        int b = occ_b[t], c0 = COLOR(occ_j[t], s[o]), c1 = COLOR(occ_j[t], v);
        cnt[b * K + c1]--; cnt[b * K + c0]++;
    }
    return dc;
}
static void apply(int o, int v) {
    for (int t = occ_start[o]; t < occ_start[o + 1]; t++) {
        int b = occ_b[t], c0 = COLOR(occ_j[t], s[o]), c1 = COLOR(occ_j[t], v);
        if (--cnt[b * K + c0] == 0) { miss[b]++; cost++; }
        if (cnt[b * K + c1]++ == 0) { miss[b]--; cost--; }
    }
    s[o] = v;
}

int main(int argc, char **argv) {
    if (argc < 7) { fprintf(stderr, "usage\n"); return 1; }
    FILE *f = fopen(argv[1], "rb"); int32_t h[3]; if (!f || fread(h, 4, 3, f) != 3) return 1;
    q = h[0]; N = h[1]; Q1 = q + 1; B = q * q + q + 1;
    LP = malloc(sizeof(int) * (size_t)N * Q1); if (fread(LP, 4, (size_t)N * Q1, f) != (size_t)N * Q1) return 1; fclose(f);
    PL = malloc(sizeof(int) * (size_t)N * Q1); int *c0 = calloc(N, sizeof(int));
    for (int l = 0; l < N; l++) for (int a = 0; a < Q1; a++) { int p = LP[l * Q1 + a]; PL[p * Q1 + c0[p]++] = l; }
    perm = malloc(sizeof(int) * N); f = fopen(argv[2], "rb"); if (fread(perm, 4, N, f) != (size_t)N) return 1; fclose(f);
    int lines = strcmp(argv[3], "lines") == 0; rs ^= (uint64_t)atoll(argv[4]) * 0x9E3779B97F4A7C15ULL; double secs = atof(argv[5]);
    orb = malloc(sizeof(int) * N); idx = malloc(sizeof(int) * N); rep = malloc(sizeof(int) * N);
    for (int i = 0; i < N; i++) orb[i] = -1;
    NO = 0; K = 0;
    for (int x0 = 0; x0 < N; x0++) {
        if (orb[x0] >= 0) continue;
        int x = x0, j = 0; while (orb[x] < 0) { orb[x] = NO; idx[x] = j++; x = perm[x]; }
        rep[NO++] = x0; K = j;
    }
    D = K; A = argc > 7 ? atoi(argv[7]) : 1; K = A * D; int fixedb = argc > 8 && strcmp(argv[8], "fixed") == 0;

    ball = malloc(sizeof(int) * (size_t)NO * B);
    for (int o = 0; o < NO; o++) build_ball(rep[o], lines, ball + (size_t)o * B);
    occ_start = calloc(NO + 1, sizeof(int));
    for (int b = 0; b < NO; b++) for (int t = 0; t < B; t++) occ_start[orb[ball[(size_t)b * B + t]] + 1]++;
    for (int o = 0; o < NO; o++) occ_start[o + 1] += occ_start[o];
    occ_b = malloc(sizeof(int) * (size_t)NO * B); occ_j = malloc(sizeof(int) * (size_t)NO * B); int *fill = calloc(NO, sizeof(int));
    for (int b = 0; b < NO; b++) for (int t = 0; t < B; t++) { int x = ball[(size_t)b * B + t], o = orb[x]; int p = occ_start[o] + fill[o]++; occ_b[p] = b; occ_j[p] = idx[x]; }
    cnt = calloc((size_t)NO * K, sizeof(int)); miss = calloc(NO, sizeof(int)); s = calloc(NO, sizeof(int));
    for (int o = 0; o < NO; o++) s[o] = fixedb ? (o % A) * D + rnd() % D : rnd() % K;
    if (getenv("GREEDY")) {   /* greedy start: orbits in random order, each takes the value covering most missing pairs */
        int *tc = calloc((size_t)NO * K, sizeof(int)), *cap = calloc(A, sizeof(int)), *used = calloc(A, sizeof(int));
        for (int o = 0; o < NO; o++) cap[o % A]++;
        int *ord = malloc(sizeof(int) * NO); for (int i = 0; i < NO; i++) ord[i] = i;
        for (int i = NO - 1; i > 0; i--) { int j = rnd() % (i + 1), t = ord[i]; ord[i] = ord[j]; ord[j] = t; }
        for (int ii = 0; ii < NO; ii++) {
            int o = ord[ii], bv = -1, bg = -1, ties = 0;
            for (int v = 0; v < K; v++) {
                if (fixedb && used[v / D] >= cap[v / D]) continue;
                int g = 0;
                for (int t = occ_start[o]; t < occ_start[o + 1]; t++) if (!tc[(size_t)occ_b[t] * K + COLOR(occ_j[t], v)]) g++;
                if (g > bg) { bg = g; bv = v; ties = 1; } else if (g == bg && rnd() % (++ties) == 0) bv = v;
            }
            s[o] = bv; used[bv / D]++;
            for (int t = occ_start[o]; t < occ_start[o + 1]; t++) tc[(size_t)occ_b[t] * K + COLOR(occ_j[t], bv)]++;
        }
        free(tc); free(cap); free(used); free(ord);
    }
    int *blist = malloc(sizeof(int) * NO), *bpos = malloc(sizeof(int) * NO), *bst = calloc(A + 1, sizeof(int));
    for (int o = 0; o < NO; o++) bst[o % A + 1]++;
    for (int a = 0; a < A; a++) bst[a + 1] += bst[a];
    if (fixedb) { int *fl = calloc(A, sizeof(int)); for (int o = 0; o < NO; o++) { int a = s[o] / D; bpos[o] = bst[a] + fl[a]++; blist[bpos[o]] = o; } }
    for (int o = 0; o < NO; o++) for (int t = occ_start[o]; t < occ_start[o + 1]; t++) cnt[occ_b[t] * K + COLOR(occ_j[t], s[o])]++;
    cost = 0; for (int b = 0; b < NO; b++) { for (int c = 0; c < K; c++) if (!cnt[b * K + c]) miss[b]++; cost += miss[b]; }
    fprintf(stderr, "q=%d %s k=%d orbits=%d ball=%d initial cost %ld\n", q, argv[3], K, NO, B, cost);
    long best = cost; int *bests = malloc(sizeof(int) * NO); memcpy(bests, s, sizeof(int) * NO);
    long *tabu = calloc((size_t)NO * K, sizeof(long)); long it = 0;
    clock_t t0 = clock();
    int *cand = malloc(sizeof(int) * NO);
    int *missl = malloc(sizeof(int) * K);
    while (cost > 0) {
        it++;
        if ((it & 255) == 0 && (double)(clock() - t0) / CLOCKS_PER_SEC > secs) break;
        /* focused move: a random incomplete ball b and one of its missing colours c; every element x of b can be
           given colour c by setting s[orb x] = c - idx[x]; take the best non-tabu one (noise: random one) */
        int b; do b = (int)(rnd() % NO); while (!miss[b]);
        int nm = 0; for (int c = 0; c < K; c++) if (!cnt[b * K + c]) missl[nm++] = c;
        int c = missl[rnd() % nm];
        long bd = 1L << 40; int bo = -1, bv = -1, bo2 = -1, ties = 0;
        int noise = (rnd() % 100) < 3;
        for (int t = 0; t < B; t++) {
            int x = ball[(size_t)b * B + t], o = orb[x], v = (c / D) * D + (((c % D) - idx[x]) % D + D) % D;
            if (v == s[o]) continue;
            long d; int o2 = -1;
            if (fixedb && v / D != s[o] / D) {          /* swap blocks with a random orbit of block v/D */
                { int a2 = v / D; o2 = blist[bst[a2] + rnd() % (bst[a2 + 1] - bst[a2])]; } if (o2 == o) continue;
                int so = s[o], s2 = s[o2]; long c0 = cost;
                apply(o, v); apply(o2, (so / D) * D + s2 % D); d = cost - c0; apply(o2, s2); apply(o, so);
            } else d = delta_of(o, v);
            if (noise) { if (rnd() % (++ties) == 0) { bo = o; bv = v; bd = d; bo2 = o2; } continue; }
            if (tabu[(size_t)o * K + v] > it && cost + d >= best) continue;
            if (d < bd) { bd = d; bo = o; bv = v; bo2 = o2; ties = 1; }
            else if (d == bd && rnd() % (++ties) == 0) { bo = o; bv = v; bo2 = o2; }
        }
        if (bo < 0) continue;
        int old = s[bo];
        if (bo2 >= 0) { int s2 = s[bo2]; apply(bo, bv); apply(bo2, (old / D) * D + s2 % D);
            int p1 = bpos[bo], p2 = bpos[bo2]; blist[p1] = bo2; blist[p2] = bo; bpos[bo] = p2; bpos[bo2] = p1; }
        else apply(bo, bv);
        tabu[(size_t)bo * K + old] = it + 5 + rnd() % 10;
        if (cost < best) { best = cost; memcpy(bests, s, sizeof(int) * NO); if (best < 50 || (it & 1023) == 0) fprintf(stderr, "it %ld cost %ld (%.0fs)\n", it, cost, (double)(clock() - t0) / CLOCKS_PER_SEC); }
    }
    printf("q=%d %s k=%d best cost %ld after %ld iterations\n", q, argv[3], K, best, it);
    {   /* recompute the cost of the best state from scratch (bookkeeping check) */
        memset(cnt, 0, sizeof(int) * (size_t)NO * K); long cc = 0;
        for (int o = 0; o < NO; o++) for (int t = occ_start[o]; t < occ_start[o + 1]; t++) cnt[occ_b[t] * K + COLOR(occ_j[t], bests[o])]++;
        for (int b = 0; b < NO; b++) for (int c = 0; c < K; c++) if (!cnt[b * K + c]) cc++;
        int *bs = calloc(A, sizeof(int)); for (int o = 0; o < NO; o++) bs[bests[o] / D]++;
        int mn = NO, mx = 0; for (int a = 0; a < A; a++) { if (bs[a] < mn) mn = bs[a]; if (bs[a] > mx) mx = bs[a]; }
        printf("recomputed cost %ld; orbits per block min %d max %d\n", cc, mn, mx);
        if (cc != best) { fprintf(stderr, "BOOKKEEPING ERROR\n"); return 1; }
    }
    if (best == 0) {
        int *col = malloc(sizeof(int) * N);
        for (int x = 0; x < N; x++) col[x] = COLOR(idx[x], bests[orb[x]]);
        f = fopen(argv[6], "wb"); fwrite(col, 4, N, f); fclose(f);
    }
    return 0;
}
