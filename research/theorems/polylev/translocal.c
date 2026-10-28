/* translocal.c: local search for a T-equivariant dominating colouring (same problem as transsat.py).
   polylev job (Opus), 2026-10-28.

   T = <h> semiregular of order k on the points (or lines) of H(q). Orbit O has representative b_O; the element
   h^j b_O gets colour j + s_O (mod k). Cost = sum over orbit representatives x of the number of colours missing
   from the 2-ball B2(x) (it is the same for every element of the orbit). Tabu search on the s_O: each step moves the
   orbit/value pair with the best cost change among the orbits that touch an incomplete ball, with a tabu tenure.
   Usage: translocal HEXBIN PERM lines|points SEED SECONDS OUT
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
static int *s;                  /* s[O] */
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

static long delta_of(int o, int v) {   /* cost change of setting s[o] = v */
    int d = (v - s[o] + K) % K; if (!d) return 0;
    long dc = 0;
    /* apply then revert */
    for (int t = occ_start[o]; t < occ_start[o + 1]; t++) {
        int b = occ_b[t], c0 = (occ_j[t] + s[o]) % K, c1 = (c0 + d) % K;
        if (--cnt[b * K + c0] == 0) dc++;
        if (cnt[b * K + c1]++ == 0) dc--;
    }
    for (int t = occ_start[o]; t < occ_start[o + 1]; t++) {
        int b = occ_b[t], c0 = (occ_j[t] + s[o]) % K, c1 = (c0 + d) % K;
        cnt[b * K + c1]--; cnt[b * K + c0]++;
    }
    return dc;
}
static void apply(int o, int v) {
    int d = (v - s[o] + K) % K;
    for (int t = occ_start[o]; t < occ_start[o + 1]; t++) {
        int b = occ_b[t], c0 = (occ_j[t] + s[o]) % K, c1 = (c0 + d) % K;
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
    ball = malloc(sizeof(int) * (size_t)NO * B);
    for (int o = 0; o < NO; o++) build_ball(rep[o], lines, ball + (size_t)o * B);
    occ_start = calloc(NO + 1, sizeof(int));
    for (int b = 0; b < NO; b++) for (int t = 0; t < B; t++) occ_start[orb[ball[(size_t)b * B + t]] + 1]++;
    for (int o = 0; o < NO; o++) occ_start[o + 1] += occ_start[o];
    occ_b = malloc(sizeof(int) * (size_t)NO * B); occ_j = malloc(sizeof(int) * (size_t)NO * B); int *fill = calloc(NO, sizeof(int));
    for (int b = 0; b < NO; b++) for (int t = 0; t < B; t++) { int x = ball[(size_t)b * B + t], o = orb[x]; int p = occ_start[o] + fill[o]++; occ_b[p] = b; occ_j[p] = idx[x]; }
    cnt = calloc((size_t)NO * K, sizeof(int)); miss = calloc(NO, sizeof(int)); s = calloc(NO, sizeof(int));
    for (int o = 0; o < NO; o++) s[o] = rnd() % K;
    for (int o = 0; o < NO; o++) for (int t = occ_start[o]; t < occ_start[o + 1]; t++) cnt[occ_b[t] * K + (occ_j[t] + s[o]) % K]++;
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
        long bd = 1L << 40; int bo = -1, bv = -1, ties = 0;
        int noise = (rnd() % 100) < 3;
        for (int t = 0; t < B; t++) {
            int x = ball[(size_t)b * B + t], o = orb[x], v = ((c - idx[x]) % K + K) % K;
            if (v == s[o]) continue;
            long d = delta_of(o, v);
            if (noise) { if (rnd() % (++ties) == 0) { bo = o; bv = v; bd = d; } continue; }
            if (tabu[(size_t)o * K + v] > it && cost + d >= best) continue;
            if (d < bd) { bd = d; bo = o; bv = v; ties = 1; }
            else if (d == bd && rnd() % (++ties) == 0) { bo = o; bv = v; }
        }
        if (bo < 0) continue;
        int old = s[bo];
        apply(bo, bv);
        tabu[(size_t)bo * K + old] = it + 5 + rnd() % 10;
        if (cost < best) { best = cost; memcpy(bests, s, sizeof(int) * NO); if (best < 50 || (it & 1023) == 0) fprintf(stderr, "it %ld cost %ld (%.0fs)\n", it, cost, (double)(clock() - t0) / CLOCKS_PER_SEC); }
    }
    printf("q=%d %s k=%d best cost %ld after %ld iterations\n", q, argv[3], K, best, it);
    if (best == 0) {
        int *col = malloc(sizeof(int) * N);
        for (int x = 0; x < N; x++) col[x] = (idx[x] + bests[orb[x]]) % K;
        f = fopen(argv[6], "wb"); fwrite(col, 4, N, f); fclose(f);
    }
    return 0;
}
