/* linestar_ls.c (card c8, squad round 2): simulated annealing over LINE-STAR sets of H(11).
   A star = middle line m plus lines s_1..s_k (k <= 11) meeting m in distinct points; lines of different stars must be
   pairwise opposite (distance 6), lines of one star are automatically at distance 4.  Score = number of non-middle lines.
   Every S-line y has a middle mid[y] (a line meeting y, not in S).  State invariants: distinct stars have distinct middles,
   middles are not in S, stars have <= MAXSTAR lines and at most CAP stars are nonempty.

   cnt[x] = number of S-lines y != x with d(x,y) <= 4 (ball4 of x has 16104 lines, computed on the fly).
   Inserting line l with middle m (x = l ∩ m, slot k of x on m): conflicts = cnt[l] - starsize[m] + [star m already has a
   line through x]; the S-lines in ball4(l) that must be removed are those with mid != m, plus the owner of x.

   usage: linestar_ls HEXFILE SEED CPU_SEC MODE OUTFILE [T0 T1 ITERS MAXSTAR CAP]
   MODE 0: middles restricted to the Hermitian spread (lines with x0+x4 = 0 on all points);  MODE 1: any middle. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>

static int q, N, L, Q1;
static int32_t *LP, *PL;
static int32_t *cnt, *mid, *ownerSlot, *starsize, *own, *Slist, *Spos, *ballbuf;
static char *inS, *isSpread;
static int nS = 0, nStars = 0, CAP = 121, MAXSTAR = 11;
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline double rndu(void) { return (rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int ball4(int l, int32_t *out) {
    int nb = 0;
    for (int k = 0; k < Q1; k++) {
        int p = LP[(size_t)l * Q1 + k];
        for (int j = 0; j < Q1; j++) {
            int M = PL[(size_t)p * Q1 + j];
            if (M == l) continue;
            out[nb++] = M;
            for (int kk = 0; kk < Q1; kk++) {
                int r = LP[(size_t)M * Q1 + kk];
                if (r == p) continue;
                for (int jj = 0; jj < Q1; jj++) {
                    int Nn = PL[(size_t)r * Q1 + jj];
                    if (Nn == M) continue;
                    out[nb++] = Nn;
                }
            }
        }
    }
    return nb;
}
static inline int slotOf(int m, int x) {
    for (int k = 0; k < Q1; k++) if (LP[(size_t)m * Q1 + k] == x) return k;
    return -1;
}
static void addLine(int l, int m, int x) {
    int k = slotOf(m, x);
    inS[l] = 1; mid[l] = m; ownerSlot[l] = k;
    if (starsize[m] == 0) nStars++;
    starsize[m]++;
    own[(size_t)m * Q1 + k] = l;
    Spos[l] = nS; Slist[nS++] = l;
    int nb = ball4(l, ballbuf);
    for (int i = 0; i < nb; i++) cnt[ballbuf[i]]++;
}
static void remLine(int y) {
    int m = mid[y], k = ownerSlot[y];
    own[(size_t)m * Q1 + k] = -1;
    starsize[m]--; if (starsize[m] == 0) nStars--;
    inS[y] = 0; mid[y] = -1;
    int pos = Spos[y], last = Slist[--nS];
    Slist[pos] = last; Spos[last] = pos;
    int nb = ball4(y, ballbuf);
    for (int i = 0; i < nb; i++) cnt[ballbuf[i]]--;
}
typedef struct { int line, mid; } pair_t;
static int cmp_pair(const void *a, const void *b) {
    const pair_t *x = a, *y = b;
    if (x->mid != y->mid) return x->mid < y->mid ? -1 : 1;
    return x->line < y->line ? -1 : (x->line > y->line);
}
static void write_stars(const char *fn, pair_t *best, int nb) {
    qsort(best, nb, sizeof(pair_t), cmp_pair);
    FILE *f = fopen(fn, "w"); if (!f) return;
    int i = 0;
    while (i < nb) {
        int m = best[i].mid; fprintf(f, "%d", m);
        while (i < nb && best[i].mid == m) { fprintf(f, " %d", best[i].line); i++; }
        fprintf(f, "\n");
    }
    fclose(f);
}

int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: linestar_ls HEXFILE SEED CPU_SEC MODE OUTFILE [T0 T1 ITERS MAXSTAR CAP]\n"); return 2; }
    uint64_t seed = strtoull(argv[2], 0, 10);
    double cpu_limit = atof(argv[3]);
    int mode = atoi(argv[4]);
    const char *outfn = argv[5];
    double T0 = argc > 6 ? atof(argv[6]) : 0.9, T1 = argc > 7 ? atof(argv[7]) : 0.08;
    double iters_d = argc > 8 ? atof(argv[8]) : 2e7;
    if (argc > 9) MAXSTAR = atoi(argv[9]);
    if (argc > 10) CAP = atoi(argv[10]);
    rs ^= seed * 0x9E3779B97F4A7C15ULL; if (!rs) rs = 1; for (int i = 0; i < 10; i++) rnd64();

    FILE *f = fopen(argv[1], "rb"); int32_t hdr[3];
    if (!f || fread(hdr, 4, 3, f) != 3) { fprintf(stderr, "bad hex file\n"); return 2; }
    q = hdr[0]; N = hdr[1]; L = hdr[2]; Q1 = q + 1;
    LP = malloc(4L * L * Q1);
    if (fread(LP, 4, (size_t)L * Q1, f) != (size_t)L * Q1) { fprintf(stderr, "short read\n"); return 2; }
    uint8_t *coord = malloc((size_t)N * 7);
    if (fread(coord, 1, (size_t)N * 7, f) != (size_t)N * 7) { fprintf(stderr, "short read coords\n"); return 2; }
    fclose(f);
    PL = malloc(4L * N * Q1);
    int *pc = calloc(N, sizeof(int));
    for (int l = 0; l < L; l++) for (int k = 0; k < Q1; k++) { int p = LP[(size_t)l * Q1 + k]; PL[(size_t)p * Q1 + pc[p]++] = l; }
    for (int p = 0; p < N; p++) if (pc[p] != Q1) { fprintf(stderr, "point %d has %d lines\n", p, pc[p]); return 2; }
    free(pc);
    isSpread = calloc(L, 1); int nsp = 0;
    for (int l = 0; l < L; l++) {
        int ok = 1;
        for (int k = 0; k < Q1 && ok; k++) { int p = LP[(size_t)l * Q1 + k];
            if ((coord[(size_t)p * 7 + 0] + coord[(size_t)p * 7 + 4]) % q != 0) ok = 0; }
        isSpread[l] = ok; nsp += ok;
    }
    fprintf(stderr, "q=%d N=%d L=%d spread lines=%d\n", q, N, L, nsp);

    cnt = calloc(L, 4); mid = malloc(4L * L); for (int i = 0; i < L; i++) mid[i] = -1;
    ownerSlot = calloc(L, 4); starsize = calloc(L, 4); own = malloc(4L * L * Q1);
    for (size_t i = 0; i < (size_t)L * Q1; i++) own[i] = -1;
    Slist = malloc(4L * L); Spos = malloc(4L * L); ballbuf = malloc(4 * 16200);
    inS = calloc(L, 1);

    pair_t *bestPairs = malloc(sizeof(pair_t) * 4096);
    int bestS = 0, bestStars = 0;
    int nconf_max = 16200; int32_t *confl = malloc(4 * nconf_max);

    double iters = iters_d; (void)iters;
    clock_t c0 = clock();
    long long it;
    long long report_every = 200000; double used_now = 0, frac = 0;
    for (it = 0; it < (long long)iters; it++) {
        if ((it & 0xFFF) == 0) {
            used_now = (double)(clock() - c0) / CLOCKS_PER_SEC;
            if (used_now > cpu_limit) break;
            frac = used_now / cpu_limit;
        }
        if (it && it % report_every == 0) {
            double used = (double)(clock() - c0) / CLOCKS_PER_SEC;
            fprintf(stderr, "it %lld cpu %.1f |S| %d stars %d best %d\n", it, used, nS, nStars, bestS);
        }
        double T = T0 * pow(T1 / T0, frac);
        int l = (int)(rnd64() % (uint64_t)L);
        if (inS[l]) continue;
        if (mode == 0 && isSpread[l]) continue;
        int bestconf = 1 << 30, bm = -1, bx = -1, bk = -1, nties = 0;
        for (int k = 0; k < Q1; k++) {
            int x = LP[(size_t)l * Q1 + k];
            for (int j = 0; j < Q1; j++) {
                int m = PL[(size_t)x * Q1 + j];
                if (m == l) continue;
                if (mode == 0 && !isSpread[m]) continue;
                int kk = slotOf(m, x);
                int ow = own[(size_t)m * Q1 + kk];
                if (starsize[m] == 0 && nStars >= CAP) continue;
                if (ow < 0 && starsize[m] >= MAXSTAR) continue;
                int conf = cnt[l] - starsize[m] + (ow >= 0);
                if (conf < bestconf) { bestconf = conf; bm = m; bx = x; bk = kk; nties = 1; }
                else if (conf == bestconf) { nties++; if (rnd64() % nties == 0) { bm = m; bx = x; bk = kk; } }
            }
        }
        if (bm < 0) continue;
        double delta = 1.0 - bestconf;
        if (delta < 0 && rndu() >= exp(delta / T)) continue;
        int nb = ball4(l, ballbuf);
        int nc = 0;
        for (int i = 0; i < nb; i++) {
            int y = ballbuf[i];
            if (inS[y] && (mid[y] != bm || y == own[(size_t)bm * Q1 + bk])) {
                if (nc < nconf_max) confl[nc++] = y;
            }
        }
        if (nc != bestconf) { fprintf(stderr, "internal mismatch nc=%d conf=%d\n", nc, bestconf); return 3; }
        for (int i = 0; i < nc; i++) remLine(confl[i]);
        addLine(l, bm, bx);
        if (nS > bestS) {
            bestS = nS; bestStars = nStars;
            for (int i = 0; i < nS; i++) { bestPairs[i].line = Slist[i]; bestPairs[i].mid = mid[Slist[i]]; }
            /* keep a copy of the best */
        }
    }
    double used = (double)(clock() - c0) / CLOCKS_PER_SEC;
    /* the current state may be worse than best: report best only (bestPairs holds the best state) */
    fprintf(stderr, "done it=%lld cpu=%.1f best |S|=%d stars=%d avg=%.3f\n", it, used, bestS, bestStars,
            bestStars ? (double)bestS / bestStars : 0.0);
    write_stars(outfn, bestPairs, bestS);
    printf("BEST %d %d %.4f\n", bestS, bestStars, bestStars ? (double)bestS / bestStars : 0.0);
    return 0;
}
