/* ovsearch.c (card c4): k-fixed tabu search for pairwise-opposite point sets in the affine chart of Q(6,11).
   Chart point u = (a,b,c,d,e) in GF(11)^5 is the point (1, a, b, c, x4, d, e) with x4 = c^2 - a d - b e
   (coordinates x0..x6 of the quadric x0x4+x1x5+x2x6 = x3^2; here a=x1, b=x2, c=x3, d=x5, e=x6).
   Two chart points are collinear in H(11) iff Q'(u-v)=0, Q'(w)=c^2 - a d - b e. The graph is the Cayley graph of
   GF(11)^5 with connection set C = nonzero isotropic vectors of Q' (|C| = 14640). We look for independent sets.
   Usage: ovsearch SECONDS SEED KSTART OUTFILE   (writes the best set found as lines "a b c d e")
   Compile: gcc -O2 -o ovsearch ovsearch.c */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define Q 11
#define N 161051
static int nC; static int Cd[15000][5];     /* digits of the connection set */
static int *tight; static char *inS; static int *Slist, *posS; static int k;
static long *tabuIn, *tabuOut;
static unsigned long long rs = 88172645463325252ULL;
static inline unsigned long long rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int pw[5] = {1, 11, 121, 1331, 14641};

static inline int addIdx(int v, int w) { /* v and w given as digit-packed index, w as digits Cd[w] */
    return v; }
static void digitsOf(int v, int *d) { for (int i = 0; i < 5; i++) { d[i] = v % Q; v /= Q; } }
static int nbIndex(int u, int ci) {
    int idx = 0; int ud[5]; digitsOf(u, ud);
    for (int i = 0; i < 5; i++) { int x = ud[i] + Cd[ci][i]; if (x >= Q) x -= Q; idx += x * pw[i]; }
    return idx;
}
static void addV(int v) { int ud[5]; digitsOf(v, ud);
    for (int c = 0; c < nC; c++) { int x = 0; for (int i = 0; i < 5; i++) { int y = ud[i] + Cd[c][i]; if (y >= Q) y -= Q; x += y * pw[i]; } tight[x]++; }
    inS[v] = 1; posS[v] = k; Slist[k++] = v; }
static void remV(int v) { int ud[5]; digitsOf(v, ud);
    for (int c = 0; c < nC; c++) { int x = 0; for (int i = 0; i < 5; i++) { int y = ud[i] + Cd[c][i]; if (y >= Q) y -= Q; x += y * pw[i]; } tight[x]--; }
    inS[v] = 0; int p = posS[v]; k--; Slist[p] = Slist[k]; posS[Slist[p]] = p; }

int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage: ovsearch SECONDS SEED KSTART OUTFILE\n"); return 2; }
    double secs = atof(argv[1]); rs ^= strtoull(argv[2], 0, 10) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 10; i++) rnd();
    int kstart = atoi(argv[3]);
    /* connection set: nonzero w with w_c^2 - w_a w_d - w_b w_e = 0 (mod 11), digits (a,b,c,d,e) */
    nC = 0;
    for (int v = 1; v < N; v++) { int d[5]; digitsOf(v, d);
        int qv = ((d[2] * d[2] - d[0] * d[3] - d[1] * d[4]) % Q + 2 * Q * Q) % Q;
        if (qv == 0) { memcpy(Cd[nC], d, sizeof(d)); nC++; } }
    fprintf(stderr, "connection set size %d (expect 14640)\n", nC);
    tight = calloc(N, sizeof(int)); inS = calloc(N, 1); Slist = malloc(sizeof(int) * N); posS = malloc(sizeof(int) * N);
    tabuIn = calloc(N, sizeof(long)); tabuOut = calloc(N, sizeof(long));
    k = 0;
    /* initial set: random vertices with min tight */
    for (int i = 0; i < kstart; i++) {
        int best = -1, bt = 1 << 30, cnt = 0;
        for (int t = 0; t < 200; t++) { int v = rnd() % N; if (inS[v]) continue; if (tight[v] < bt) { bt = tight[v]; best = v; } }
        addV(best);
    }
    long conflicts = 0; for (int i = 0; i < k; i++) conflicts += tight[Slist[i]]; conflicts /= 2;
    int bestK = 0; clock_t c0 = clock(); long it = 0; long lastImp = 0;
    FILE *fo = NULL;
    int *cand = malloc(sizeof(int) * N);
    while (1) {
        double el = (double)(clock() - c0) / CLOCKS_PER_SEC; if (el > secs) break;
        if (conflicts == 0) {
            if (k > bestK) {
                bestK = k; fprintf(stderr, "valid k=%d at %.1fs it %ld\n", k, el, it);
                fo = fopen(argv[4], "w"); for (int i = 0; i < k; i++) { int d[5]; digitsOf(Slist[i], d); fprintf(fo, "%d %d %d %d %d\n", d[0], d[1], d[2], d[3], d[4]); } fclose(fo);
            }
            /* grow: add the non-S vertex with min tight */
            int best = -1, bt = 1 << 30, nb = 0;
            for (int v = 0; v < N; v++) if (!inS[v]) { if (tight[v] < bt) { bt = tight[v]; best = v; nb = 1; } else if (tight[v] == bt && (rnd() % (++nb)) == 0) best = v; }
            addV(best); conflicts += tight[best];   /* tight[best] counts neighbours in S before add: edges added */
            continue;
        }
        it++;
        /* pick a random conflicting S vertex */
        int nc = 0; for (int i = 0; i < k; i++) if (tight[Slist[i]] > 0) cand[nc++] = Slist[i];
        int x = cand[rnd() % nc];
        conflicts -= tight[x]; remV(x); tabuOut[x] = it + 7 + (long)(rnd() % 10);
        /* best non-S vertex by tight, non-tabu (aspiration if it improves best) */
        int best = -1, bt = 1 << 30, nb = 0;
        for (int v = 0; v < N; v++) { if (inS[v] || v == x) continue; if (tabuOut[v] > it) continue; int t = tight[v];
            if (t < bt) { bt = t; best = v; nb = 1; } else if (t == bt && (rnd() % (++nb)) == 0) best = v; }
        if (best < 0) { best = x; bt = tight[x]; }
        addV(best); conflicts += tight[best] - 0;  /* tight[best] now counts neighbours in S including itself? no: best not its own neighbour */
        tabuIn[best] = it + 3;
        /* recompute conflicts exactly every 10000 iterations (guard against bookkeeping slips) */
        if ((it % 10000) == 0) { long c2 = 0; for (int i = 0; i < k; i++) c2 += tight[Slist[i]]; c2 /= 2; conflicts = c2; }
        if ((it % 200000) == 0) fprintf(stderr, "it %ld k %d conflicts %ld best %d (%.0fs)\n", it, k, conflicts, bestK, el);
    }
    fprintf(stderr, "done: best valid k = %d after %ld iterations\n", bestK, it);
    printf("%d\n", bestK);
    return 0;
}
