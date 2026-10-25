/* mindeg: min-degree dynamic greedy for a non-concurrent (pairwise disjoint) line set of H(q).
   Each step picks, uniformly at random among the available lines of minimum conflict degree,
   where conflict degree = number of still-available lines meeting it = sum_{p in L}(A[p]-1).
   Usage: mindeg HEXBIN SEED SEEDFILE|- OUT [TRIALS]
   SEEDFILE lines are forced in first (skipped if they conflict). Writes chosen line ids, one per line. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

static int q, N, Lc, Q1;
static int *LP, *PL, *A, *deg, *bkpos, **bk, *bksz, *bkcap, mind;
static char *avail;
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }

static void bk_add(int L, int d) {
    deg[L] = d;
    if (bksz[d] == bkcap[d]) {
        bkcap[d] = bkcap[d] ? 2 * bkcap[d] : 64;
        bk[d] = realloc(bk[d], bkcap[d] * sizeof(int));
    }
    bkpos[L] = bksz[d];
    bk[d][bksz[d]++] = L;
    if (d < mind) mind = d;
}
static void bk_del(int L) {
    int d = deg[L], i = bkpos[L];
    int last = bk[d][--bksz[d]];
    bk[d][i] = last;
    bkpos[last] = i;
}

static int *blk; static int nblk;

/* choose line L: block all available lines meeting L (incl. L), update A and degrees */
static void choose(int L) {
    nblk = 0;
    for (int j = 0; j < Q1; j++) {
        int p = LP[(long)L * Q1 + j];
        for (int k = 0; k < Q1; k++) {
            int M = PL[(long)p * Q1 + k];
            if (avail[M]) { avail[M] = 0; bk_del(M); blk[nblk++] = M; }
        }
    }
    for (int b = 0; b < nblk; b++) {
        int M = blk[b];
        for (int j = 0; j < Q1; j++) {
            int x = LP[(long)M * Q1 + j];
            A[x]--;
            for (int k = 0; k < Q1; k++) {
                int K = PL[(long)x * Q1 + k];
                if (avail[K]) { bk_del(K); bk_add(K, deg[K] - 1); }
            }
        }
    }
    avail[L] = 2; /* chosen marker */
}

int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage: mindeg HEXBIN SEED SEEDFILE|- OUT [TRIALS]\n"); return 1; }
    FILE *f = fopen(argv[1], "rb");
    if (!f) { perror("hex"); return 1; }
    int hdr[3];
    if (fread(hdr, 4, 3, f) != 3) return 1;
    q = hdr[0]; N = hdr[1]; Lc = hdr[2]; Q1 = q + 1;
    LP = malloc((size_t)Lc * Q1 * sizeof(int));
    if (fread(LP, sizeof(int), (size_t)Lc * Q1, f) != (size_t)Lc * Q1) return 1;
    fclose(f);
    /* point -> lines */
    int *cnt = calloc(N, sizeof(int));
    PL = malloc((size_t)N * Q1 * sizeof(int));
    for (long L = 0; L < Lc; L++) for (int j = 0; j < Q1; j++) { int p = LP[L * Q1 + j]; PL[(long)p * Q1 + cnt[p]++] = (int)L; }
    for (int p = 0; p < N; p++) if (cnt[p] != Q1) { fprintf(stderr, "point %d has %d lines\n", p, cnt[p]); return 1; }
    free(cnt);
    uint64_t seed = strtoull(argv[2], 0, 10);
    rs ^= seed * 0x9E3779B97F4A7C15ULL; if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();
    int trials = argc > 5 ? atoi(argv[5]) : 1;

    A = malloc(N * sizeof(int));
    deg = malloc(Lc * sizeof(int));
    bkpos = malloc(Lc * sizeof(int));
    avail = malloc(Lc);
    blk = malloc(Lc * sizeof(int));
    int maxd = Q1 * Q1 + 1;
    bk = calloc(maxd + 1, sizeof(int *)); bksz = calloc(maxd + 1, sizeof(int)); bkcap = calloc(maxd + 1, sizeof(int));

    int best = -1;
    int *bestset = malloc(N * sizeof(int));
    for (int t = 0; t < trials; t++) {
        for (int p = 0; p < N; p++) A[p] = Q1;
        for (int d = 0; d <= maxd; d++) bksz[d] = 0;
        memset(avail, 1, Lc);
        mind = maxd;
        for (long L = 0; L < Lc; L++) bk_add((int)L, Q1 * (Q1 - 1));
        int *chosen = malloc(Lc * sizeof(int)); int nch = 0;
        /* forced seeds */
        if (strcmp(argv[3], "-") != 0) {
            FILE *g = fopen(argv[3], "r");
            if (!g) { perror("seedfile"); return 1; }
            int L; int forced = 0, skipped = 0; char buf[256];
            while (fgets(buf, sizeof buf, g)) {
                if (buf[0] == '#' || sscanf(buf, "%d", &L) != 1) continue;
                if (L < 0 || L >= Lc) continue;
                if (avail[L] == 1) { choose(L); chosen[nch++] = L; forced++; }
                else skipped++;
            }
            fclose(g);
            if (t == 0) fprintf(stderr, "forced %d skipped %d\n", forced, skipped);
        }
        for (;;) {
            while (mind <= maxd && bksz[mind] == 0) mind++;
            if (mind > maxd) break;
            int L = bk[mind][rnd() % bksz[mind]];
            choose(L);
            chosen[nch++] = L;
        }
        fprintf(stderr, "trial %d size %d\n", t, nch);
        if (nch > best) {
            best = nch;
            memcpy(bestset, chosen, nch * sizeof(int));
            FILE *o = fopen(argv[4], "w");
            for (int i = 0; i < nch; i++) fprintf(o, "%d\n", chosen[i]);
            fclose(o);
        }
        free(chosen);
    }
    printf("best %d\n", best);
    return 0;
}
