/* lsearch.c: local search for Z_N voltages on "hexagon H(q) + k hop matchings" so that the Z_N-lift has all
   point-line pairs within distance 7 (bipartite diameter <= 8).

   Base: points 0..n-1, lines 0..n-1 of H(q) (hex/hex_qQ.bin), hexagon edges (p,l) for p on l, plus k random perfect
   matchings p -> M_j(p) (hop edges). Lift group Z_N (N <= 64), voltage of edge read from point to line.
   Modes: FIXLEV=c  : voltages are forced to c-level structure: hexagon edge voltage = c*z, hop j voltage = j + c*z?? (unused)
   Simple version: all voltages free in Z_N. Objective = total uncovered (line,x) over all point sources.

   Usage: lsearch q k N seconds seed [init: 0 = random, 1 = delorme (hex 0, hop j -> j)] [out]
   Writes the best base graph in liftcheck format to out (default /tmp/ls_best.base). */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#ifdef _OPENMP
#include <omp.h>
#endif
typedef uint64_t u64;
static int q, n, k, N, Q1, DEG;
static int *lines;      /* n*(q+1) */
static int *padjL, *pvol;   /* per point: DEG entries (line, voltage), first q+1 hexagon then k hops */
static u64 FULL;
static int *lstart, *lpt, *lslot; /* per line: list of (point, slot index into point's adjacency) */

static inline u64 rot(u64 x, int g) { g %= N; if (g < 0) g += N; if (!g) return x; return ((x << g) | (x >> (N - g))) & FULL; }

static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }

/* exact evaluation: total uncovered pairs; also per-source counts into unc[] if non-null */
static long long evaluate(int *unc) {
    long long total = 0;
    #pragma omp parallel reduction(+:total)
    {
        u64 *rp = malloc(8 * n), *rl = malloc(8 * n), *fp = malloc(8 * n), *fl = malloc(8 * n);
        #pragma omp for schedule(dynamic, 8)
        for (int s = 0; s < n; s++) {
            memset(rp, 0, 8 * n); memset(rl, 0, 8 * n); memset(fp, 0, 8 * n); memset(fl, 0, 8 * n);
            rp[s] = fp[s] = 1;
            for (int t = 1; t <= 7; t++) {
                if (t & 1) {
                    for (int y = 0; y < n; y++) {
                        u64 acc = 0;
                        for (int i = lstart[y]; i < lstart[y + 1]; i++) { int p = lpt[i]; u64 x = fp[p]; if (x) acc |= rot(x, pvol[p * DEG + lslot[i]]); }
                        acc &= ~rl[y]; fl[y] = acc; rl[y] |= acc;
                    }
                } else if (t < 7) {
                    for (int p = 0; p < n; p++) {
                        u64 acc = 0;
                        for (int j = 0; j < DEG; j++) { u64 x = fl[padjL[p * DEG + j]]; if (x) acc |= rot(x, -pvol[p * DEG + j]); }
                        acc &= ~rp[p]; fp[p] = acc; rp[p] |= acc;
                    }
                }
            }
            long long u = 0;
            for (int y = 0; y < n; y++) u += N - __builtin_popcountll(rl[y]);
            if (unc) unc[s] = (int)u;
            total += u;
        }
        free(rp); free(rl); free(fp); free(fl);
    }
    return total;
}

static void build_line_index(void) {
    lstart = calloc(n + 1, sizeof(int));
    for (int p = 0; p < n; p++) for (int j = 0; j < DEG; j++) lstart[padjL[p * DEG + j] + 1]++;
    for (int y = 0; y < n; y++) lstart[y + 1] += lstart[y];
    lpt = malloc(sizeof(int) * n * DEG); lslot = malloc(sizeof(int) * n * DEG);
    int *c = calloc(n, sizeof(int));
    for (int p = 0; p < n; p++) for (int j = 0; j < DEG; j++) { int y = padjL[p * DEG + j]; int i = lstart[y] + c[y]++; lpt[i] = p; lslot[i] = j; }
    free(c);
}

int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: lsearch q k N seconds seed [init] [out]\n"); return 1; }
    q = atoi(argv[1]); k = atoi(argv[2]); N = atoi(argv[3]); double secs = atof(argv[4]); int seed = atoi(argv[5]);
    int init = argc > 6 ? atoi(argv[6]) : 0; const char *out = argc > 7 ? argv[7] : "/tmp/ls_best.base";
    FULL = (N == 64) ? ~0ULL : ((1ULL << N) - 1);
    char fn[256]; sprintf(fn, "%s/../hex/hex_q%d.bin", getenv("HEXDIR") ? getenv("HEXDIR") : ".", q);
    FILE *f = fopen(fn, "rb"); if (!f) { sprintf(fn, "../hex/hex_q%d.bin", q); f = fopen(fn, "rb"); }
    if (!f) { perror(fn); return 1; }
    int32_t hdr[3]; if (fread(hdr, 4, 3, f) != 3) return 1;
    n = hdr[1]; Q1 = q + 1; DEG = Q1 + k;
    lines = malloc(sizeof(int) * n * Q1); if (fread(lines, 4, (size_t)n * Q1, f) != (size_t)n * Q1) return 1; fclose(f);
    srand(seed);
    padjL = malloc(sizeof(int) * n * DEG); pvol = malloc(sizeof(int) * n * DEG);
    int *cnt = calloc(n, sizeof(int));
    for (int l = 0; l < n; l++) for (int i = 0; i < Q1; i++) { int p = lines[l * Q1 + i]; padjL[p * DEG + cnt[p]++] = l; }
    int *perm = malloc(sizeof(int) * n);
    for (int j = 0; j < k; j++) {
        for (int i = 0; i < n; i++) perm[i] = i;
        for (int i = n - 1; i > 0; i--) { int r = rand() % (i + 1); int t = perm[i]; perm[i] = perm[r]; perm[r] = t; }
        for (int p = 0; p < n; p++) padjL[p * DEG + Q1 + j] = perm[p];
    }
    for (int p = 0; p < n; p++) for (int j = 0; j < DEG; j++) pvol[p * DEG + j] = init == 1 ? (j < Q1 ? 0 : (j - Q1 + 1) % N) : rand() % N;
    build_line_index();
    int *unc = malloc(sizeof(int) * n);
    double t0 = now();
    long long cur = evaluate(unc), best = cur;
    fprintf(stderr, "q=%d n=%d k=%d N=%d lift=%lld init cost %lld (%.3fs/eval)\n", q, n, k, N, 2LL * n * N, cur, now() - t0);
    long long it = 0; double T = 2.0;
    int *bestvol = malloc(sizeof(int) * n * DEG); memcpy(bestvol, pvol, sizeof(int) * n * DEG);
    while (now() - t0 < secs && best > 0) {
        it++;
        /* move: pick a bad source with prob 0.7 and change an edge at it or a random edge */
        int p, j;
        if (rand() % 10 < 7) {
            int s; int tries = 0; do { s = rand() % n; } while (unc[s] == 0 && ++tries < 50);
            p = s; j = rand() % DEG;
            if (rand() % 2) { /* move to a random neighbour's point via a random line */
                int y = padjL[p * DEG + j]; int i = lstart[y] + rand() % (lstart[y + 1] - lstart[y]); p = lpt[i]; j = rand() % DEG;
            }
        } else { p = rand() % n; j = rand() % DEG; }
        int old = pvol[p * DEG + j]; int nv = rand() % N; if (nv == old) nv = (nv + 1) % N;
        pvol[p * DEG + j] = nv;
        int *unc2 = malloc(sizeof(int) * n);
        long long c2 = evaluate(unc2);
        double d = (double)(c2 - cur);
        if (c2 <= cur || (T > 0 && exp(-d / T) * RAND_MAX > rand())) {
            cur = c2; memcpy(unc, unc2, sizeof(int) * n);
            if (cur < best) { best = cur; memcpy(bestvol, pvol, sizeof(int) * n * DEG); }
        } else pvol[p * DEG + j] = old;
        free(unc2);
        T *= 0.9995; if (T < 0.05) T = 0.05;
        if (it % 200 == 0) fprintf(stderr, "it %lld cur %lld best %lld T %.3f t %.0fs\n", it, cur, best, T, now() - t0);
    }
    printf("RESULT q=%d k=%d N=%d lift=%lld best=%lld iters=%lld time=%.1f\n", q, k, N, 2LL * n * N, best, it, now() - t0);
    FILE *g = fopen(out, "w");
    fprintf(g, "%d %d %d cyc\n", n, n, N);
    for (int pp = 0; pp < n; pp++) for (int jj = 0; jj < DEG; jj++) fprintf(g, "%d %d %d\n", pp, padjL[pp * DEG + jj], bestvol[pp * DEG + jj]);
    fclose(g);
    return 0;
}
