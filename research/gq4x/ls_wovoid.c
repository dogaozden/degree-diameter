/* Tabu search for a weighted m-ovoid: weights w_p in 0..WMAX with every line summing to exactly m.

   usage: ls_wovoid INSTANCE m WMAX SECONDS SEED [OUT]
   INSTANCE as for ls_cap. Total weight is fixed at m * (#lines) / (line degree of a point) (all points must be on the
   same number of lines). Move: w_p -= 1, w_r += 1. Cost = sum over lines (s_L - m)^2. On success writes "p w" lines.
*/
#include <stdio.h>
#include <stdlib.h>
#include <time.h>

static int n, mL, M, WMAX;
static int *lsz, **lpts, *pdeg, **plines, *s, *w, *tabu;
static unsigned long long rs;
static inline unsigned rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return (unsigned)(rs >> 11); }
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }

static long dinc(int p) { long d = 0; for (int i = 0; i < pdeg[p]; i++) d += 2 * (s[plines[p][i]] - M) + 1; return d; }
static long ddec(int p) { long d = 0; for (int i = 0; i < pdeg[p]; i++) d += -2 * (s[plines[p][i]] - M) + 1; return d; }
static void chg(int p, int d) { w[p] += d; for (int i = 0; i < pdeg[p]; i++) s[plines[p][i]] += d; }

int main(int argc, char **argv) {
    FILE *f = fopen(argv[1], "r");
    M = atoi(argv[2]); WMAX = atoi(argv[3]); double secs = atof(argv[4]);
    rs = 0x9E3779B97F4A7C15ULL * (atoi(argv[5]) + 1);
    if (fscanf(f, "%d %d", &n, &mL) != 2) return 2;
    lsz = malloc(mL * sizeof(int)); lpts = malloc(mL * sizeof(int *)); pdeg = calloc(n, sizeof(int));
    for (int j = 0; j < mL; j++) {
        if (fscanf(f, "%d", &lsz[j]) != 1) return 2;
        lpts[j] = malloc(lsz[j] * sizeof(int));
        for (int i = 0; i < lsz[j]; i++) { if (fscanf(f, "%d", &lpts[j][i]) != 1) return 2; pdeg[lpts[j][i]]++; }
    }
    plines = malloc(n * sizeof(int *)); int *fill = calloc(n, sizeof(int));
    for (int p = 0; p < n; p++) plines[p] = malloc(pdeg[p] * sizeof(int));
    for (int j = 0; j < mL; j++) for (int i = 0; i < lsz[j]; i++) { int p = lpts[j][i]; plines[p][fill[p]++] = j; }
    s = calloc(mL, sizeof(int)); w = calloc(n, sizeof(int)); tabu = calloc(n, sizeof(int));
    long total = (long)M * mL / pdeg[0];
    for (long t = 0; t < total;) { int p = rnd() % n; if (w[p] < WMAX && dinc(p) <= 1 + 2 * (long)pdeg[p]) { chg(p, 1); t++; } }
    long cost = 0; for (int j = 0; j < mL; j++) cost += (long)(s[j] - M) * (s[j] - M);
    long best = cost; double t0 = now(), tend = t0 + secs; long it = 0;
    int *cand = malloc(2 * n * sizeof(int)), *bad = malloc(mL * sizeof(int));
    while (cost > 0) {
        if ((it & 255) == 0 && now() > tend) break;
        it++;
        int nb = 0; for (int j = 0; j < mL; j++) if (s[j] > M) bad[nb++] = j;
        int L = bad[rnd() % nb];
        /* decrement: a weighted point on L with best ddec */
        long bd = 1L << 60; int nc = 0;
        for (int i = 0; i < lsz[L]; i++) { int p = lpts[L][i]; if (!w[p]) continue;
            long d = ddec(p) + (tabu[p] > it ? 1000 : 0);
            if (d < bd) { bd = d; nc = 0; } if (d == bd) cand[nc++] = p; }
        int p = cand[rnd() % nc];
        chg(p, -1);
        long bi = 1L << 60; nc = 0;
        for (int r = 0; r < n; r++) { if (r == p || w[r] >= WMAX) continue;
            long d = dinc(r) + (tabu[r] > it ? 1000 : 0);
            if (d < bi) { bi = d; nc = 0; } if (d == bi) cand[nc++] = r; }
        int r = cand[rnd() % nc];
        chg(r, 1);
        tabu[p] = it + 5 + rnd() % 10; tabu[r] = it + 5 + rnd() % 10;
        cost = 0; for (int j = 0; j < mL; j++) cost += (long)(s[j] - M) * (s[j] - M);
        if (cost < best) { best = cost; fprintf(stderr, "it %ld t %.1f best %ld\n", it, now() - t0, best); }
    }
    fprintf(stderr, "final cost %ld best %ld iters %ld time %.1f\n", cost, best, it, now() - t0);
    if (cost == 0) {
        FILE *o = argc > 6 ? fopen(argv[6], "w") : stdout;
        for (int q = 0; q < n; q++) if (w[q]) fprintf(o, "%d %d\n", q, w[q]);
        if (o != stdout) fclose(o);
        return 0;
    }
    return 1;
}
