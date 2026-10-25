/* c2solve.c: search over Z3 values of H-orbit variables for a covering cocycle on W(7).
   input fam.txt: "k nrep", then nrep lines "w v0 c0 v1 c1 ... v31 c31": the 8 geodesics of one pair-orbit
   representative, 4 (variable, coefficient) terms each; voltage of geodesic = sum c * x[v] mod 3.
   w = orbit size.  Cost = sum_w * (number of missing Z3 values), i.e. the zcov cost of the expanded labelling.
   usage: c2solve fam.txt mode secs seed outc [T0 T1]
     mode 0: exhaustive (x[0] in {0,1} by the sign symmetry x -> -x, others in Z3)
     mode 1: simulated annealing for secs seconds (single-variable moves, incremental update)
   prints: RESULT k=.. nrep=.. best=.. iters=.. ; writes best assignment (k ints) to outc. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <time.h>
#include <stdint.h>
#include <limits.h>

static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline double urand(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int k, nrep;
static long *w;
static int *var, *coef; /* nrep*32 */

static long eval_full(const int *x, long limit) {
    long cost = 0;
    for (int r = 0; r < nrep; r++) {
        int seen = 0;
        for (int g = 0; g < 8; g++) {
            int s = 0;
            const int *vv = var + r * 32 + g * 4, *cc = coef + r * 32 + g * 4;
            for (int j = 0; j < 4; j++) s += cc[j] * x[vv[j]];
            s %= 3; if (s < 0) s += 3;
            seen |= 1 << s;
        }
        cost += w[r] * (3 - __builtin_popcount(seen));
        if (cost >= limit) return cost;
    }
    return cost;
}

static int *cnt3; /* nrep*3 */
static int *volt; /* nrep*8 */
static inline int missr(int r) { return (cnt3[3 * r] == 0) + (cnt3[3 * r + 1] == 0) + (cnt3[3 * r + 2] == 0); }

int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: c2solve fam.txt mode secs seed outc [T0 T1]\n"); return 1; }
    FILE *f = fopen(argv[1], "r");
    if (!f || fscanf(f, "%d %d", &k, &nrep) != 2) { fprintf(stderr, "bad family file\n"); return 1; }
    int mode = atoi(argv[2]); double secs = atof(argv[3]);
    rs ^= (uint64_t)atoll(argv[4]) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 20; i++) rnd();
    w = malloc(sizeof(long) * nrep); var = malloc(sizeof(int) * nrep * 32); coef = malloc(sizeof(int) * nrep * 32);
    double wsum = 0;
    for (int r = 0; r < nrep; r++) {
        if (fscanf(f, "%ld", &w[r]) != 1) { fprintf(stderr, "short family\n"); return 1; }
        wsum += w[r];
        for (int j = 0; j < 32; j++) if (fscanf(f, "%d %d", &var[r * 32 + j], &coef[r * 32 + j]) != 2) { fprintf(stderr, "short family\n"); return 1; }
    }
    fclose(f);
    int *x = calloc(k > 0 ? k : 1, sizeof(int));
    int *bestx = calloc(k > 0 ? k : 1, sizeof(int));
    long best = LONG_MAX, iters = 0;
    if (mode == 0) {
        long total = 2; for (int i = 1; i < k; i++) total *= 3;
        for (long idx = 0; idx < total; idx++) {
            long t = idx; x[0] = (k > 0) ? (int)(t % 2) : 0; t /= 2;
            for (int i = 1; i < k; i++) { x[i] = (int)(t % 3); t /= 3; }
            long cost = eval_full(x, best);
            iters++;
            if (cost < best) { best = cost; memcpy(bestx, x, sizeof(int) * k); if (best == 0) break; }
        }
    } else {
        double wavg = wsum / nrep;
        double T0 = argc > 6 ? atof(argv[6]) : 1.0 * wavg, T1 = argc > 7 ? atof(argv[7]) : 0.05 * wavg;
        /* random start */
        for (int i = 0; i < k; i++) x[i] = rnd() % 3;
        cnt3 = calloc(nrep * 3, sizeof(int)); volt = malloc(sizeof(int) * nrep * 8);
        for (int r = 0; r < nrep; r++) for (int g = 0; g < 8; g++) {
            int s = 0;
            for (int j = 0; j < 4; j++) s += coef[r * 32 + g * 4 + j] * x[var[r * 32 + g * 4 + j]];
            s %= 3; if (s < 0) s += 3;
            volt[r * 8 + g] = s; cnt3[r * 3 + s]++;
        }
        /* incidence lists per variable (entries with coef != 0) */
        int *ioff = calloc(k + 1, sizeof(int));
        for (int e = 0; e < nrep * 32; e++) if (coef[e]) ioff[var[e] + 1]++;
        for (int i = 0; i < k; i++) ioff[i + 1] += ioff[i];
        int *fill = calloc(k + 1, sizeof(int)); int *ilist = malloc(sizeof(int) * (ioff[k] + 1));
        for (int e = 0; e < nrep * 32; e++) if (coef[e]) { int v = var[e]; ilist[ioff[v] + fill[v]++] = e; }
        long cost = 0;
        for (int r = 0; r < nrep; r++) cost += w[r] * missr(r);
        best = cost; memcpy(bestx, x, sizeof(int) * k);
        int *undo = malloc(sizeof(int) * 3 * (1 << 16)); /* (geo, old, new) triples; grows if needed */
        int ucap = 1 << 16;
        clock_t t0 = clock(); double T = T0;
        while (best > 0) {
            if ((iters & 1023) == 0) {
                double el = (double)(clock() - t0) / CLOCKS_PER_SEC;
                if (el > secs) break;
                T = T0 * pow(T1 / T0, el / secs);
            }
            iters++;
            int xv = rnd() % k; int d = 1 + (int)(rnd() % 2);
            long dc = 0; int nu = 0;
            for (int t = ioff[xv]; t < ioff[xv + 1]; t++) {
                int e = ilist[t]; int r = e / 32; int geo = e / 4;
                int old = volt[geo]; int nw = (old + coef[e] * d) % 3; if (nw < 0) nw += 3;
                if (nw == old) continue;
                int m0 = missr(r);
                cnt3[r * 3 + old]--; cnt3[r * 3 + nw]++; volt[geo] = nw;
                int m1 = missr(r);
                dc += w[r] * (m1 - m0);
                if (nu + 1 >= ucap) { ucap *= 2; undo = realloc(undo, sizeof(int) * 3 * ucap); }
                undo[3 * nu] = geo; undo[3 * nu + 1] = old; undo[3 * nu + 2] = nw; nu++;
            }
            if (dc <= 0 || urand() < exp(-(double)dc / T)) {
                x[xv] = (x[xv] + d) % 3; cost += dc;
                if (cost < best) { best = cost; memcpy(bestx, x, sizeof(int) * k); }
            } else {
                for (int u = nu - 1; u >= 0; u--) {
                    int geo = undo[3 * u], old = undo[3 * u + 1], nw = undo[3 * u + 2]; int r = geo / 8;
                    cnt3[r * 3 + nw]--; cnt3[r * 3 + old]++; volt[geo] = old;
                }
            }
        }
        /* sanity: recompute exact cost of best */
        long chk = eval_full(bestx, LONG_MAX);
        if (chk != best) { fprintf(stderr, "internal mismatch best=%ld chk=%ld\n", best, chk); best = chk; }
    }
    printf("RESULT k=%d nrep=%d best=%ld iters=%ld mode=%d\n", k, nrep, best, iters, mode);
    FILE *g = fopen(argv[5], "w");
    if (g) { for (int i = 0; i < k; i++) fprintf(g, "%d\n", bestx[i]); fclose(g); }
    return 0;
}
