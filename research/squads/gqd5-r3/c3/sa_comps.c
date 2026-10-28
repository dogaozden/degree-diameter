/* sa_comps.c: simulated annealing for the maximum weight packing of components (card r3c3).
   Components: singles (w=1, 10 lines) and non-S collinear pairs (w=2, 19 lines); a state is a family of components
   with pairwise disjoint line sets (owner[line] <= one component). A move picks a random component c outside the
   state, removes the components conflicting with it, adds c; accepted by Metropolis on the weight change.
   usage: sa_comps COMPS SEED ITERS_PER_CYCLE CYCLES T0 T1 OUT
   OUT receives the best point set (first line = size, then one point id per line). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>

static int nl, nc;
static int *w, *m, *loff, *lin, *k, *poff, *pts;
static int *owner, *inS, *mark, stamp = 1;
static int *Xl;
static unsigned long long rs;
static inline unsigned long long rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline double rndu(void) { return (rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int W_, cnt_;
static void addc(int c) {
    inS[c] = 1; W_ += w[c]; cnt_++;
    for (int i = 0; i < m[c]; i++) owner[lin[loff[c] + i]] = c;
}
static void remc(int c) {
    inS[c] = 0; W_ -= w[c]; cnt_--;
    for (int i = 0; i < m[c]; i++) { int l = lin[loff[c] + i]; if (owner[l] == c) owner[l] = -1; }
}

int main(int argc, char **argv) {
    if (argc < 8) { fprintf(stderr, "usage: sa_comps COMPS SEED ITERS CYCLES T0 T1 OUT\n"); return 1; }
    FILE *f = fopen(argv[1], "r"); if (!f) return 1;
    if (fscanf(f, "%d %d", &nl, &nc) != 2) return 1;
    w = malloc(nc * sizeof(int)); m = malloc(nc * sizeof(int)); loff = malloc(nc * sizeof(int));
    k = malloc(nc * sizeof(int)); poff = malloc(nc * sizeof(int));
    lin = malloc(sizeof(int) * nc * 19); pts = malloc(sizeof(int) * nc * 2);
    int lo = 0, po = 0;
    for (int c = 0; c < nc; c++) {
        if (fscanf(f, "%d %d", &w[c], &m[c]) != 2) return 1;
        loff[c] = lo;
        for (int i = 0; i < m[c]; i++) if (fscanf(f, "%d", &lin[lo++]) != 1) return 1;
        if (fscanf(f, "%d", &k[c]) != 1) return 1;
        poff[c] = po;
        for (int i = 0; i < k[c]; i++) if (fscanf(f, "%d", &pts[po++]) != 1) return 1;
    }
    fclose(f);
    owner = malloc(sizeof(int) * nl); inS = calloc(nc, sizeof(int)); mark = calloc(nc, sizeof(int));
    Xl = malloc(sizeof(int) * 1024);
    for (int l = 0; l < nl; l++) owner[l] = -1;
    rs = 88172645463325252ULL ^ (unsigned long long)atoll(argv[2]) * 2654435761ULL;
    long iters = atol(argv[3]); int cycles = atoi(argv[4]);
    double T0 = atof(argv[5]), T1 = atof(argv[6]);
    const char *out = argv[7];
    int bestW = -1; int *best = malloc(sizeof(int) * nc); int nbest = 0;
    for (int cy = 0; cy < cycles; cy++) {
        /* restart cycles from the empty state (keeps diversity); later cycles could start from best */
        for (int c = 0; c < nc; c++) if (inS[c]) remc(c);
        for (long it = 0; it < iters; it++) {
            double T = T0 * pow(T1 / T0, (double)it / (double)iters);
            int c = (int)(rnd64() % (unsigned long long)nc);
            if (inS[c]) continue;
            stamp++;
            int nx = 0, dw = 0;
            for (int i = 0; i < m[c]; i++) {
                int o = owner[lin[loff[c] + i]];
                if (o >= 0 && mark[o] != stamp) { mark[o] = stamp; Xl[nx++] = o; dw += w[o]; }
            }
            int delta = w[c] - dw;
            if (delta >= 0 || rndu() < exp(delta / T)) {
                for (int i = 0; i < nx; i++) remc(Xl[i]);
                addc(c);
                if (W_ > bestW) {
                    bestW = W_; nbest = 0;
                    for (int d = 0; d < nc; d++) if (inS[d]) best[nbest++] = d;
                    fprintf(stderr, "cycle %d it %ld W %d comps %d\n", cy, it, W_, cnt_);
                }
            }
        }
        fprintf(stderr, "end cycle %d: current W %d best %d\n", cy, W_, bestW);
    }
    /* expand best to points */
    int np = 0; int *P = malloc(sizeof(int) * 4096);
    for (int i = 0; i < nbest; i++) { int c = best[i]; for (int j = 0; j < k[c]; j++) P[np++] = pts[poff[c] + j]; }
    /* sort */
    for (int i = 1; i < np; i++) { int x = P[i], j = i - 1; while (j >= 0 && P[j] > x) { P[j + 1] = P[j]; j--; } P[j + 1] = x; }
    FILE *g = fopen(out, "w"); fprintf(g, "%d\n", np); for (int i = 0; i < np; i++) fprintf(g, "%d\n", P[i]); fclose(g);
    printf("BEST_W %d POINTS %d COMPS %d\n", bestW, np, nbest);
    return 0;
}
