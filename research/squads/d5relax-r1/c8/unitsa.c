/* unitsa.c (card c8, wildcard): simulated annealing over UNITS of W(q).

   A unit is a single point x (footprint: the q+1 lines through x) or a collinear pair {x,y} (footprint: the 2q+1
   lines through x or y; the line xy is counted once).  Weight: single 1, pair 2 (number of points covered).
   Claim: a set of units with pairwise disjoint footprints is a relaxed set, and every relaxed set arises this way.
   Proof sketch: two points of different units that share a line are collinear, so they would be a pair of one unit;
   conversely a point z collinear with x lies on a line through x, which is in the footprint of x's unit and of z's
   unit.  So the conflict relation is pairwise (no triple effects) and the problem is a weighted set packing of the
   1464 lines (q = 11) by pencils and pencil-pairs.

   State: owner[line] = unit owning it, or -1.  Move: propose a unit u (random point x, random option: one of its
   q(q+1) collinear partners, or the single), collect the distinct owners of u's footprint (at most 2q+1 units),
   delta = w(u) - sum of their weights, accept with Metropolis (delta >= 0 always).  Cost per proposal is ~2q+1 array
   reads, so tens of millions of proposals per second.  Constant-cycle exponential cooling with restarts.

   usage: unitsa LINESFILE q seconds seed OUT [T0 T1 CYCLE MODE]  (MODE 0: random units; 1: best option at a random uncovered point)
   OUT: rtabu format (number of points, then the points), rewritten at each improvement. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <time.h>
#include <stdint.h>

static int q, N, D, FS, P;
static int *pl, *lp, *nbr, *nline, *pidx, *pa, *pb, *pfoot;
static int *owner, *cov, *solList, *solPos, nSol, W;
static int *bestList, nBest, bestW;
static uint64_t rs = 0x9E3779B97F4A7C15ULL;
static inline uint64_t rnd64(void) {
    rs ^= rs >> 12; rs ^= rs << 25; rs ^= rs >> 27; return rs * 2685821657736338717ULL;
}

static inline const int *foot(int u, int *fs) {
    if (u < N) { *fs = q + 1; return &pl[u * (q + 1)]; }
    *fs = FS; return &pfoot[(u - N) * FS];
}
static inline int wt(int u) { return u < N ? 1 : 2; }

static void insertU(int u) {
    int fs; const int *F = foot(u, &fs);
    for (int i = 0; i < fs; i++) owner[F[i]] = u;
    if (u < N) cov[u] = u; else { cov[pa[u - N]] = u; cov[pb[u - N]] = u; }
    solPos[u] = nSol; solList[nSol++] = u; W += wt(u);
}
static void removeU(int u) {
    int fs; const int *F = foot(u, &fs);
    for (int i = 0; i < fs; i++) owner[F[i]] = -1;
    if (u < N) cov[u] = -1; else { cov[pa[u - N]] = -1; cov[pb[u - N]] = -1; }
    int p = solPos[u], last = solList[--nSol];
    solList[p] = last; solPos[last] = p; solPos[u] = -1; W -= wt(u);
}

static void writeSet(const char *fn, const int *units, int nu) {
    int npts = 0;
    for (int i = 0; i < nu; i++) npts += wt(units[i]);
    FILE *o = fopen(fn, "w"); if (!o) return;
    fprintf(o, "%d\n", npts);
    for (int i = 0; i < nu; i++) {
        int u = units[i];
        if (u < N) fprintf(o, "%d\n", u);
        else fprintf(o, "%d\n%d\n", pa[u - N], pb[u - N]);
    }
    fclose(o);
}

/* independent check: every point of T has at most one collinear neighbour in T */
static int checkRelaxed(const int *units, int nu) {
    char *inT = calloc(N, 1);
    int npts = 0;
    for (int i = 0; i < nu; i++) {
        int u = units[i];
        if (u < N) { inT[u] = 1; npts++; }
        else { inT[pa[u - N]] = 1; inT[pb[u - N]] = 1; npts += 2; }
    }
    int ok = 1;
    for (int x = 0; x < N && ok; x++) if (inT[x]) {
        int c = 0;
        for (int k = 0; k < D; k++) if (inT[nbr[x * D + k]]) c++;
        if (c > 1) ok = 0;
    }
    free(inT);
    return ok ? npts : -1;
}

/* weight change if unit u is inserted and its conflicting units removed; fills conf[] with the conflicts */
static int evalU(int u, int *conf, int *ncp) {
    int fs; const int *F = foot(u, &fs);
    int nc = 0, delta = wt(u);
    for (int i = 0; i < fs; i++) {
        int o = owner[F[i]];
        if (o >= 0) {
            int seen = 0;
            for (int c = 0; c < nc; c++) if (conf[c] == o) { seen = 1; break; }
            if (!seen) { conf[nc++] = o; delta -= wt(o); }
        }
    }
    *ncp = nc;
    return delta;
}

int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: unitsa LINESFILE q seconds seed OUT [T0 T1 CYCLE MODE]  (MODE 0: random units; 1: best option at a random uncovered point)\n"); return 1; }
    q = atoi(argv[2]);
    double secs = atof(argv[3]);
    rs ^= (uint64_t)atoll(argv[4]) * 0xD1B54A32D192ED03ULL; for (int i = 0; i < 20; i++) rnd64();
    const char *outf = argv[5];
    double T0 = 0.5, T1 = 0.1; long cyc = 4000000; int mode = 0;
    if (argc > 6) T0 = atof(argv[6]);
    if (argc > 7) T1 = atof(argv[7]);
    if (argc > 8) cyc = atol(argv[8]);
    if (argc > 9) mode = atoi(argv[9]);

    FILE *f = fopen(argv[1], "r");
    if (!f) { fprintf(stderr, "cannot open %s\n", argv[1]); return 1; }
    int L; if (fscanf(f, "%d", &L) != 1) return 1;
    N = L; D = q * (q + 1); FS = 2 * q + 1;
    if (N != (q + 1) * (q * q + 1)) { fprintf(stderr, "bad line count\n"); return 1; }
    lp = malloc(sizeof(int) * N * (q + 1));
    for (int l = 0; l < L; l++) for (int i = 0; i < q + 1; i++) if (fscanf(f, "%d", &lp[l * (q + 1) + i]) != 1) return 1;
    fclose(f);

    /* lines through each point */
    pl = malloc(sizeof(int) * N * (q + 1));
    int *cnt = calloc(N, sizeof(int));
    for (int l = 0; l < L; l++) for (int i = 0; i < q + 1; i++) {
        int x = lp[l * (q + 1) + i];
        pl[x * (q + 1) + cnt[x]++] = l;
    }
    for (int x = 0; x < N; x++) if (cnt[x] != q + 1) { fprintf(stderr, "point %d on %d lines\n", x, cnt[x]); return 1; }

    /* collinear partners with the shared line */
    nbr = malloc(sizeof(int) * N * D); nline = malloc(sizeof(int) * N * D);
    for (int x = 0; x < N; x++) {
        int c = 0;
        for (int i = 0; i < q + 1; i++) {
            int l = pl[x * (q + 1) + i];
            for (int j = 0; j < q + 1; j++) {
                int y = lp[l * (q + 1) + j];
                if (y != x) { nbr[x * D + c] = y; nline[x * D + c] = l; c++; }
            }
        }
        if (c != D) { fprintf(stderr, "degree %d at %d\n", c, x); return 1; }
    }

    /* pair units: index p for every unordered collinear pair */
    int Pmax = N * D / 2;
    pa = malloc(sizeof(int) * Pmax); pb = malloc(sizeof(int) * Pmax);
    pfoot = malloc(sizeof(int) * (size_t)Pmax * FS);
    pidx = malloc(sizeof(int) * N * D);
    P = 0;
    for (int x = 0; x < N; x++) for (int k = 0; k < D; k++) {
        int y = nbr[x * D + k];
        if (x < y) {
            int p = P++;
            pa[p] = x; pb[p] = y; pidx[x * D + k] = p;
            int *F = &pfoot[(size_t)p * FS]; int m = 0, sh = nline[x * D + k];
            for (int i = 0; i < q + 1; i++) F[m++] = pl[x * (q + 1) + i];
            for (int i = 0; i < q + 1; i++) if (pl[y * (q + 1) + i] != sh) F[m++] = pl[y * (q + 1) + i];
            if (m != FS) { fprintf(stderr, "footprint %d\n", m); return 1; }
        }
    }
    for (int x = 0; x < N; x++) for (int k = 0; k < D; k++) {
        int y = nbr[x * D + k];
        if (x > y) {
            for (int kk = 0; kk < D; kk++) if (nbr[y * D + kk] == x) { pidx[x * D + k] = pidx[y * D + kk]; break; }
        }
    }
    if (P != Pmax) { fprintf(stderr, "pair count %d\n", P); return 1; }

    owner = malloc(sizeof(int) * L); for (int l = 0; l < L; l++) owner[l] = -1;
    cov = malloc(sizeof(int) * N); for (int x = 0; x < N; x++) cov[x] = -1;
    int nUnits = N + P;
    solPos = malloc(sizeof(int) * nUnits); for (int u = 0; u < nUnits; u++) solPos[u] = -1;
    solList = malloc(sizeof(int) * N); bestList = malloc(sizeof(int) * N);
    nSol = 0; W = 0; nBest = 0; bestW = 0;

    clock_t t0 = clock();
    long it = 0, lastImp = 0;
    double T = T0;
    uint32_t acc[64];
    int conf[64];
    while (1) {
        if ((it & 0xFFFF) == 0 && (double)(clock() - t0) / CLOCKS_PER_SEC > secs) break;
        if ((it & 0xFFF) == 0) {
            double ph = (double)(it % cyc) / (double)cyc;
            T = T0 * pow(T1 / T0, ph);
            for (int k = 0; k < 64; k++) { double a = exp(-(double)k / T) * 4294967295.0; acc[k] = (uint32_t)a; }
        }
        it++;
        int u, nc = 0, delta = 0;
        if (mode == 0) {
            int x = (int)(rnd64() % N);
            int j = (int)(rnd64() % (D + 1));
            u = (j < D) ? N + pidx[x * D + j] : x;
            if (solPos[u] >= 0) continue;
            delta = evalU(u, conf, &nc);
        } else {
            /* anchored: pick an uncovered point a, evaluate its q(q+1)+1 options, keep the best (random ties) */
            int a = (int)(rnd64() % N);
            if (cov[a] >= 0) continue;
            int bestd = -1000, nties = 0, bu = -1, bnc = 0, bconf[64];
            for (int j = 0; j <= D; j++) {
                int v = (j < D) ? N + pidx[a * D + j] : a;
                int cc = 0, dd = evalU(v, conf, &cc);
                if (dd > bestd) { bestd = dd; nties = 1; bu = v; bnc = cc; memcpy(bconf, conf, sizeof(int) * cc); }
                else if (dd == bestd && (rnd64() % (++nties)) == 0) { bu = v; bnc = cc; memcpy(bconf, conf, sizeof(int) * cc); }
            }
            u = bu; nc = bnc; delta = bestd; memcpy(conf, bconf, sizeof(int) * bnc);
        }
        if (delta >= 0 || (uint32_t)rnd64() < acc[-delta]) {
            for (int c = 0; c < nc; c++) removeU(conf[c]);
            insertU(u);
            if (W > bestW) {
                bestW = W; nBest = nSol; memcpy(bestList, solList, sizeof(int) * nSol);
                writeSet(outf, bestList, nBest); lastImp = it;
                fprintf(stderr, "size %d at it %ld, %.1f s, T=%.3f\n", bestW, it,
                        (double)(clock() - t0) / CLOCKS_PER_SEC, T);
            }
        }
    }
    int chk = checkRelaxed(bestList, nBest);
    printf("best %d (units %d) iterations %ld, %.1f s, last improvement at it %ld, valid-check %d\n", bestW, nBest,
           it, (double)(clock() - t0) / CLOCKS_PER_SEC, lastImp, chk);
    return 0;
}
