/* ctrl2.c: two-orbit controllers, i.e. voltage lifts of a 2+2 base multigraph (card C3 of squad r1-165).

   Base multigraph: A-vertices a0 (id 0), a1 (id 1); B-vertices b0 (id 2), b1 (id 3); every vertex has degree 4.
   Edge multiplicities  mult(a0,b0) = k, mult(a0,b1) = 4-k, mult(a1,b0) = 4-k, mult(a1,b1) = k,  k in {1,2,3}.
   (k = 1 and k = 3 are isomorphic: swap b0 and b1.)  Each base edge e gets a voltage v_e in the group G.
   Lift (controller): (a_i, g) ~ (b_j, v_e g) for each base edge e = a_i b_j.  So m = 2|G| vertices per side.
   Gauge: the spanning tree a0b0#0, a0b1#0, a1b0#0 gets the identity; the 5 other edges are free.
   Parallel base edges must get distinct voltages (else the lift has multi-edges): such assignments are skipped.

   Exact-NB-4 coverage: for each of the four base vertices s (as source at the identity), every same-side pair
   (target base vertex p, element h) must be the endpoint of a nonbacktracking walk of length 4 from (s,1).
   A walk is a base-edge sequence e1 e2 e3 e4 with consecutive edges distinct.  Words (group products):
     A source: h = v4^-1 v3 v2^-1 v1 ;   B source: h = v4 v3^-1 v2 v1^-1.
   Cost = number of uncovered (source, target) pairs, 0..8|G|.  Right multiplication by G is an automorphism of the
   lift, which is why the identity source suffices.

   Group table TABLE (same as squad165 dump_table.py): first line n, then n*n ints, entry [i*n+j] = index of i*j.

   usage:
     ctrl2 TABLE k exh [maxprint]                 exhaustive over the 5 free voltages (prints best cost, zero count)
     ctrl2 TABLE k sa SECS SEED [T0] [nseg]       simulated annealing, nseg random restarts, stops at cost 0
     ctrl2 TABLE k eval v0 v1 v2 v3 v4            cost of one assignment of the 5 free voltages (in edge order fr[])
     ctrl2 TABLE k emit v0 v1 v2 v3 v4 OUT        write the controller edge list "a b" (a = i*n+g, b = j*n+h)
   build: gcc -O3 -march=native -o ctrl2 ctrl2.c -lm */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <time.h>
#include <stdint.h>

static int n, *T, *Inv, E0;
static int ua[8], ub[8];          /* base edge e joins A-vertex ua[e] in {0,1} and B-vertex ub[e] in {2,3} */
static int tr[8], fidx[8], fr[5]; /* tree edges (voltage identity); free edges and their index 0..4 */
static int npar, parp[32][2];     /* pairs of parallel base edges: voltages must differ */
static int inc[4][4];             /* the 4 base edges at each base vertex */
static int NW, wS[432], wE[432][4], wT[432];

static inline int mul(int x, int y) { return T[x * n + y]; }
static inline int other(int e, int v) { return v == ua[e] ? ub[e] : ua[e]; }

static void setup_base(int k) {
    int mult[2][2] = { { k, 4 - k }, { 4 - k, k } };
    int e = 0, nf = 0;
    for (int i = 0; i < 2; i++) for (int j = 0; j < 2; j++)
        for (int c = 0; c < mult[i][j]; c++) {
            ua[e] = i; ub[e] = 2 + j;
            tr[e] = (c == 0 && !(i == 1 && j == 1));
            fidx[e] = -1;
            if (!tr[e]) { fidx[e] = nf; fr[nf++] = e; }
            e++;
        }
    if (e != 8 || nf != 5) { fprintf(stderr, "bad base k=%d\n", k); exit(1); }
    int ic[4] = { 0, 0, 0, 0 };
    for (e = 0; e < 8; e++) { inc[ua[e]][ic[ua[e]]++] = e; inc[ub[e]][ic[ub[e]]++] = e; }
    npar = 0;
    for (int e1 = 0; e1 < 8; e1++) for (int e2 = e1 + 1; e2 < 8; e2++)
        if (ua[e1] == ua[e2] && ub[e1] == ub[e2]) { parp[npar][0] = e1; parp[npar][1] = e2; npar++; }
}

/* all 432 = 4 * 108 nonbacktracking walks of length 4 (from the 4 base vertices) */
static void build_walks(void) {
    NW = 0;
    for (int s = 0; s < 4; s++)
    for (int a = 0; a < 4; a++) {
        int e1 = inc[s][a], u1 = other(e1, s);
        for (int b = 0; b < 4; b++) { int e2 = inc[u1][b]; if (e2 == e1) continue; int u2 = other(e2, u1);
        for (int c = 0; c < 4; c++) { int e3 = inc[u2][c]; if (e3 == e2) continue; int u3 = other(e3, u2);
        for (int d = 0; d < 4; d++) { int e4 = inc[u3][d]; if (e4 == e3) continue; int u4 = other(e4, u3);
            wS[NW] = s; wE[NW][0] = e1; wE[NW][1] = e2; wE[NW][2] = e3; wE[NW][3] = e4; wT[NW] = u4; NW++;
        }}}
    }
    if (NW != 432) { fprintf(stderr, "NW=%d\n", NW); exit(1); }
}

static void fill(const int *var, int *vol) { for (int e = 0; e < 8; e++) vol[e] = tr[e] ? E0 : var[fidx[e]]; }
static int valid(const int *vol) { for (int p = 0; p < npar; p++) if (vol[parp[p][0]] == vol[parp[p][1]]) return 0; return 1; }

/* number of uncovered (source, same-side target) pairs; cov index = (source*2 + targetside)*n + element */
static int cost_vol(const int *vol) {
    int v[8], vi[8];
    static unsigned char cov[8 * 128];
    for (int e = 0; e < 8; e++) { v[e] = vol[e]; vi[e] = Inv[vol[e]]; }
    memset(cov, 0, 8 * n);
    for (int w = 0; w < NW; w++) {
        int e1 = wE[w][0], e2 = wE[w][1], e3 = wE[w][2], e4 = wE[w][3], g;
        if (wS[w] < 2) g = mul(mul(mul(vi[e4], v[e3]), vi[e2]), v[e1]);     /* A source */
        else           g = mul(mul(mul(v[e4], vi[e3]), v[e2]), vi[e1]);     /* B source */
        cov[(wS[w] * 2 + (wT[w] & 1)) * n + g] = 1;
    }
    int c = 0;
    for (int i = 0; i < 8 * n; i++) c += !cov[i];
    return c;
}

static void run_exh(int maxprint) {
    int var[5], vol[8], bestvar[5] = { 0, 0, 0, 0, 0 };
    long tried = 0, nz = 0, hist[16] = { 0 };
    int best = 1 << 30;
    for (var[0] = 0; var[0] < n; var[0]++) for (var[1] = 0; var[1] < n; var[1]++)
    for (var[2] = 0; var[2] < n; var[2]++) for (var[3] = 0; var[3] < n; var[3]++)
    for (var[4] = 0; var[4] < n; var[4]++) {
        fill(var, vol);
        if (!valid(vol)) continue;
        int c = cost_vol(vol);
        tried++;
        if (c < 16) hist[c]++;
        if (c < best) { best = c; memcpy(bestvar, var, sizeof var); }
        if (c == 0) {
            nz++;
            if (nz <= maxprint) printf("SOL0 %d %d %d %d %d\n", var[0], var[1], var[2], var[3], var[4]);
        }
    }
    printf("exh n=%d k=? tried=%ld best_cost=%d zero_count=%ld best_vars=%d %d %d %d %d\n",
           n, tried, best, nz, bestvar[0], bestvar[1], bestvar[2], bestvar[3], bestvar[4]);
    printf("hist(cost:count):");
    for (int c = 0; c < 16; c++) if (hist[c]) printf(" %d:%ld", c, hist[c]);
    printf("\n");
}

static uint64_t rs = 88172645463325252ULL;
static inline uint64_t xr(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline double urand(void) { return (double)(xr() >> 11) * (1.0 / 9007199254740992.0); }

static void run_sa(double secs, uint64_t seed, double T0, int nseg) {
    rs ^= seed * 0x9E3779B97F4A7C15ULL;
    for (int i = 0; i < 20; i++) xr();
    int var[5], vol[8], bestvar[5] = { 0, 0, 0, 0, 0 };
    int best = 1 << 30, c, c2;
    double seg = secs / nseg, T = T0;
    for (int s = 0; s < nseg && best > 0; s++) {
        do { for (int i = 0; i < 5; i++) var[i] = (int)(xr() % n); fill(var, vol); } while (!valid(vol));
        c = cost_vol(vol);
        clock_t t0 = clock();
        long it = 0;
        for (;;) {
            if ((it & 1023) == 0) {
                double el = (double)(clock() - t0) / CLOCKS_PER_SEC;
                if (el >= seg) break;
                double frac = el / seg;
                T = T0 * pow(0.05 / T0, frac);
            }
            it++;
            int i = (int)(xr() % 5), old = var[i];
            int nv = (int)(xr() % n);
            if (nv == old) continue;
            var[i] = nv; fill(var, vol);
            if (!valid(vol)) { var[i] = old; continue; }
            c2 = cost_vol(vol);
            if (c2 <= c || urand() < exp((double)(c - c2) / T)) {
                c = c2;
                if (c < best) { best = c; memcpy(bestvar, var, sizeof var); if (best == 0) break; }
            } else var[i] = old;
        }
    }
    printf("sa n=%d best_cost=%d best_vars=%d %d %d %d %d\n", n, best,
           bestvar[0], bestvar[1], bestvar[2], bestvar[3], bestvar[4]);
}

static void emit(const int *var, const char *path) {
    int vol[8];
    fill(var, vol);
    FILE *f = fopen(path, "w");
    if (!f) { perror(path); exit(1); }
    for (int i = 0; i < 2; i++) for (int g = 0; g < n; g++) for (int c = 0; c < 4; c++) {
        int e = inc[i][c], j = ub[e] - 2, h = mul(vol[e], g);
        fprintf(f, "%d %d\n", i * n + g, j * n + h);
    }
    fclose(f);
}

int main(int argc, char **argv) {
    if (argc < 4) { fprintf(stderr, "usage: ctrl2 TABLE k exh|sa|eval|emit ...\n"); return 1; }
    FILE *f = fopen(argv[1], "r");
    if (!f) { perror(argv[1]); return 2; }
    int k = atoi(argv[2]);
    const char *mode = argv[3];
    if (fscanf(f, "%d", &n) != 1 || n > 128) return 2;
    T = malloc(sizeof(int) * n * n);
    Inv = malloc(sizeof(int) * n);
    for (int i = 0; i < n * n; i++) if (fscanf(f, "%d", &T[i]) != 1) return 3;
    fclose(f);
    E0 = -1;
    for (int i = 0; i < n; i++) { int ok = 1; for (int j = 0; j < n && ok; j++) if (T[i * n + j] != j) ok = 0; if (ok) E0 = i; }
    for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) if (T[i * n + j] == E0) Inv[i] = j;
    setup_base(k);
    build_walks();
    if (!strcmp(mode, "exh")) {
        run_exh(argc > 4 ? atoi(argv[4]) : 5);
    } else if (!strcmp(mode, "sa")) {
        if (argc < 6) { fprintf(stderr, "sa needs SECS SEED\n"); return 1; }
        run_sa(atof(argv[4]), (uint64_t)atoll(argv[5]), argc > 6 ? atof(argv[6]) : 2.0, argc > 7 ? atoi(argv[7]) : 4);
    } else if (!strcmp(mode, "eval") || !strcmp(mode, "emit")) {
        int var[5], vol[8];
        if (argc < 9) { fprintf(stderr, "need 5 free voltages\n"); return 1; }
        for (int i = 0; i < 5; i++) var[i] = atoi(argv[4 + i]);
        fill(var, vol);
        if (!strcmp(mode, "eval")) printf("cost %d valid %d\n", cost_vol(vol), valid(vol));
        else { if (argc < 10) { fprintf(stderr, "emit needs OUT\n"); return 1; } emit(var, argv[9]); printf("wrote %s valid %d cost %d\n", argv[9], valid(vol), cost_vol(vol)); }
    } else {
        fprintf(stderr, "unknown mode %s\n", mode);
        return 1;
    }
    return 0;
}
