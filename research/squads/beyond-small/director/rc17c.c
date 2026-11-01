/* rc17c: rc17 for an explicit controller edge list (mlift_chart output: lines "a b colour", A-vertex (a_i,g) = i*N+g,
 * B-vertex (b_j,h) = j*N+h). letter = PERM[colour]. Edges whose letter is XL get a 5th translation vector, one per
 * Z_N edge orbit (i, j, h-g). usage: rc17c CHART CTRL N "p0 p1 p2 p3" XL SEED STEPS [STATEIN] [STATEOUT] [EDGESOUT]
 * Derived from: rc17: route-chart lifts with extra translation vectors (degree 5+4+4+4 = 17), exact cost, annealing.
 *
 * Controller: Z_N voltage lift of a bipartite base multigraph (nb + nb vertices, every base vertex has exactly one edge
 * of each letter 0..3). Fibre F4^4 (256 points). Lift edge for base edge e = (i, j, v, c):
 *   ((a_i, g), x) ~ ((b_j, g + v), A_c x + w),  w in W_e = {lam b_c : lam in F4}  (+ {X_e} if e is "extended").
 * Extended base edges must form a perfect matching of the base, so the lift is 17-regular.
 * Cost = number of (source, target) pairs at distance > 5 (same-side > 4), sources = one controller vertex per base vertex
 * (g = 0) times all 256 fibre points. g -> g+1 is an automorphism, so cost 0 <=> diameter <= 5.
 *
 * usage: rc17 CHART BASE N SEED STEPS [T0] [STATEIN] [STATEOUT] [EDGESOUT]
 *   CHART: chart_u8.txt format (A_0..A_3 as 16 numbers row-major, then b_0..b_3).
 *   BASE:  first line nb m, then m lines "i j v c ext" (v = initial voltage, ext = 1 if extended).
 *   STATE file: m voltages, then for each extended edge its X (as an id 0..255).
 *   STEPS = 0: just evaluate (and write edges if EDGESOUT given).
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>

static int MUL[4][4] = {{0,0,0,0},{0,1,2,3},{0,2,3,1},{0,3,1,2}};
static int A[4][4][4], Bv[4][4];
static int AX[4][256];          /* A_c applied to vector id */
static int LB[4][4];            /* lam * b_c as id */
static int nb, m, N;
static int Ei[64], Ej[64], Ev[64], Ec[64], Ex[64], Xv[64];
static long n, nA;
static long *st; static int *adj;   /* CSR */
static uint64_t *vis, *fr, *nx;

static int vid(int *v) { return v[0] | (v[1] << 2) | (v[2] << 4) | (v[3] << 6); }
static void unid(int id, int *v) { for (int k = 0; k < 4; k++) v[k] = (id >> (2 * k)) & 3; }

static void prep_chart(void) {
    for (int c = 0; c < 4; c++) {
        for (int id = 0; id < 256; id++) {
            int x[4], y[4]; unid(id, x);
            for (int r = 0; r < 4; r++) { int s = 0; for (int k = 0; k < 4; k++) s ^= MUL[A[c][r][k]][x[k]]; y[r] = s; }
            AX[c][id] = vid(y);
        }
        for (int l = 0; l < 4; l++) { int y[4]; for (int k = 0; k < 4; k++) y[k] = MUL[l][Bv[c][k]]; LB[c][l] = vid(y); }
    }
}

static int deg_of(int e) { return 4 + (Ex[e] ? 1 : 0); }

static void build(void) {
    nA = (long)nb * N * 256; n = 2 * nA;
    long *dg = calloc(n + 1, sizeof(long));
    for (int e = 0; e < m; e++) {
        int d = deg_of(e);
        for (int g = 0; g < N; g++) for (int x = 0; x < 256; x++) {
            long a = ((long)Ei[e] * N + g) * 256 + x; dg[a] += d;
        }
        for (int h = 0; h < N; h++) for (int y = 0; y < 256; y++) {
            long b = nA + ((long)Ej[e] * N + h) * 256 + y; dg[b] += d;
        }
    }
    if (!st) { st = malloc((n + 1) * sizeof(long)); }
    st[0] = 0; for (long i = 0; i < n; i++) st[i + 1] = st[i] + dg[i];
    if (!adj) adj = malloc(st[n] * sizeof(int));
    long *pos = dg; for (long i = 0; i < n; i++) pos[i] = st[i];
    for (int e = 0; e < m; e++) {
        int c = Ec[e];
        for (int g = 0; g < N; g++) {
            long ca = (long)Ei[e] * N + g, cb = (long)Ej[e] * N + ((g + Ev[e]) % N);
            for (int x = 0; x < 256; x++) {
                long a = ca * 256 + x; int ax = AX[c][x];
                for (int l = 0; l < 4; l++) { long b = nA + cb * 256 + (ax ^ LB[c][l]); adj[pos[a]++] = (int)b; adj[pos[b]++] = (int)a; }
                if (Ex[e]) { long b = nA + cb * 256 + (ax ^ Xv[e]); adj[pos[a]++] = (int)b; adj[pos[b]++] = (int)a; }
            }
        }
    }
    free(dg);
}

/* exact cost: far pairs from the sources */
static long cost(long cap) {
    long far = 0;
    long nsrc = 2L * nb * 256;
    for (long k0 = 0; k0 < nsrc; k0 += 64) {
        memset(vis, 0, n * 8); memset(fr, 0, n * 8);
        int ns = (nsrc - k0 < 64) ? (int)(nsrc - k0) : 64;
        for (int k = 0; k < ns; k++) {
            long s = k0 + k; long side = s / ((long)nb * 256), r = s % ((long)nb * 256);
            long bi = r / 256, x = r % 256;
            long v = side * nA + (bi * N + 0) * 256 + x;
            vis[v] |= 1ULL << k; fr[v] |= 1ULL << k;
        }
        for (int lev = 0; lev < 5; lev++) {
            for (long x = 0; x < n; x++) {
                uint64_t acc = 0; for (long i = st[x]; i < st[x + 1]; i++) acc |= fr[adj[i]];
                acc &= ~vis[x]; nx[x] = acc;
            }
            for (long x = 0; x < n; x++) vis[x] |= nx[x];
            uint64_t *t = fr; fr = nx; nx = t;
        }
        uint64_t full = ns == 64 ? ~0ULL : ((1ULL << ns) - 1);
        for (long x = 0; x < n; x++) far += __builtin_popcountll(full & ~vis[x]);
        if (far >= cap) return far;
    }
    return far;
}

static unsigned long long rs;
static unsigned rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return (unsigned)(rs >> 11); }
static double urand(void) { return (rnd() & 0xffffff) / 16777216.0; }

static void save_state(const char *fn, long c) {
    FILE *f = fopen(fn, "w"); if (!f) return;
    fprintf(f, "# N %d cost %ld\n", N, c);
    for (int e = 0; e < m; e++) fprintf(f, "%d ", Ev[e]); fprintf(f, "\n");
    for (int e = 0; e < m; e++) if (Ex[e]) fprintf(f, "%d ", Xv[e]); fprintf(f, "\n");
    fclose(f);
}
static int load_state(const char *fn) {
    FILE *f = fopen(fn, "r"); if (!f) return 0;
    char line[4096]; if (!fgets(line, sizeof line, f)) return 0;
    if (line[0] != '#') { fclose(f); return 0; }
    for (int e = 0; e < m; e++) if (fscanf(f, "%d", &Ev[e]) != 1) return 0;
    for (int e = 0; e < m; e++) if (Ex[e]) if (fscanf(f, "%d", &Xv[e]) != 1) return 0;
    fclose(f); return 1;
}

int main(int argc, char **argv) {
    if (argc < 8) { fprintf(stderr, "usage: rc17c CHART CTRL N PERM XL SEED STEPS [STATEIN] [STATEOUT] [EDGESOUT]\n"); return 2; }
    FILE *f = fopen(argv[1], "r");
    for (int c = 0; c < 4; c++) for (int r = 0; r < 4; r++) for (int k = 0; k < 4; k++) if (fscanf(f, "%d", &A[c][r][k]) != 1) return 3;
    for (int c = 0; c < 4; c++) for (int k = 0; k < 4; k++) if (fscanf(f, "%d", &Bv[c][k]) != 1) return 3;
    fclose(f);
    N = atoi(argv[3]); int perm[4]; sscanf(argv[4], "%d %d %d %d", &perm[0], &perm[1], &perm[2], &perm[3]);
    int XL = atoi(argv[5]);
    f = fopen(argv[2], "r"); long a, b; int col; nb = 0; m = 0;
    while (fscanf(f, "%ld %ld %d", &a, &b, &col) == 3) {
        int i = a / N, g = a % N, j = b / N, h = b % N; if (g != 0) continue;   /* one representative per orbit */
        Ei[m] = i; Ej[m] = j; Ev[m] = ((h - g) % N + N) % N; Ec[m] = perm[col]; Ex[m] = (perm[col] == XL); m++;
        if (i + 1 > nb) nb = i + 1; if (j + 1 > nb) nb = j + 1;
    }
    fclose(f);
    rs = 88172645463325252ULL ^ (unsigned long long)atoll(argv[6]) * 2654435761ULL; for (int i = 0; i < 10; i++) rnd();
    long steps = atol(argv[7]); double T0 = 1.0;
    const char *sin = argc > 8 ? argv[8] : "-", *sout = argc > 9 ? argv[9] : "-", *eout = argc > 10 ? argv[10] : "-";
    prep_chart();
    for (int e = 0; e < m; e++) Xv[e] = 0;
    int loaded = (strcmp(sin, "-") != 0) && load_state(sin);
    if (!loaded) for (int e = 0; e < m; e++) if (Ex[e]) { do Xv[e] = rnd() % 256; while (0); }
    /* check extended edges form a perfect matching of the base */
    int cntA[64] = {0}, cntB[64] = {0};
    for (int e = 0; e < m; e++) if (Ex[e]) { cntA[Ei[e]]++; cntB[Ej[e]]++; }
    for (int i = 0; i < nb; i++) if (cntA[i] != 1 || cntB[i] != 1) { fprintf(stderr, "extended edges are not a perfect matching\n"); }
    build();
    vis = malloc(n * 8); fr = malloc(n * 8); nx = malloc(n * 8);
    long cur = cost(1L << 62), best = cur;
    printf("N %d n %ld start cost %ld\n", N, n, cur); fflush(stdout);
    int bv[64], bx[64]; memcpy(bv, Ev, sizeof Ev); memcpy(bx, Xv, sizeof Xv);
    time_t t0 = time(0);
    for (long s = 0; s < steps && best > 0; s++) {
        double T = T0 * (1.0 - (double)s / steps) + 1e-3;
        int e = rnd() % m, ov = Ev[e], ox = Xv[e], mode;
        if (!Ex[e]) { s--; continue; }
        if (1) { mode = 1; int nxv; do nxv = rnd() % 256; while (nxv == ox); Xv[e] = nxv; }
        else { mode = 0; int nv; do nv = rnd() % N; while (nv == ov && N > 1); Ev[e] = nv; }
        (void)mode;
        build();
        double Tabs = T * 0.02 * (double)(best + 50);
        long cap = cur + (long)(-Tabs * log(urand() + 1e-12)) + 1;
        long c = cost(cap);
        if (c <= cur || c < cap) {
            cur = c;
            if (c < best) { best = c; memcpy(bv, Ev, sizeof Ev); memcpy(bx, Xv, sizeof Xv); if (strcmp(sout, "-")) save_state(sout, best);
                printf("step %ld cost %ld (t=%lds)\n", s, best, (long)(time(0) - t0)); fflush(stdout); }
        } else { Ev[e] = ov; Xv[e] = ox; }
    }
    memcpy(Ev, bv, sizeof Ev); memcpy(Xv, bx, sizeof Xv);
    if (strcmp(sout, "-")) save_state(sout, best);
    if (strcmp(eout, "-")) {
        build();
        FILE *g = fopen(eout, "w"); fprintf(g, "%ld\n", n);
        for (long a = 0; a < nA; a++) for (long i = st[a]; i < st[a + 1]; i++) fprintf(g, "%ld %d\n", a, adj[i]);
        fclose(g);
    }
    printf("FINAL N %d n %ld best %ld\n", N, n, best);
    return 0;
}
