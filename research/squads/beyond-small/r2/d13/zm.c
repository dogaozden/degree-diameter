/* zm: Z_N-symmetric lift of a bipartite controller (plain 16-regular, letters 0..3, F4^4 fibres) plus one extra
 * Z_N-invariant perfect matching between A-classes (i,x) and B-classes (j,y) with voltages (degree 17 overall).
 * usage: zm CHART CTRL N "p0 p1 p2 p3" SECS SEED STATEIN|- STATEOUT|- EDGESOUT|-
 * State: 768 PI values (B-class of each A-class k=i*256+x), then 768 voltages TV.
 * Cost = far pairs (distance > 5) from sources (one per base vertex, g=0, all fibre points, both sides) x all vertices.
 * Symmetry-based exact cost; calibrated: Z22 known controller with identity perm gives 0. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>
static int MUL[4][4] = {{0,0,0,0},{0,1,2,3},{0,2,3,1},{0,3,1,2}};
static int A[4][4][4], Bv[4][4];
static int AX[4][256], LB[4][4];
static int nb, m, N, Ei[64], Ej[64], Ev[64], Ec[64];
static long n, nA, NE;
static int *eu, *ev;
static long *st; static int *adj;
static uint64_t *vis, *fr, *nx;
static int PI[1024], TV[1024];
static int NCL;
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
static void build(void) {
    nA = (long)nb * N * 256; n = 2 * nA; NE = 0;
    for (int e = 0; e < m; e++) { int c = Ec[e];
        for (int g = 0; g < N; g++) for (int x = 0; x < 256; x++) {
            long ca = ((long)Ei[e] * N + g) * 256 + x; int ax = AX[c][x];
            long cb = (long)Ej[e] * N + ((g + Ev[e]) % N);
            for (int l = 0; l < 4; l++) { eu[NE] = (int)ca; ev[NE] = (int)(nA + cb * 256 + (ax ^ LB[c][l])); NE++; }
        } }
    for (int k = 0; k < NCL; k++) { int i = k / 256, x = k % 256; int p = PI[k], j = p / 256, y = p % 256;
        for (int g = 0; g < N; g++) { long a = ((long)i * N + g) * 256 + x; long h = (g + TV[k]) % N;
            eu[NE] = (int)a; ev[NE] = (int)(nA + ((long)j * N + h) * 256 + y); NE++; } }
    long *deg = calloc(n + 1, sizeof(long));
    for (long e = 0; e < NE; e++) { deg[eu[e]]++; deg[ev[e]]++; }
    st[0] = 0; for (long i = 0; i < n; i++) st[i + 1] = st[i] + deg[i];
    for (long i = 0; i < n; i++) deg[i] = st[i];
    for (long e = 0; e < NE; e++) { adj[deg[eu[e]]++] = ev[e]; adj[deg[ev[e]]++] = eu[e]; }
    free(deg);
}
static long dupcount(void) { /* extra edges that duplicate a base edge (penalised) */
    long d = 0; int base_m = NE - NCL * N;
    for (long e = base_m; e < NE; e++) { long a = eu[e], b = ev[e];
        for (long i = st[a]; i < st[a + 1]; i++) if (adj[i] == b) { int cnt = 0; for (long j = st[a]; j < st[a+1]; j++) if (adj[j]==b) cnt++; if (cnt > 1) { d++; } break; } }
    return d;
}
static long cost(long cap) {
    long far = 0; long nsrc = 2L * nb * 256;
    for (long k0 = 0; k0 < nsrc; k0 += 64) {
        memset(vis, 0, n * 8); memset(fr, 0, n * 8);
        int ns = (nsrc - k0 < 64) ? (int)(nsrc - k0) : 64;
        for (int k = 0; k < ns; k++) {
            long s = k0 + k; long side = s / ((long)nb * 256), r = s % ((long)nb * 256);
            long bi = r / 256, x = r % 256; long v = side * nA + (bi * N) * 256 + x;
            vis[v] |= 1ULL << k; fr[v] |= 1ULL << k;
        }
        for (int lev = 0; lev < 5; lev++) {
            for (long x = 0; x < n; x++) { uint64_t acc = 0; for (long i = st[x]; i < st[x + 1]; i++) acc |= fr[adj[i]]; acc &= ~vis[x]; nx[x] = acc; }
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
static void save_state(const char *fn) { if (!strcmp(fn, "-")) return; FILE *f = fopen(fn, "w"); if (!f) return;
    for (int k = 0; k < NCL; k++) fprintf(f, "%d ", PI[k]); fprintf(f, "\n");
    for (int k = 0; k < NCL; k++) fprintf(f, "%d ", TV[k]); fprintf(f, "\n"); fclose(f); }
static int load_state(const char *fn) { FILE *f = fopen(fn, "r"); if (!f) return 0;
    for (int k = 0; k < NCL; k++) if (fscanf(f, "%d", &PI[k]) != 1) { fclose(f); return 0; }
    for (int k = 0; k < NCL; k++) if (fscanf(f, "%d", &TV[k]) != 1) { fclose(f); return 0; }
    fclose(f); return 1; }
int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: zm CHART CTRL N \"p0 p1 p2 p3\" SECS SEED [STATEIN] [STATEOUT] [EDGESOUT]\n"); return 2; }
    FILE *f = fopen(argv[1], "r");
    for (int c = 0; c < 4; c++) for (int r = 0; r < 4; r++) for (int k = 0; k < 4; k++) if (fscanf(f, "%d", &A[c][r][k]) != 1) return 3;
    for (int c = 0; c < 4; c++) for (int k = 0; k < 4; k++) if (fscanf(f, "%d", &Bv[c][k]) != 1) return 3;
    fclose(f);
    N = atoi(argv[3]); int perm[4]; sscanf(argv[4], "%d %d %d %d", &perm[0], &perm[1], &perm[2], &perm[3]);
    f = fopen(argv[2], "r"); long a, b; int col; nb = 0; m = 0;
    while (fscanf(f, "%ld %ld %d", &a, &b, &col) == 3) {
        int i = a / N, g = a % N, j = b / N, h = b % N; if (g != 0) continue;
        Ei[m] = i; Ej[m] = j; Ev[m] = ((h - g) % N + N) % N; Ec[m] = perm[col]; m++;
        if (i + 1 > nb) nb = i + 1; if (j + 1 > nb) nb = j + 1;
    }
    fclose(f);
    double secs = atof(argv[5]); rs = 88172645463325252ULL ^ (unsigned long long)atoll(argv[6]) * 2654435761ULL; for (int i = 0; i < 10; i++) rnd();
    const char *sin = argc > 7 ? argv[7] : "-", *sout = argc > 8 ? argv[8] : "-", *eout = argc > 9 ? argv[9] : "-";
    prep_chart(); NCL = nb * 256;
    int loaded = (strcmp(sin, "-") != 0) && load_state(sin);
    if (!loaded) {
        for (int k = 0; k < NCL; k++) PI[k] = k;
        for (int k = NCL - 1; k > 0; k--) { int r = rnd() % (k + 1); int t = PI[k]; PI[k] = PI[r]; PI[r] = t; }
        for (int k = 0; k < NCL; k++) TV[k] = rnd() % N;
    }
    long maxE = (long)m * N * 256 * 4 + (long)NCL * N + 16;
    eu = malloc(maxE * sizeof(int)); ev = malloc(maxE * sizeof(int));
    st = malloc((2L * nb * N * 256 + 1) * sizeof(long));
    adj = malloc(2 * maxE * sizeof(int));
    build();
    vis = malloc(n * 8); fr = malloc(n * 8); nx = malloc(n * 8);
    long cur = cost(1L << 62) + 1000 * dupcount(), best = cur;
    int bPI[1024], bTV[1024];
    memcpy(bPI, PI, sizeof PI); memcpy(bTV, TV, sizeof TV);
    printf("N %d n %ld m %d start cost %ld\n", N, n, m, cur); fflush(stdout);
    time_t t0 = time(0);
    long steps = 0;
    while (best > 0 && difftime(time(0), t0) < secs) {
        steps++;
        double T = 300.0 * (1.0 - difftime(time(0), t0) / secs) + 2.0;
        int mv = rnd() % 3, k1 = rnd() % NCL, k2 = rnd() % NCL, oldt = TV[k1], oldp1 = PI[k1], oldp2 = PI[k2];
        if (mv == 0) { int nt; do nt = rnd() % N; while (nt == oldt); TV[k1] = nt; }
        else { if (k1 == k2) continue; PI[k1] = oldp2; PI[k2] = oldp1; }
        build();
        long c = cost((long)(cur + (-T * log(urand() + 1e-12))) + 1 - 1000 * dupcount()) + 1000 * dupcount();
        double u = urand() + 1e-12;
        long cap = cur + (long)(-T * log(u)) + 1;
        if (c <= cur || c < cap) {
            cur = c;
            if (c < best) { best = c; memcpy(bPI, PI, sizeof PI); memcpy(bTV, TV, sizeof TV);
                printf("step %ld cost %ld (t=%.0fs)\n", steps, best, difftime(time(0), t0)); fflush(stdout); }
        } else {
            if (mv == 0) TV[k1] = oldt; else { PI[k1] = oldp1; PI[k2] = oldp2; }
        }
    }
    memcpy(PI, bPI, sizeof PI); memcpy(TV, bTV, sizeof TV);
    save_state(sout);
    printf("FINAL N %d n %ld best %ld steps %ld\n", N, n, best, steps);
    if (strcmp(eout, "-") && best == 0) {
        build();
        FILE *g = fopen(eout, "w"); fprintf(g, "%ld\n", n);
        for (long e = 0; e < NE; e++) fprintf(g, "%d %d\n", eu[e], ev[e]);
        fclose(g);
    }
    return 0;
}
