/* geocov.c: Z_k covers of a generalized quadrangle (incidence graph I, diameter 4) whose geodesics between opposite
   elements carry many distinct voltages.

   Flag voltages psi(P,L) in Z_k. For opposite points u, y the q+1 geodesics u - L1 - p - L2 - y have voltage
   psi(u,L1) - psi(p,L1) + psi(p,L2) - psi(y,L2); for opposite lines u, y the q+1 geodesics u - p1 - L - p2 - y have
   -psi(p1,u) + psi(p1,L) - psi(p2,L) + psi(p2,y). Cost = sum over unordered opposite pairs (points and lines) of the
   number of values of Z_k missed by its q+1 geodesic voltages (target: 0, i.e. every opposite pair sees all k
   sheets). Reports also the histogram of distinct values per pair.

   Usage: geocov POLY k secs seed [OUTFLAGS]   (POLY in hexgen format; prints min/mean distinct counts) */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>

static int q, q1, N, k;
static int *lp, *pl, *fid;     /* fid[l*q1+j] = flag id of (lp[l*q1+j], l) */
static int *psi;               /* per flag */
typedef struct { int f[4]; signed char s[4]; } Geo;
static Geo *geo; static long ngeo;  /* geodesics grouped by pair: pair i has geodesics [i*q1, (i+1)*q1) */
static long npair;
static int *pmiss;
static long *fl_off, *fl_list;     /* flag -> list of pairs using it */
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline int rndi(int n) { return (int)(rnd() % (uint64_t)n); }
static double now(void) { struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts); return ts.tv_sec + 1e-9 * ts.tv_nsec; }

static int flag_of(int p, int l) { for (int j = 0; j < q1; j++) if (lp[l * q1 + j] == p) return fid[l * q1 + j]; return -1; }
static int line_of(int p1, int p2) {  /* line through two collinear points, or -1 */
    for (int a = 0; a < q1; a++) { int l = pl[p1 * q1 + a]; for (int j = 0; j < q1; j++) if (lp[l * q1 + j] == p2) return l; }
    return -1;
}
static int pair_miss(long i) {
    unsigned char seen[64]; memset(seen, 0, k); int c = 0;
    for (int g = 0; g < q1; g++) {
        Geo *G = &geo[i * q1 + g]; int v = 0;
        for (int t = 0; t < 4; t++) v += G->s[t] * psi[G->f[t]];
        v %= k; if (v < 0) v += k;
        if (!seen[v]) { seen[v] = 1; c++; }
    }
    return k - c;
}
int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage: geocov POLY k secs seed [OUT]\n"); return 1; }
    FILE *f = fopen(argv[1], "rb"); int32_t h[3]; if (!f || fread(h, 4, 3, f) != 3) return 1;
    q = h[0]; N = h[1]; q1 = q + 1;
    lp = malloc(sizeof(int) * (size_t)N * q1); pl = malloc(sizeof(int) * (size_t)N * q1); fid = malloc(sizeof(int) * (size_t)N * q1);
    int32_t *tmp = malloc(4 * (size_t)N * q1); if (fread(tmp, 4, (size_t)N * q1, f) != (size_t)N * q1) return 1; fclose(f);
    int *cnt = calloc(N, sizeof(int));
    for (size_t i = 0; i < (size_t)N * q1; i++) { lp[i] = tmp[i]; fid[i] = (int)i; }
    for (int l = 0; l < N; l++) for (int j = 0; j < q1; j++) { int p = lp[l * q1 + j]; pl[p * q1 + cnt[p]++] = l; }
    k = atoi(argv[2]); double secs = atof(argv[3]);
    rs ^= (uint64_t)atoll(argv[4]) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 10; i++) rnd();
    int F = N * q1; psi = malloc(sizeof(int) * F); for (int i = 0; i < F; i++) psi[i] = rndi(k);
    /* collinearity: point distance-2 lists */
    unsigned char *col = calloc((size_t)N * N, 1);   /* col[u*N+y]=1 if collinear or equal */
    for (int l = 0; l < N; l++) for (int a = 0; a < q1; a++) for (int b = 0; b < q1; b++) col[(size_t)lp[l * q1 + a] * N + lp[l * q1 + b]] = 1;
    unsigned char *conc = calloc((size_t)N * N, 1);  /* lines concurrent or equal */
    for (int p = 0; p < N; p++) for (int a = 0; a < q1; a++) for (int b = 0; b < q1; b++) conc[(size_t)pl[p * q1 + a] * N + pl[p * q1 + b]] = 1;
    long cap = (long)N * N; geo = malloc(sizeof(Geo) * 1); npair = 0;
    /* count pairs */
    long np = 0; for (int u = 0; u < N; u++) for (int y = u + 1; y < N; y++) { if (!col[(size_t)u * N + y]) np++; if (!conc[(size_t)u * N + y]) np++; }
    (void)cap;
    geo = malloc(sizeof(Geo) * np * q1);
    for (int u = 0; u < N; u++) for (int y = u + 1; y < N; y++) {
        if (!col[(size_t)u * N + y]) {   /* opposite points: common neighbours p */
            int g = 0;
            for (int a = 0; a < q1; a++) { int L1 = pl[u * q1 + a];
                for (int j = 0; j < q1; j++) { int p = lp[L1 * q1 + j]; if (p == u || !col[(size_t)p * N + y]) continue;
                    int L2 = line_of(p, y); Geo *G = &geo[npair * q1 + g++];
                    G->f[0] = flag_of(u, L1); G->s[0] = 1; G->f[1] = flag_of(p, L1); G->s[1] = -1;
                    G->f[2] = flag_of(p, L2); G->s[2] = 1; G->f[3] = flag_of(y, L2); G->s[3] = -1; } }
            if (g != q1) { fprintf(stderr, "geodesic count %d\n", g); return 1; }
            npair++;
        }
        if (!conc[(size_t)u * N + y]) {  /* opposite lines u, y: points p1 on u collinear with a point p2 on y */
            int g = 0;
            for (int a = 0; a < q1; a++) { int p1 = lp[u * q1 + a];
                for (int b = 0; b < q1; b++) { int p2 = lp[y * q1 + b]; if (!col[(size_t)p1 * N + p2] || p1 == p2) continue;
                    int L = line_of(p1, p2); Geo *G = &geo[npair * q1 + g++];
                    G->f[0] = flag_of(p1, u); G->s[0] = -1; G->f[1] = flag_of(p1, L); G->s[1] = 1;
                    G->f[2] = flag_of(p2, L); G->s[2] = -1; G->f[3] = flag_of(p2, y); G->s[3] = 1; } }
            if (g != q1) { fprintf(stderr, "line geodesic count %d\n", g); return 1; }
            npair++;
        }
    }
    free(col); free(conc);
    /* flag -> pairs index */
    long *deg = calloc(F, sizeof(long));
    for (long i = 0; i < npair; i++) for (int g = 0; g < q1; g++) for (int t = 0; t < 4; t++) deg[geo[i * q1 + g].f[t]]++;
    fl_off = malloc(sizeof(long) * (F + 1)); fl_off[0] = 0; for (int i = 0; i < F; i++) fl_off[i + 1] = fl_off[i] + deg[i];
    fl_list = malloc(sizeof(long) * fl_off[F]); memset(deg, 0, sizeof(long) * F);
    for (long i = 0; i < npair; i++) for (int g = 0; g < q1; g++) for (int t = 0; t < 4; t++) { int fl = geo[i * q1 + g].f[t]; fl_list[fl_off[fl] + deg[fl]++] = i; }
    pmiss = malloc(sizeof(int) * npair); long cost = 0;
    for (long i = 0; i < npair; i++) { pmiss[i] = pair_miss(i); cost += pmiss[i]; }
    fprintf(stderr, "q=%d k=%d pairs=%ld start cost %ld (mean missing %.3f)\n", q, k, npair, cost, (double)cost / npair);
    double T0 = getenv("T0") ? atof(getenv("T0")) : 2.0, T1 = getenv("T1") ? atof(getenv("T1")) : 0.05;
    double t0 = now(), last = t0; long it = 0, best = cost;
    int *newm = malloc(sizeof(int) * 400000); long *uidx = malloc(sizeof(long) * 400000);
    int *stamp = calloc(npair, sizeof(int)); int stampc = 0;
    while (cost > 0 && now() - t0 < secs) {
        double T = T0 * pow(T1 / T0, (now() - t0) / secs);
        int fl = rndi(F), old = psi[fl], nv = rndi(k); if (nv == old) continue;
        long d = 0; psi[fl] = nv; long n0 = fl_off[fl], n1 = fl_off[fl + 1]; int nu = 0;
        stampc++;
        for (long a = n0; a < n1; a++) { long i = fl_list[a]; if (stamp[i] == stampc) continue; stamp[i] = stampc;
            int nm = pair_miss(i); uidx[nu] = i; newm[nu++] = nm; d += nm - pmiss[i]; }
        it++;
        if (d <= 0 || (rnd() >> 11) * (1.0 / 9007199254740992.0) < exp(-d / T)) {
            for (int a = 0; a < nu; a++) pmiss[uidx[a]] = newm[a];
            cost += d; if (cost < best) best = cost;
        } else psi[fl] = old;
        if (now() - last > 10) { last = now(); fprintf(stderr, "t=%.0f it=%ld T=%.3f cost=%ld best=%ld\n", now() - t0, it, T, cost, best); }
    }
    long hist[65] = {0}; for (long i = 0; i < npair; i++) hist[k - pmiss[i]]++;
    printf("RESULT q=%d k=%d cost=%ld pairs=%ld; distinct-values histogram:", q, k, cost, npair);
    for (int c = 0; c <= k; c++) if (hist[c]) printf(" %d:%ld", c, hist[c]);
    printf("\n");
    if (argc > 5) { FILE *o = fopen(argv[5], "w"); for (int i = 0; i < F; i++) fprintf(o, "%d\n", psi[i]); fclose(o); }
    return 0;
}
