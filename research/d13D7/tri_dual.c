/* tri_dual.c: the three-copy construction with hubs when H(q) has an explicit duality (q = 3^h), side quest of job
   cell-13-7 for (q+2, 7).  Vertices (x, i), x a point or line of H(q), i in Z3; hexagon edges in every copy; matching
   (p, i) ~ (delta(p), i+1) with delta: points -> lines a DUALITY (so delta(Gamma_2(p)) = Gamma_2(delta(p)) for every p).
   Surgery: R = a set of pairwise NON-COLLINEAR points; for r in R the three matching edges at r are removed, a hub v_r is
   joined to (r, 0), (r, 1), (r, 2) and a hub u_r to (delta(r), 0), (delta(r), 1), (delta(r), 2); hubs are joined by a
   circulant v_j ~ u_{j+c}, c in a random set of nsd = q-1 offsets (Delta = q+2).
   Theorem (research/d13D7/REPORT.md): diameter <= 7 whenever R is non-collinear, delta is a local duality at every r,
   and hub pairs whose points are opposite are within 6 (checked here by BFS).
   usage: tri_dual HEXFILE DUALFILE RFILE seed [out.edges]   (DUALFILE: delta(p) for p = 0..N-1; RFILE: point indices)
   env NRAND (random BFS sources, default 2048), NOCHECK (skip the BFS check), NSDEG, NSFILE (hub graph "j k" lines), OFFS ("c1 c2 ...": hub offsets; default random). */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
static int q, N, Q1; static int32_t *lp, *pl;
static uint64_t rs = 0x9E3779B97F4A7C15ULL;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int *readints(const char *fn, int *n) {
    FILE *g = fopen(fn, "r"); if (!g) { perror(fn); exit(1); } int cap = 1 << 16, k = 0; int *a = malloc(sizeof(int) * cap); char buf[512];
    while (fgets(buf, sizeof buf, g)) { if (buf[0] == '#') continue; int v; if (sscanf(buf, "%d", &v) == 1) { if (k == cap) { cap *= 2; a = realloc(a, sizeof(int) * cap); } a[k++] = v; } }
    fclose(g); *n = k; return a;
}
int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage: tri_dual HEXFILE DUALFILE RFILE seed [out.edges]\n"); return 1; }
    FILE *f = fopen(argv[1], "rb"); int32_t hdr[3]; if (!f || fread(hdr, 4, 3, f) != 3) return 1; q = hdr[0]; N = hdr[1]; Q1 = q + 1;
    lp = malloc(4L * N * Q1); if (fread(lp, 4, (size_t)N * Q1, f) != (size_t)N * Q1) return 1; fclose(f);
    pl = malloc(4L * N * Q1); int *c = calloc(N, sizeof(int));
    for (int l = 0; l < N; l++) for (int k = 0; k < Q1; k++) { int p = lp[(size_t)l * Q1 + k]; pl[(size_t)p * Q1 + c[p]++] = l; }
    int nd; int *sig = readints(argv[2], &nd); if (nd != N) { fprintf(stderr, "duality file has %d entries, want %d\n", nd, N); return 1; }
    int m; int *R = readints(argv[3], &m);
    rs ^= (uint64_t)atoll(argv[4]) * 0x2545F4914F6CDD1DULL; for (int i = 0; i < 10; i++) rnd();
    /* checks: sig is a bijection; R non-collinear; sig(Gamma_2(r)) = Gamma_2(sig(r)) for r in R */
    char *usedL = calloc(N, 1); for (int p = 0; p < N; p++) { if (sig[p] < 0 || sig[p] >= N || usedL[sig[p]]) { fprintf(stderr, "delta not a bijection\n"); return 1; } usedL[sig[p]] = 1; }
    char *lineHasR = calloc(N, 1), *inR = calloc(N, 1);
    for (int j = 0; j < m; j++) { int r = R[j]; if (inR[r]) { fprintf(stderr, "repeated R point\n"); return 1; } inR[r] = 1;
        for (int k = 0; k < Q1; k++) { int l = pl[(size_t)r * Q1 + k]; if (lineHasR[l]) { fprintf(stderr, "R not non-collinear (line %d)\n", l); return 1; } lineHasR[l] = 1; } }
    char *mark = calloc(N, 1); long badloc = 0;
    for (int j = 0; j < m; j++) { int r = R[j], s = sig[r];
        for (int k = 0; k < Q1; k++) { int l = lp[(size_t)s * Q1 + k]; for (int t = 0; t < Q1; t++) { int l2 = pl[(size_t)l * Q1 + t]; if (l2 != s) mark[l2] = 1; } }
        for (int k = 0; k < Q1; k++) { int l = pl[(size_t)r * Q1 + k]; for (int t = 0; t < Q1; t++) { int x = lp[(size_t)l * Q1 + t]; if (x != r && !mark[sig[x]]) badloc++; } }
        for (int k = 0; k < Q1; k++) { int l = lp[(size_t)s * Q1 + k]; for (int t = 0; t < Q1; t++) { int l2 = pl[(size_t)l * Q1 + t]; mark[l2] = 0; } } }
    if (badloc) { fprintf(stderr, "delta is not a local duality at R (%ld misses)\n", badloc); return 1; }
    fprintf(stderr, "H(%d): delta OK, |R| = %d non-collinear, local duality at every r\n", q, m);
    long n = 6L * N + 2L * m;
    int nsd = getenv("NSDEG") ? atoi(getenv("NSDEG")) : q - 1;
    long nemax = 3L * N * Q1 + 3L * N + 6L * m + (long)nsd * m + 16;
    int32_t *EU = malloc(4 * nemax), *EW = malloc(4 * nemax); long ne = 0;
#define V_PT(i, p) ((int32_t)((long)(i) * 2 * N + (p)))
#define V_LN(i, l) ((int32_t)((long)(i) * 2 * N + N + (l)))
#define V_NEWV(j) ((int32_t)(6L * N + (j)))
#define V_NEWU(j) ((int32_t)(6L * N + m + (j)))
    for (int i = 0; i < 3; i++) for (int l = 0; l < N; l++) for (int k = 0; k < Q1; k++) { EU[ne] = V_PT(i, lp[(size_t)l * Q1 + k]); EW[ne] = V_LN(i, l); ne++; }
    for (int i = 0; i < 3; i++) for (int p = 0; p < N; p++) if (!inR[p]) { EU[ne] = V_PT(i, p); EW[ne] = V_LN((i + 1) % 3, sig[p]); ne++; }
    for (int j = 0; j < m; j++) for (int i = 0; i < 3; i++) { EU[ne] = V_NEWV(j); EW[ne] = V_PT(i, R[j]); ne++; EU[ne] = V_NEWU(j); EW[ne] = V_LN(i, sig[R[j]]); ne++; }
    if (getenv("NSFILE")) { FILE *g = fopen(getenv("NSFILE"), "r"); int a, b; long cnt = 0; while (g && fscanf(g, "%d %d", &a, &b) == 2) { if (a < 0 || a >= m || b < 0 || b >= m || cnt >= (long)nsd * m) { fprintf(stderr, "bad NSFILE\n"); return 1; } EU[ne] = V_NEWV(a); EW[ne] = V_NEWU(b); ne++; cnt++; } if (g) fclose(g); fprintf(stderr, "hub graph from %s: %ld edges\n", getenv("NSFILE"), cnt); }
    else if (m <= nsd) { for (int j = 0; j < m; j++) for (int k = 0; k < m; k++) { EU[ne] = V_NEWV(j); EW[ne] = V_NEWU(k); ne++; } }
    else { int offs[32], no = 0;
        if (getenv("OFFS")) { char *p = getenv("OFFS"); int v, u; while (no < nsd && sscanf(p, "%d%n", &v, &u) == 1) { offs[no++] = ((v % m) + m) % m; p += u; } }
        while (no < nsd) { int cnd = rnd() % m, ok = 1; for (int t = 0; t < no; t++) if (offs[t] == cnd) ok = 0; if (ok) offs[no++] = cnd; }
        fprintf(stderr, "hub offsets:"); for (int t = 0; t < nsd; t++) fprintf(stderr, " %d", offs[t]); fprintf(stderr, "\n");
        for (int j = 0; j < m; j++) for (int t = 0; t < nsd; t++) { EU[ne] = V_NEWV(j); EW[ne] = V_NEWU((j + offs[t]) % m); ne++; } }
    int *deg = calloc(n, sizeof(int)); for (long e = 0; e < ne; e++) { deg[EU[e]]++; deg[EW[e]]++; }
    long *st = malloc(sizeof(long) * (n + 1)); st[0] = 0; for (long x = 0; x < n; x++) st[x + 1] = st[x] + deg[x];
    int32_t *adj = malloc(4 * st[n]); long *pos = calloc(n, sizeof(long));
    for (long e = 0; e < ne; e++) { adj[st[EU[e]] + pos[EU[e]]++] = EW[e]; adj[st[EW[e]] + pos[EW[e]]++] = EU[e]; }
    int maxdeg = 0; for (long x = 0; x < n; x++) if (deg[x] > maxdeg) maxdeg = deg[x];
    fprintf(stderr, "graph: n = %ld, edges = %ld, max degree %d\n", n, ne, maxdeg);
    /* BFS from all damaged/new vertices and random ones (bit-parallel, 64 per pass) */
    if (getenv("NOCHECK")) { if (argc > 5) { FILE *o = fopen(argv[5], "w"); fprintf(o, "%ld\n", n); for (long e = 0; e < ne; e++) fprintf(o, "%d %d\n", EU[e], EW[e]); fclose(o); fprintf(stderr, "wrote %s (no internal check)\n", argv[5]); } return 0; }
    int nrand = getenv("NRAND") ? atoi(getenv("NRAND")) : 2048;
    long nsrc = 0; int32_t *src = malloc(4 * (8L * m + nrand + 64));
    for (int j = 0; j < m; j++) { src[nsrc++] = V_NEWV(j); src[nsrc++] = V_NEWU(j); for (int i = 0; i < 3; i++) { src[nsrc++] = V_PT(i, R[j]); src[nsrc++] = V_LN(i, sig[R[j]]); } }
    for (int t = 0; t < nrand; t++) src[nsrc++] = (int32_t)(rnd() % n);
    int worst = 0; long bad = 0; long npass = (nsrc + 63) / 64;
    #pragma omp parallel
    { uint64_t *vis = malloc(8 * n), *fr = malloc(8 * n), *nx = malloc(8 * n);
      #pragma omp for schedule(dynamic, 1) reduction(max:worst) reduction(+:bad)
      for (long ps = 0; ps < npass; ps++) {
        long s0 = ps * 64; int ns = (nsrc - s0 < 64) ? (int)(nsrc - s0) : 64;
        memset(vis, 0, 8 * n); memset(fr, 0, 8 * n);
        for (int k = 0; k < ns; k++) { vis[src[s0 + k]] |= 1ULL << k; fr[src[s0 + k]] |= 1ULL << k; }
        uint64_t full = (ns == 64) ? ~0ULL : ((1ULL << ns) - 1); int ecc[64] = {0}; int lev = 0;
        for (;;) { uint64_t anyb = 0;
            for (long x = 0; x < n; x++) { uint64_t acc = 0; for (long a = st[x]; a < st[x + 1]; a++) acc |= fr[adj[a]]; acc &= ~vis[x]; nx[x] = acc; anyb |= acc; }
            if (!anyb) break; lev++; for (int k = 0; k < ns; k++) if (anyb >> k & 1) ecc[k] = lev;
            for (long x = 0; x < n; x++) vis[x] |= nx[x]; uint64_t *t = fr; fr = nx; nx = t; if (lev > 9) break; }
        uint64_t miss = 0; for (long x = 0; x < n; x++) miss |= full & ~vis[x];
        for (int k = 0; k < ns; k++) { int e = (miss >> k & 1) ? 99 : ecc[k]; if (e > worst) worst = e; if (e > 7) bad++; }
      }
      free(vis); free(fr); free(nx); }
    printf("q=%d m=%d n=%ld maxdeg=%d sources=%ld worst_ecc=%d bad=%ld\n", q, m, n, maxdeg, nsrc, worst, bad);
    if (argc > 5) { FILE *o = fopen(argv[5], "w"); fprintf(o, "%ld\n", n); for (long e = 0; e < ne; e++) fprintf(o, "%d %d\n", EU[e], EW[e]); fclose(o); fprintf(stderr, "wrote %s\n", argv[5]); }
    return bad ? 2 : 0;
}
