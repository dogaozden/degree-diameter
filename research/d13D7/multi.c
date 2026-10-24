/* multi.c: (2r+1) copies of the generalized hexagon H(q) joined by r matchings (the table's (q+1+r, 7) construction,
   order (2r+1)|H(q)|), with hub surgeries.  Job cell-13-7, 2026-10-24.
   Levels Z_{2r+1}; hexagon edges in every level; for k = 1..r: (p, i) ~ (sigma(p), i+k) (the same bijection sigma:
   points -> lines for every k).  Any sigma gives diameter <= 7: two levels differ by +-k for some k <= r and the
   three-copy proof applies to the pair with the k-th matching.
   Surgery at a point set R (FULL removal, default): delete all r(2r+1) extra edges at every (x, i), x in R; add r
   line-side hubs v_{a,x} ~ (x, i) for all i and r point-side hubs u_{a,x} ~ (sigma(x), i) for all i (a = 1..r):
   +2r vertices per point.  PARTIAL=1: delete only the k = 1 edges: one hub of each side per point, +2 per point.
   Valid (diameter <= 7) when, as in REPORT.md: R non-collinear and sigma(R) non-concurrent with sigma a local duality
   at every x in R (sigma(Gamma_2(x)) = Gamma_2(sigma(x))), and same-side hubs of opposite points within 6 (hub graph).
   Modes:  DUALFILE=f : sigma = the duality in f (point -> line), R from RFILE must be non-collinear;
           otherwise   : RFILE (pairwise opposite points) and SFILE (pairwise opposite lines): sigma(R_j) = S_j,
                         sigma(Gamma_2(R_j)) = Gamma_2(S_j) in random order, random elsewhere.
   Hub graph: NSFILE ("j k" lines: line-side hub j ~ point-side hub k; hub j = a*m + index in R), else a random
   d-regular bipartite graph, d = NSDEG or q - r (PARTIAL: q - 1... capped by Delta - (2r+1)), retried until all
   same-side hub distances in it are <= 6 (at most 200 tries).
   usage: multi HEXFILE r seed out.edges     env NOCHECK=1 skips the internal BFS (damaged vertices + hubs + random);
   HP = number of point-side hubs (default = number of line-side hubs; fewer leaves freed line slots unused). */
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
/* same-side distances <= 6 in a bipartite hub graph (H hubs per side, adjacency lists) */
static int hub_ok(int H, int d, int *A, int *B) {   /* A[j*d+t]: point-side nbrs of line-side hub j; B: reverse */
    int *dist = malloc(sizeof(int) * H), *qa = malloc(sizeof(int) * H), *mk = malloc(sizeof(int) * H); int ok = 1;
    for (int side = 0; side < 2 && ok; side++) { int *X = side ? B : A, *Y = side ? A : B;
        for (int s = 0; s < H && ok; s++) {
            for (int i = 0; i < H; i++) { dist[i] = -1; mk[i] = 0; }
            int h = 0, t = 0; dist[s] = 0; qa[t++] = s; int reached = 1;
            while (h < t) { int x = qa[h++]; if (dist[x] >= 6) continue;
                for (int a = 0; a < d; a++) { int y = X[x * d + a]; if (mk[y]) continue; mk[y] = 1;
                    for (int b = 0; b < d; b++) { int z = Y[y * d + b]; if (dist[z] < 0) { dist[z] = dist[x] + 2; qa[t++] = z; reached++; } } } }
            if (reached < H) ok = 0; } }
    free(dist); free(qa); free(mk); return ok;
}
int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage: multi HEXFILE r seed out.edges\n"); return 1; }
    FILE *f = fopen(argv[1], "rb"); int32_t hdr[3]; if (!f || fread(hdr, 4, 3, f) != 3) return 1; q = hdr[0]; N = hdr[1]; Q1 = q + 1;
    lp = malloc(4L * N * Q1); if (fread(lp, 4, (size_t)N * Q1, f) != (size_t)N * Q1) return 1; fclose(f);
    pl = malloc(4L * N * Q1); int *c = calloc(N, sizeof(int));
    for (int l = 0; l < N; l++) for (int k = 0; k < Q1; k++) { int p = lp[(size_t)l * Q1 + k]; pl[(size_t)p * Q1 + c[p]++] = l; }
    int r = atoi(argv[2]), L = 2 * r + 1; rs ^= (uint64_t)atoll(argv[3]) * 0x2545F4914F6CDD1DULL; for (int i = 0; i < 10; i++) rnd();
    int partial = getenv("PARTIAL") != NULL, nh = partial ? 1 : r;   /* hubs per side per point */
    int m; int *R = readints(getenv("RFILE"), &m);
    int *sig = malloc(sizeof(int) * N), *sinv = malloc(sizeof(int) * N); for (int i = 0; i < N; i++) sig[i] = sinv[i] = -1;
    char *inR = calloc(N, 1); for (int j = 0; j < m; j++) { if (inR[R[j]]) { fprintf(stderr, "repeated R point\n"); return 1; } inR[R[j]] = 1; }
    { char *lineHasR = calloc(N, 1); for (int j = 0; j < m; j++) for (int k = 0; k < Q1; k++) { int l = pl[(size_t)R[j] * Q1 + k]; if (lineHasR[l]) { fprintf(stderr, "R not non-collinear\n"); return 1; } lineHasR[l] = 1; } free(lineHasR); }
    if (getenv("DUALFILE")) {
        int nd; int *d = readints(getenv("DUALFILE"), &nd); if (nd != N) { fprintf(stderr, "bad DUALFILE\n"); return 1; }
        for (int p = 0; p < N; p++) { sig[p] = d[p]; if (sinv[d[p]] >= 0) { fprintf(stderr, "not a bijection\n"); return 1; } sinv[d[p]] = p; }
    } else {
        int ns; int *S = readints(getenv("SFILE"), &ns); if (ns < m) { fprintf(stderr, "SFILE too short\n"); return 1; }
        for (int j = 0; j < m; j++) {
            int p = R[j], l = S[j]; if (sig[p] >= 0 || sinv[l] >= 0) { fprintf(stderr, "conflict at %d\n", j); return 1; }
            sig[p] = l; sinv[l] = p; int a[256], na = 0, b[256], nb = 0;
            for (int k = 0; k < Q1; k++) { int ln = pl[(size_t)p * Q1 + k]; for (int t = 0; t < Q1; t++) { int x = lp[(size_t)ln * Q1 + t]; if (x != p) a[na++] = x; } }
            for (int k = 0; k < Q1; k++) { int pt = lp[(size_t)l * Q1 + k]; for (int t = 0; t < Q1; t++) { int y = pl[(size_t)pt * Q1 + t]; if (y != l) b[nb++] = y; } }
            for (int i = nb - 1; i > 0; i--) { int z = rnd() % (i + 1), tt = b[i]; b[i] = b[z]; b[z] = tt; }
            for (int i = 0; i < na; i++) { if (sig[a[i]] >= 0 || sinv[b[i]] >= 0) { fprintf(stderr, "local duality regions overlap (R or S not pairwise opposite)\n"); return 1; } sig[a[i]] = b[i]; sinv[b[i]] = a[i]; }
        }
        int *fp = malloc(sizeof(int) * N), *fl = malloc(sizeof(int) * N), nfp = 0, nfl = 0;
        for (int i = 0; i < N; i++) { if (sig[i] < 0) fp[nfp++] = i; if (sinv[i] < 0) fl[nfl++] = i; }
        for (int i = nfl - 1; i > 0; i--) { int z = rnd() % (i + 1), tt = fl[i]; fl[i] = fl[z]; fl[z] = tt; }
        for (int i = 0; i < nfp; i++) { sig[fp[i]] = fl[i]; sinv[fl[i]] = fp[i]; }
    }
    /* local duality check at every x in R (also non-concurrency of sigma(R) follows) */
    { char *mark = calloc(N, 1); long bad = 0;
      for (int j = 0; j < m; j++) { int x = R[j], s = sig[x];
        for (int k = 0; k < Q1; k++) { int l = lp[(size_t)s * Q1 + k]; for (int t = 0; t < Q1; t++) { int l2 = pl[(size_t)l * Q1 + t]; if (l2 != s) mark[l2] = 1; } }
        for (int k = 0; k < Q1; k++) { int l = pl[(size_t)x * Q1 + k]; for (int t = 0; t < Q1; t++) { int y = lp[(size_t)l * Q1 + t]; if (y != x && !mark[sig[y]]) bad++; } }
        for (int k = 0; k < Q1; k++) { int l = lp[(size_t)s * Q1 + k]; for (int t = 0; t < Q1; t++) mark[pl[(size_t)l * Q1 + t]] = 0; } }
      char *sl = calloc(N, 1); for (int j = 0; j < m; j++) for (int k = 0; k < Q1; k++) { int pt = lp[(size_t)sig[R[j]] * Q1 + k]; if (sl[pt]) bad++; sl[pt] = 1; }
      if (bad) { fprintf(stderr, "local duality / non-concurrency fails (%ld)\n", bad); return 1; } free(mark); free(sl); }
    int Delta = q + 1 + r, d = getenv("NSDEG") ? atoi(getenv("NSDEG")) : Delta - L; if (d > Delta - L) d = Delta - L;
    int H = nh * m;   /* line-side hubs */
    int HP = getenv("HP") ? atoi(getenv("HP")) : H;   /* point-side hubs (<= H; the rest of the freed line slots stay unused) */
    if (HP > H || HP < 0) { fprintf(stderr, "bad HP\n"); return 1; }
    long n = (long)L * 2 * N + H + HP;
    fprintf(stderr, "H(%d), r = %d (%d levels, Delta %d), |R| = %d, %s removal, %d line-side and %d point-side hubs, hub degree %d, n = %ld\n", q, r, L, Delta, m, partial ? "partial" : "full", H, HP, d, n);
    int *NA = NULL, *NB = NULL; long nne = 0;
    if (getenv("NSFILE")) { FILE *g = fopen(getenv("NSFILE"), "r"); int a, b; NA = malloc(sizeof(int) * 2L * (H + HP) * (d + 1)); while (g && fscanf(g, "%d %d", &a, &b) == 2) { NA[2 * nne] = a; NA[2 * nne + 1] = b; nne++; } if (g) fclose(g); }
    else if (HP != H) { fprintf(stderr, "HP != H needs NSFILE\n"); return 1; }
    else if (H <= d) { NA = malloc(sizeof(int) * 2L * H * H); for (int a = 0; a < H; a++) for (int b = 0; b < H; b++) { NA[2 * nne] = a; NA[2 * nne + 1] = b; nne++; } }
    else {
        int *A = malloc(sizeof(int) * H * d), *B = malloc(sizeof(int) * H * d), *perm = malloc(sizeof(int) * H), *fillB = malloc(sizeof(int) * H), ok = 0;
        for (int att = 0; att < 200 && !ok; att++) {
            int built = 1;
            for (int t = 0; t < d && built; t++) {
                /* random perfect matching avoiding the t earlier ones: random permutation, then repair conflicts by swaps */
                for (int i = 0; i < H; i++) perm[i] = i; for (int i = H - 1; i > 0; i--) { int z = rnd() % (i + 1), tt = perm[i]; perm[i] = perm[z]; perm[z] = tt; }
                for (int pass = 0; pass < 1000; pass++) { int conflicts = 0;
                    for (int j = 0; j < H; j++) { int bad = 0; for (int u = 0; u < t; u++) if (A[j * d + u] == perm[j]) bad = 1;
                        if (!bad) continue; conflicts++;
                        for (int tr = 0; tr < 50; tr++) { int k = rnd() % H, ok1 = 1; if (k == j) continue;
                            for (int u = 0; u < t; u++) if (A[j * d + u] == perm[k] || A[k * d + u] == perm[j]) ok1 = 0;
                            if (ok1) { int tt = perm[j]; perm[j] = perm[k]; perm[k] = tt; break; } } }
                    if (!conflicts) break; }
                for (int j = 0; j < H; j++) for (int u = 0; u < t; u++) if (A[j * d + u] == perm[j]) built = 0;
                for (int j = 0; j < H; j++) A[j * d + t] = perm[j]; }
            if (!built) { fprintf(stderr, "hub graph attempt %d: repeated edge, retry\n", att); continue; }
            for (int i = 0; i < H; i++) fillB[i] = 0; for (int j = 0; j < H; j++) for (int t = 0; t < d; t++) { int k = A[j * d + t]; B[k * d + fillB[k]++] = j; }
            ok = hub_ok(H, d, A, B); fprintf(stderr, "hub graph attempt %d: %s\n", att, ok ? "OK" : "fails");
        }
        if (!ok) { fprintf(stderr, "no hub graph found\n"); return 1; }
        NA = malloc(sizeof(int) * 2L * H * d); for (int j = 0; j < H; j++) for (int t = 0; t < d; t++) { NA[2 * nne] = j; NA[2 * nne + 1] = A[j * d + t]; nne++; }
    }
    long nemax = (long)L * N * Q1 + (long)L * N * r + (long)(H + HP) * L + nne + 16;
    int32_t *EU = malloc(4 * nemax), *EW = malloc(4 * nemax); long ne = 0;
#define V_PT(i, p) ((int32_t)((long)(i) * 2 * N + (p)))
#define V_LN(i, l) ((int32_t)((long)(i) * 2 * N + N + (l)))
#define V_HL(t) ((int32_t)((long)L * 2 * N + (t)))
#define V_HP(t) ((int32_t)((long)L * 2 * N + H + (t)))
    for (int i = 0; i < L; i++) for (int l = 0; l < N; l++) for (int k = 0; k < Q1; k++) { EU[ne] = V_PT(i, lp[(size_t)l * Q1 + k]); EW[ne] = V_LN(i, l); ne++; }
    for (int i = 0; i < L; i++) for (int p = 0; p < N; p++) for (int k = 1; k <= r; k++) {
        if (inR[p] && (!partial || k == 1)) continue;
        EU[ne] = V_PT(i, p); EW[ne] = V_LN((i + k) % L, sig[p]); ne++; }
    for (int a = 0; a < nh; a++) for (int j = 0; j < m; j++) for (int i = 0; i < L; i++) {
        EU[ne] = V_HL(a * m + j); EW[ne] = V_PT(i, R[j]); ne++;
        if (a * m + j < HP) { EU[ne] = V_HP(a * m + j); EW[ne] = V_LN(i, sig[R[j]]); ne++; } }
    for (long e = 0; e < nne; e++) { if (NA[2 * e] < 0 || NA[2 * e] >= H || NA[2 * e + 1] < 0 || NA[2 * e + 1] >= HP) { fprintf(stderr, "bad hub edge\n"); return 1; } EU[ne] = V_HL(NA[2 * e]); EW[ne] = V_HP(NA[2 * e + 1]); ne++; }
    int *deg = calloc(n, sizeof(int)); for (long e = 0; e < ne; e++) { deg[EU[e]]++; deg[EW[e]]++; }
    int maxdeg = 0; for (long x = 0; x < n; x++) if (deg[x] > maxdeg) maxdeg = deg[x];
    fprintf(stderr, "graph: n = %ld, edges = %ld, max degree %d\n", n, ne, maxdeg);
    if (!getenv("NOCHECK")) {
        long *st = malloc(sizeof(long) * (n + 1)); st[0] = 0; for (long x = 0; x < n; x++) st[x + 1] = st[x] + deg[x];
        int32_t *adj = malloc(4 * st[n]); long *pos = calloc(n, sizeof(long));
        for (long e = 0; e < ne; e++) { adj[st[EU[e]] + pos[EU[e]]++] = EW[e]; adj[st[EW[e]] + pos[EW[e]]++] = EU[e]; }
        int nrand = getenv("NRAND") ? atoi(getenv("NRAND")) : 1024;
        long nsrc = 0; int32_t *src = malloc(4 * (2L * m * L + 2L * H + nrand + 64));
        for (int j = 0; j < m; j++) for (int i = 0; i < L; i++) { src[nsrc++] = V_PT(i, R[j]); src[nsrc++] = V_LN(i, sig[R[j]]); }
        for (int t = 0; t < H; t++) src[nsrc++] = V_HL(t); for (int t = 0; t < HP; t++) src[nsrc++] = V_HP(t);
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
        printf("q=%d r=%d m=%d n=%ld maxdeg=%d sources=%ld worst_ecc=%d bad=%ld\n", q, r, m, n, maxdeg, nsrc, worst, bad);
    }
    FILE *o = fopen(argv[4], "w"); fprintf(o, "%ld\n", n); for (long e = 0; e < ne; e++) fprintf(o, "%d %d\n", EU[e], EW[e]); fclose(o);
    fprintf(stderr, "wrote %s\n", argv[4]);
    return 0;
}
