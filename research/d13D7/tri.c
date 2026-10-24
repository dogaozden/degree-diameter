/* tri.c: three copies of the incidence graph of the split Cayley hexagon H(q), joined by one extra matching
   (p, i) ~ (sigma(p), i+1) for a bijection sigma: points -> lines (the table's (q+2, 7) construction, any sigma works),
   plus "surgeries": for p in R the three matching edges at p are removed, a new vertex v_p is joined to (p, 0), (p, 1),
   (p, 2) and a new vertex u_p to (sigma(p), 0), (sigma(p), 1), (sigma(p), 2).  sigma is a local duality at every
   p in R: sigma(Gamma_2(p)) = Gamma_2(sigma(p)) (points collinear with p -> lines concurrent with sigma(p)).
   R = pairwise opposite points, sigma(R) = pairwise opposite lines.  The new vertices are joined among themselves by
   a bipartite graph NS (v's on one side, u's on the other) of max degree <= 10 so that v-v and u-u distances are <= 6.

   usage: [RFILE=points.txt SFILE=lines.txt] tri HEXFILE m seed [out.edges]
     m     number of surgeries (0 = the plain table construction); m < 0: as many as the greedy finds, or all of
           RFILE/SFILE (pairwise opposite points / lines, one index per line; checked)
     seed  random seed (sigma off the local-duality region, greedy order)
   Checks: BFS from every damaged vertex, every new vertex and 2000 random vertices (exact eccentricities).
   With an output file, writes the edge list in apsp.c format (first line n, then "u v" per edge). */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

static int q, N, Q1;
static int32_t *lp, *pl;           /* lp[l*Q1+k]: points on line l; pl[p*Q1+k]: lines through p */
static uint64_t rng_s;
static uint64_t rnd(void) { rng_s ^= rng_s << 13; rng_s ^= rng_s >> 7; rng_s ^= rng_s << 17; return rng_s; }

/* distances <= maxd from a point (type 0) or line (type 1) in the incidence graph; dist array over 2N ids
   (points 0..N-1, lines N..2N-1), 255 = farther */
static void gh_ball(int id, int maxd, uint8_t *dist, int32_t *queue) {
    memset(dist, 255, 2 * (size_t)N);
    int h = 0, t = 0; dist[id] = 0; queue[t++] = id;
    while (h < t) {
        int x = queue[h++]; if (dist[x] >= maxd) continue;
        const int32_t *nb = (x < N) ? &pl[(size_t)x * Q1] : &lp[(size_t)(x - N) * Q1];
        int off = (x < N) ? N : 0;
        for (int k = 0; k < Q1; k++) { int y = nb[k] + off; if (dist[y] == 255) { dist[y] = dist[x] + 1; queue[t++] = y; } }
    }
}

int main(int argc, char **argv) {
    if (argc < 4) { fprintf(stderr, "usage: tri HEXFILE m seed [out.edges]\n"); return 1; }
    FILE *f = fopen(argv[1], "rb"); int32_t hdr[3];
    if (!f || fread(hdr, 4, 3, f) != 3) { fprintf(stderr, "cannot read %s\n", argv[1]); return 1; }
    q = hdr[0]; N = hdr[1]; Q1 = q + 1;
    lp = malloc(sizeof(int32_t) * (size_t)N * Q1);
    if (fread(lp, 4, (size_t)N * Q1, f) != (size_t)N * Q1) return 1;
    fclose(f);
    pl = malloc(sizeof(int32_t) * (size_t)N * Q1); int *c = calloc(N, sizeof(int));
    for (int l = 0; l < N; l++) for (int k = 0; k < Q1; k++) { int p = lp[(size_t)l * Q1 + k]; pl[(size_t)p * Q1 + c[p]++] = l; }
    int mreq = atoi(argv[2]); rng_s = 0x9E3779B97F4A7C15ULL ^ (uint64_t)atoll(argv[3]) * 0x2545F4914F6CDD1DULL; for (int i = 0; i < 10; i++) rnd();
    fprintf(stderr, "H(%d): %d points, %d lines\n", q, N, N);

    uint8_t *dist = malloc(2 * (size_t)N); int32_t *queue = malloc(sizeof(int32_t) * 2 * (size_t)N);
    /* greedy pairwise-opposite points R and lines S */
    int cap = 4000; int *R = malloc(sizeof(int) * cap), *S = malloc(sizeof(int) * cap); int m = 0;
    uint8_t *blkP = calloc(N, 1), *blkL = calloc(N, 1);
    int *permP = malloc(sizeof(int) * N), *permL = malloc(sizeof(int) * N);
    for (int i = 0; i < N; i++) permP[i] = permL[i] = i;
    for (int i = N - 1; i > 0; i--) { int j = rnd() % (i + 1), t = permP[i]; permP[i] = permP[j]; permP[j] = t; }
    for (int i = N - 1; i > 0; i--) { int j = rnd() % (i + 1), t = permL[i]; permL[i] = permL[j]; permL[j] = t; }
    int ip = 0, il = 0, want = mreq < 0 ? cap : mreq;
    const char *rf = getenv("RFILE"), *sf = getenv("SFILE");
    if (rf || sf) {
        /* R (points) and S (lines) from files, one index per line; both must be pairwise opposite (checked) */
        int *RR = malloc(sizeof(int) * N), *SS = malloc(sizeof(int) * N); int nr = 0, ns = 0; char buf[256];
        FILE *g = rf ? fopen(rf, "r") : NULL; while (g && fgets(buf, sizeof buf, g)) { int v; if (buf[0] != '#' && sscanf(buf, "%d", &v) == 1) RR[nr++] = v; } if (g) fclose(g);
        g = sf ? fopen(sf, "r") : NULL; while (g && fgets(buf, sizeof buf, g)) { int v; if (buf[0] != '#' && sscanf(buf, "%d", &v) == 1) SS[ns++] = v; } if (g) fclose(g);
        int mm = nr < ns ? nr : ns; if (mreq >= 0 && mreq < mm) mm = mreq; if (mm > cap) mm = cap;
        for (int j = 0; j < mm; j++) {
            int p = RR[j], l = SS[j];
            if (blkP[p] || blkL[l]) { fprintf(stderr, "R/S not pairwise opposite at entry %d\n", j); return 1; }
            R[m] = p; S[m] = l; m++;
            gh_ball(p, 4, dist, queue); for (int x = 0; x < N; x++) if (dist[x] <= 4) blkP[x] = 1;
            gh_ball(N + l, 4, dist, queue); for (int x = N; x < 2 * N; x++) if (dist[x] <= 4) blkL[x - N] = 1;
        }
        want = m;
    }
    while (m < want) {
        while (ip < N && blkP[permP[ip]]) ip++;
        while (il < N && blkL[permL[il]]) il++;
        if (ip >= N || il >= N) break;
        int p = permP[ip], l = permL[il];
        R[m] = p; S[m] = l; m++;
        gh_ball(p, 4, dist, queue); for (int x = 0; x < N; x++) if (dist[x] <= 4) blkP[x] = 1;
        gh_ball(N + l, 4, dist, queue); for (int x = N; x < 2 * N; x++) if (dist[x] <= 4) blkL[x - N] = 1;
    }
    fprintf(stderr, "surgeries m = %d (requested %d)\n", m, mreq);

    /* sigma: R -> S, Gamma_2(R_j) -> Gamma_2(S_j), rest random */
    int *sig = malloc(sizeof(int) * N), *sinv = malloc(sizeof(int) * N);
    for (int i = 0; i < N; i++) sig[i] = sinv[i] = -1;
    for (int j = 0; j < m; j++) {
        sig[R[j]] = S[j]; sinv[S[j]] = R[j];
        int a[256], na = 0, b[256], nb = 0;
        int p = R[j], l = S[j];
        for (int k = 0; k < Q1; k++) { int ln = pl[(size_t)p * Q1 + k]; for (int t = 0; t < Q1; t++) { int x = lp[(size_t)ln * Q1 + t]; if (x != p) a[na++] = x; } }
        for (int k = 0; k < Q1; k++) { int pt = lp[(size_t)l * Q1 + k]; for (int t = 0; t < Q1; t++) { int y = pl[(size_t)pt * Q1 + t]; if (y != l) b[nb++] = y; } }
        if (na != nb) { fprintf(stderr, "size mismatch\n"); return 1; }
        for (int i = na - 1; i > 0; i--) { int r2 = rnd() % (i + 1), t = b[i]; b[i] = b[r2]; b[r2] = t; }
        for (int i = 0; i < na; i++) {
            if (sig[a[i]] != -1 || sinv[b[i]] != -1) { fprintf(stderr, "local duality conflict\n"); return 1; }
            sig[a[i]] = b[i]; sinv[b[i]] = a[i];
        }
    }
    int *freeP = malloc(sizeof(int) * N), *freeL = malloc(sizeof(int) * N), nfp = 0, nfl = 0;
    for (int i = 0; i < N; i++) { if (sig[i] < 0) freeP[nfp++] = i; if (sinv[i] < 0) freeL[nfl++] = i; }
    if (nfp != nfl) { fprintf(stderr, "free mismatch\n"); return 1; }
    for (int i = nfl - 1; i > 0; i--) { int j = rnd() % (i + 1), t = freeL[i]; freeL[i] = freeL[j]; freeL[j] = t; }
    for (int i = 0; i < nfp; i++) { sig[freeP[i]] = freeL[i]; sinv[freeL[i]] = freeP[i]; }
    uint8_t *inR = calloc(N, 1); for (int j = 0; j < m; j++) inR[R[j]] = 1;

    /* the graph */
    long n = 6L * N + 2L * m;
    long nedge_max = 3L * N * Q1 + 3L * N + 6L * m + 11L * m + 16;
    int32_t *EU = malloc(sizeof(int32_t) * nedge_max), *EW = malloc(sizeof(int32_t) * nedge_max); long ne = 0;
#define V_PT(i, p) ((int32_t)((long)(i) * 2 * N + (p)))
#define V_LN(i, l) ((int32_t)((long)(i) * 2 * N + N + (l)))
#define V_NEWV(j) ((int32_t)(6L * N + (j)))
#define V_NEWU(j) ((int32_t)(6L * N + m + (j)))
    for (int i = 0; i < 3; i++) for (int l = 0; l < N; l++) for (int k = 0; k < Q1; k++) { EU[ne] = V_PT(i, lp[(size_t)l * Q1 + k]); EW[ne] = V_LN(i, l); ne++; }
    for (int i = 0; i < 3; i++) for (int p = 0; p < N; p++) if (!inR[p]) { EU[ne] = V_PT(i, p); EW[ne] = V_LN((i + 1) % 3, sig[p]); ne++; }
    for (int j = 0; j < m; j++) for (int i = 0; i < 3; i++) {
        EU[ne] = V_NEWV(j); EW[ne] = V_PT(i, R[j]); ne++;
        EU[ne] = V_NEWU(j); EW[ne] = V_LN(i, S[j]); ne++;
    }
    /* NS: v_j ~ u_k, degree nsd = q - 1 (env NSDEG overrides, at most 10).  m <= nsd: complete bipartite.  Otherwise a
       circulant v_j ~ u_{j + c} with nsd random offsets c; the BFS check below decides. */
    int nsd = getenv("NSDEG") ? atoi(getenv("NSDEG")) : q - 1;   /* hub-graph degree: Delta - 3 = q - 1 */
    if (nsd > 10) nsd = 10;
    if (m > 0 && m <= nsd) { for (int j = 0; j < m; j++) for (int k = 0; k < m; k++) { EU[ne] = V_NEWV(j); EW[ne] = V_NEWU(k); ne++; } }
    else if (m > nsd) {
        /* circulant: v_j ~ u_{j + c_t} for 10 offsets c_t chosen as a "Sidon-like" set mod m */
        int offs[10]; int no = 0;
        while (no < nsd) { int cnd = rnd() % m, ok = 1; for (int t = 0; t < no; t++) if (offs[t] == cnd) ok = 0; if (ok) offs[no++] = cnd; }
        for (int j = 0; j < m; j++) for (int t = 0; t < nsd; t++) { EU[ne] = V_NEWV(j); EW[ne] = V_NEWU((j + offs[t]) % m); ne++; }
    }
    fprintf(stderr, "graph: n = %ld, edges = %ld\n", n, ne);

    /* CSR */
    int *deg = calloc(n, sizeof(int));
    for (long e = 0; e < ne; e++) { deg[EU[e]]++; deg[EW[e]]++; }
    long *st = malloc(sizeof(long) * (n + 1)); st[0] = 0; for (long x = 0; x < n; x++) st[x + 1] = st[x] + deg[x];
    int32_t *adj = malloc(sizeof(int32_t) * st[n]); long *pos = calloc(n, sizeof(long));
    for (long e = 0; e < ne; e++) { adj[st[EU[e]] + pos[EU[e]]++] = EW[e]; adj[st[EW[e]] + pos[EW[e]]++] = EU[e]; }
    int maxdeg = 0; for (long x = 0; x < n; x++) if (deg[x] > maxdeg) maxdeg = deg[x];
    /* simple? */
    for (long x = 0; x < n; x++) for (long a = st[x]; a < st[x + 1]; a++) for (long b = a + 1; b < st[x + 1]; b++) if (adj[a] == adj[b]) { fprintf(stderr, "repeated edge at %ld\n", x); return 1; }
    fprintf(stderr, "max degree %d\n", maxdeg);

    /* BFS checks: bit-parallel, 64 sources per pass; exact eccentricities; parallel over passes */
    long nsrc = 0; int32_t *src = malloc(sizeof(int32_t) * (8L * m + 4200));
    for (int j = 0; j < m; j++) { src[nsrc++] = V_NEWV(j); src[nsrc++] = V_NEWU(j); for (int i = 0; i < 3; i++) { src[nsrc++] = V_PT(i, R[j]); src[nsrc++] = V_LN(i, S[j]); } }
    int nrand = getenv("NRAND") ? atoi(getenv("NRAND")) : 2048;
    for (int t = 0; t < nrand; t++) src[nsrc++] = (int32_t)(rnd() % n);
    int worst = 0; long bad = 0;
    long npass = (nsrc + 63) / 64;
    #pragma omp parallel
    {
        uint64_t *vis = malloc(8 * n), *fr = malloc(8 * n), *nx = malloc(8 * n);
        #pragma omp for schedule(dynamic, 1) reduction(max:worst) reduction(+:bad)
        for (long ps = 0; ps < npass; ps++) {
            long s0 = ps * 64; int ns = (nsrc - s0 < 64) ? (int)(nsrc - s0) : 64;
            memset(vis, 0, 8 * n); memset(fr, 0, 8 * n);
            for (int k = 0; k < ns; k++) { vis[src[s0 + k]] |= 1ULL << k; fr[src[s0 + k]] |= 1ULL << k; }
            uint64_t full = (ns == 64) ? ~0ULL : ((1ULL << ns) - 1);
            int ecc[64]; for (int k = 0; k < 64; k++) ecc[k] = 0;
            int lev = 0;
            for (;;) {
                uint64_t anyb = 0;
                for (long x = 0; x < n; x++) { uint64_t acc = 0; for (long a = st[x]; a < st[x + 1]; a++) acc |= fr[adj[a]]; acc &= ~vis[x]; nx[x] = acc; anyb |= acc; }
                if (!anyb) break;
                lev++;
                for (int k = 0; k < ns; k++) if (anyb >> k & 1) ecc[k] = lev;
                for (long x = 0; x < n; x++) vis[x] |= nx[x];
                uint64_t *tmp = fr; fr = nx; nx = tmp;
                if (lev > 9) break;
            }
            uint64_t miss = 0; for (long x = 0; x < n; x++) miss |= full & ~vis[x];
            for (int k = 0; k < ns; k++) {
                int e = (miss >> k & 1) ? 99 : ecc[k];
                if (e > worst) worst = e;
                if (e > 7) { bad++;
                    #pragma omp critical
                    { if (bad <= 10) fprintf(stderr, "source %d: ecc %d\n", src[s0 + k], e); }
                }
            }
        }
        free(vis); free(fr); free(nx);
    }
    /* bipartite check by 2-colouring */
    { int8_t *col = malloc(n); memset(col, -1, n); int32_t *qq = malloc(sizeof(int32_t) * n); long h = 0, t = 0; col[0] = 0; qq[t++] = 0; int bip = 1;
      while (h < t) { int x = qq[h++]; for (long a = st[x]; a < st[x + 1]; a++) { int y = adj[a]; if (col[y] < 0) { col[y] = 1 - col[x]; qq[t++] = y; } else if (col[y] == col[x]) bip = 0; } }
      if (!bip || t != n) { fprintf(stderr, "bipartite=%d connected=%d\n", bip, t == n); return 1; } }
    printf("q=%d m=%d n=%ld maxdeg=%d sources=%ld worst_ecc=%d bad=%ld\n", q, m, n, maxdeg, nsrc, worst, bad);
    if (argc > 4) {
        FILE *o = fopen(argv[4], "w"); fprintf(o, "%ld\n", n);
        for (long e = 0; e < ne; e++) fprintf(o, "%d %d\n", EU[e], EW[e]);
        fclose(o); fprintf(stderr, "wrote %s\n", argv[4]);
    }
    return 0;
}
