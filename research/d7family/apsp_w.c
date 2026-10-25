/* apsp_w.c: research/lifts/coordinator_check/apsp_mt.c with 512 sources per batch (one cache line per vertex, as in
   research/squads/cells/d16D7/apsp_autw.c) and the bipartite parity trick; still BFS from EVERY vertex, no symmetry.
   Same checks as apsp_mt: simple graph (no loops, no repeated edges), max degree, bipartite, connected, exact
   eccentricity of every vertex (diameter = max). Sources are sorted by colour, so one batch has one colour; at BFS step
   t only vertices of colour (source colour + t) mod 2 can be new, and only those are scanned (half the work). While the
   frontier is small (< n/64 vertices) the step pushes from a frontier list instead of pulling over all vertices, and in
   pull steps a vertex already reached from all 512 sources is skipped.
   Usage: apsp_w EDGES d D [T]     (build: cc -O2 -march=native -pthread -o apsp_w apsp_w.c)   job d7-family 2026-10-25 */
#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#define WW 8
typedef struct { uint64_t w[WW]; } blk;
static long n, nsrc; static int64_t *st; static int32_t *adj; static long *src; static int *col; static long *byc[2], nbyc[2];
static long next_k = 0; static int diam = 0, bad = 0; static long done_b = 0, nbatch = 0, pushdiv = 64;   /* env PUSHDIV */
static pthread_mutex_t mu = PTHREAD_MUTEX_INITIALIZER;
static int cmpi(const void *a, const void *b) { int32_t x = *(const int32_t *)a, y = *(const int32_t *)b; return x < y ? -1 : x > y; }
static void *work(void *unused) {
    blk *vis = aligned_alloc(64, n * sizeof(blk)), *fr = aligned_alloc(64, n * sizeof(blk)); int my = 0;
    int32_t *F = malloc(n * 4), *G = malloc(n * 4), *H = malloc(n * 4); char *mark = calloc(n, 1);
    long nF, nG, nH;                                   /* frontier lists: F = current, H = two steps old */
    for (;;) {
        pthread_mutex_lock(&mu); long k0 = next_k; next_k += 64 * WW; int stop = bad; pthread_mutex_unlock(&mu);
        if (k0 >= nsrc || stop) break;
        long ns = (nsrc - k0 < 64 * WW) ? nsrc - k0 : 64 * WW;
        /* a batch never mixes colours: batches are cut at the colour boundary (see main) */
        int c0 = col[src[k0]];
        for (long k = 0; k < ns; k++) if (col[src[k0 + k]] != c0) { fprintf(stderr, "mixed batch\n"); exit(3); }
        memset(vis, 0, n * sizeof(blk)); memset(fr, 0, n * sizeof(blk));
        blk full; memset(&full, 0, sizeof full);
        nF = 0; nH = 0;
        for (long k = 0; k < ns; k++) { long s0 = src[k0 + k]; full.w[k >> 6] |= 1ULL << (k & 63); vis[s0].w[k >> 6] |= 1ULL << (k & 63); fr[s0].w[k >> 6] |= 1ULL << (k & 63);
            if (!mark[s0]) { mark[s0] = 1; F[nF++] = (int32_t)s0; } }
        for (long i = 0; i < nF; i++) mark[F[i]] = 0;
        int lev = 0, listed = 1;                       /* listed: F holds the whole current frontier */
        for (;;) { int any = 0; int c = (c0 + lev + 1) & 1;           /* colour of the vertices reachable at step lev+1 */
            if (listed && nF < n / pushdiv) {
                /* push from the (small) frontier list: clear the two-steps-old colour-c frontier, then OR into neighbours */
                for (long i = 0; i < nH; i++) memset(&fr[H[i]], 0, sizeof(blk));
                nG = 0;
                for (long i = 0; i < nF; i++) { long u = F[i]; const blk *f = &fr[u];
                    for (int64_t e = st[u]; e < st[u + 1]; e++) { long y = adj[e]; for (int t = 0; t < WW; t++) fr[y].w[t] |= f->w[t];
                        if (!mark[y]) { mark[y] = 1; G[nG++] = (int32_t)y; } } }
                long m2 = 0;
                for (long i = 0; i < nG; i++) { long y = G[i]; mark[y] = 0; uint64_t o = 0;
                    for (int t = 0; t < WW; t++) { fr[y].w[t] &= ~vis[y].w[t]; o |= fr[y].w[t]; vis[y].w[t] |= fr[y].w[t]; }
                    if (o) { G[m2++] = (int32_t)y; any = 1; } else memset(&fr[y], 0, sizeof(blk)); }
                nG = m2;
                int32_t *tp = H; H = F; nH = nF; F = G; nF = nG; G = tp;
            } else {
                /* pull over all colour-c vertices; saturated ones only get their stale frontier cleared */
                long *X = byc[c], nx = nbyc[c];
                for (long ii = 0; ii < nx; ii++) { long x = X[ii];
                    uint64_t sat = ~0ULL; for (int t = 0; t < WW; t++) sat &= ~(vis[x].w[t] ^ full.w[t]);
                    if (sat == ~0ULL) { memset(&fr[x], 0, sizeof(blk)); continue; }
                    blk acc; memset(&acc, 0, sizeof acc);
                    for (int64_t i = st[x]; i < st[x + 1]; i++) { const blk *f = &fr[adj[i]]; for (int t = 0; t < WW; t++) acc.w[t] |= f->w[t]; }
                    uint64_t o = 0; for (int t = 0; t < WW; t++) { acc.w[t] &= ~vis[x].w[t]; o |= acc.w[t]; }
                    fr[x] = acc; if (o) { any = 1; for (int t = 0; t < WW; t++) vis[x].w[t] |= acc.w[t]; } }
                listed = 0;
            }
            if (!any) break; lev++; }
        for (long x = 0; x < n; x++) { for (int t = 0; t < WW; t++) if (vis[x].w[t] != full.w[t]) { pthread_mutex_lock(&mu); bad = 1; pthread_mutex_unlock(&mu); break; } if (bad) break; }
        if (lev > my) my = lev;
        pthread_mutex_lock(&mu); done_b++; if (getenv("PROGRESS") && done_b % atoi(getenv("PROGRESS")) == 0) fprintf(stderr, "batch %ld/%ld done (max lev %d)\n", done_b, nbatch, my); pthread_mutex_unlock(&mu);
    }
    pthread_mutex_lock(&mu); if (my > diam) diam = my; pthread_mutex_unlock(&mu);
    free(vis); free(fr); free(F); free(G); free(H); free(mark); return NULL;
}
int main(int c, char **v) {
    if (c < 4) { printf("usage: apsp_w EDGES d D [T]\n"); return 2; }
    FILE *f = fopen(v[1], "r"); int d = atoi(v[2]), D = atoi(v[3]), T = c > 4 ? atoi(v[4]) : 1; long m = 0, cap = 1 << 20;
    if (!f || fscanf(f, "%ld", &n) != 1) return 2;
    if (n >= (1L << 31)) { printf("n too large for int32\n"); return 2; }
    int32_t *U = malloc(cap * 4), *W = malloc(cap * 4); long a, b;
    while (fscanf(f, "%ld %ld", &a, &b) == 2) {
        if (a == b || a < 0 || b < 0 || a >= n || b >= n) { printf("BAD edge %ld\n", m); return 1; }
        if (m == cap) { cap *= 2; U = realloc(U, cap * 4); W = realloc(W, cap * 4); } U[m] = (int32_t)a; W[m] = (int32_t)b; m++; }
    fclose(f);
    int64_t *deg = calloc(n + 1, 8);
    for (long i = 0; i < m; i++) { deg[U[i]]++; deg[W[i]]++; }
    st = calloc(n + 1, 8); for (long i = 0; i < n; i++) st[i + 1] = st[i] + deg[i];
    adj = malloc(2 * m * 4); int64_t *pos = calloc(n, 8);
    for (long i = 0; i < m; i++) { adj[st[U[i]] + pos[U[i]]++] = W[i]; adj[st[W[i]] + pos[W[i]]++] = U[i]; }
    free(pos); free(U); free(W);
    long maxd = 0, mind = n;
    for (long x = 0; x < n; x++) { long k = deg[x]; if (k > maxd) maxd = k; if (k < mind) mind = k;
        qsort(adj + st[x], k, 4, cmpi);
        for (int64_t i = st[x] + 1; i < st[x + 1]; i++) if (adj[i] == adj[i - 1]) { printf("RESULT INVALID repeated edge at %ld\n", x); return 1; } }
    col = malloc(n * sizeof(int)); for (long i = 0; i < n; i++) col[i] = -1;
    long *qq = malloc(n * 8); long h = 0, t = 0; col[0] = 0; qq[t++] = 0; int bip = 1;
    while (h < t) { long x = qq[h++]; for (int64_t i = st[x]; i < st[x + 1]; i++) { long y = adj[i]; if (col[y] < 0) { col[y] = 1 - col[x]; qq[t++] = y; } else if (col[y] == col[x]) bip = 0; } }
    if (t != n) { printf("RESULT INVALID disconnected (%ld of %ld)\n", t, n); return 1; }
    free(qq);
    if (!bip) { printf("RESULT INVALID not bipartite (the parity trick needs a bipartite graph)\n"); return 1; }
    for (int cc = 0; cc < 2; cc++) { byc[cc] = malloc(n * 8); nbyc[cc] = 0; }
    for (long x = 0; x < n; x++) byc[col[x]][nbyc[col[x]]++] = x;
    /* sources: colour 0 then colour 1, each padded to whole batches by starting colour 1 at a batch boundary */
    long nb0 = (nbyc[0] + 64 * WW - 1) / (64 * WW), nb1 = (nbyc[1] + 64 * WW - 1) / (64 * WW);
    src = malloc((nb0 + nb1) * 64 * WW * 8); nsrc = 0;
    long *batch_src = src; (void)batch_src;
    /* lay out batches explicitly: batch i < nb0 holds colour-0 sources, the rest colour-1 */
    long *tmp = malloc((nb0 + nb1) * 64 * WW * 8); long nt = 0;
    for (long x = 0; x < nbyc[0]; x++) tmp[nt++] = byc[0][x];
    long pad0 = nb0 * 64 * WW - nbyc[0];
    for (long k = 0; k < pad0; k++) tmp[nt++] = byc[0][k % nbyc[0]];   /* repeats only re-check colour-0 vertices */
    for (long x = 0; x < nbyc[1]; x++) tmp[nt++] = byc[1][x];
    free(src); src = tmp; nsrc = nt; nbatch = (nsrc + 64 * WW - 1) / (64 * WW);
    if (getenv("PUSHDIV")) pushdiv = atol(getenv("PUSHDIV"));
    fprintf(stderr, "n=%ld m=%ld colours %ld + %ld, batches=%ld\n", n, m, nbyc[0], nbyc[1], nbatch);
    pthread_t *th = malloc(T * sizeof(pthread_t));
    for (int i = 0; i < T; i++) pthread_create(&th[i], NULL, work, NULL);
    for (int i = 0; i < T; i++) pthread_join(th[i], NULL);
    if (bad) { printf("RESULT INVALID unreached\n"); return 1; }
    printf("n=%ld edges=%ld degree min=%ld max=%ld bipartite=%s diameter=%d (BFS from all %ld vertices)\n", n, m, mind, maxd, bip ? "yes" : "no", diam, n);
    if (bip && maxd <= d && diam <= D) printf("RESULT VALID d=%d D=%d n=%ld\n", d, D, n); else printf("RESULT INVALID\n");
    return 0;
}
