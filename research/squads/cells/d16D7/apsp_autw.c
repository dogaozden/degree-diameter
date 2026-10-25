/* apsp_autw.c: apsp_aut.c with int32 adjacency and 64*WW sources per batch (WW = 8: 512 sources, one cache line per vertex
   per BFS level). Same checks: simple graph, max degree, bipartite, connected, the permutation is a bijection mapping every
   edge to an edge (an automorphism), BFS from one vertex per cycle, exact diameter. cell-16-7 session, 2026-10-25.
   Usage: apsp_autw EDGES d D T AUTFILE      (build: cc -O2 -march=native -pthread -o apsp_autw apsp_autw.c) */
#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#define WW 8
typedef struct { uint64_t w[WW]; } blk;
static long n, nsrc; static int64_t *st; static int32_t *adj; static long *src;
static long next_k = 0; static int diam = 0, bad = 0; static long done_b = 0;
static pthread_mutex_t mu = PTHREAD_MUTEX_INITIALIZER;
static int cmpi(const void *a, const void *b) { int32_t x = *(const int32_t *)a, y = *(const int32_t *)b; return x < y ? -1 : x > y; }
static int has_edge(long u, long v) {
    long lo = st[u], hi = st[u + 1] - 1;
    while (lo <= hi) { long m = (lo + hi) / 2; if (adj[m] == v) return 1; if (adj[m] < v) lo = m + 1; else hi = m - 1; }
    return 0;
}
static void *work(void *unused) {
    blk *vis = aligned_alloc(64, n * sizeof(blk)), *fr = aligned_alloc(64, n * sizeof(blk)), *nx = aligned_alloc(64, n * sizeof(blk)); int my = 0;
    for (;;) {
        pthread_mutex_lock(&mu); long k0 = next_k; next_k += 64 * WW; int stop = bad; pthread_mutex_unlock(&mu);
        if (k0 >= nsrc || stop) break;
        memset(vis, 0, n * sizeof(blk)); memset(fr, 0, n * sizeof(blk));
        long ns = (nsrc - k0 < 64 * WW) ? nsrc - k0 : 64 * WW;
        blk full; memset(&full, 0, sizeof full);
        for (long k = 0; k < ns; k++) { full.w[k >> 6] |= 1ULL << (k & 63); vis[src[k0 + k]].w[k >> 6] |= 1ULL << (k & 63); fr[src[k0 + k]].w[k >> 6] |= 1ULL << (k & 63); }
        int lev = 0;
        for (;;) { int any = 0;
            for (long x = 0; x < n; x++) {
                blk acc; memset(&acc, 0, sizeof acc);
                for (int64_t i = st[x]; i < st[x + 1]; i++) { const blk *f = &fr[adj[i]]; for (int t = 0; t < WW; t++) acc.w[t] |= f->w[t]; }
                uint64_t o = 0; for (int t = 0; t < WW; t++) { acc.w[t] &= ~vis[x].w[t]; o |= acc.w[t]; }
                nx[x] = acc; if (o) any = 1;
            }
            if (!any) break; lev++;
            for (long x = 0; x < n; x++) for (int t = 0; t < WW; t++) vis[x].w[t] |= nx[x].w[t];
            blk *tmp = fr; fr = nx; nx = tmp; }
        for (long x = 0; x < n; x++) { for (int t = 0; t < WW; t++) if (vis[x].w[t] != full.w[t]) { pthread_mutex_lock(&mu); bad = 1; pthread_mutex_unlock(&mu); break; } if (bad) break; }
        if (lev > my) my = lev;
        pthread_mutex_lock(&mu); done_b++; if (getenv("PROGRESS")) { fprintf(stderr, "batch %ld done (lev %d)\n", done_b, lev); } pthread_mutex_unlock(&mu);
    }
    pthread_mutex_lock(&mu); if (my > diam) diam = my; pthread_mutex_unlock(&mu);
    free(vis); free(fr); free(nx); return NULL;
}
int main(int c, char **v) {
    if (c < 6) { printf("usage: apsp_autw EDGES d D T AUTFILE\n"); return 2; }
    FILE *f = fopen(v[1], "r"); int d = atoi(v[2]), D = atoi(v[3]), T = atoi(v[4]); long m = 0, cap = 1 << 20;
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
    free(pos);
    long maxd = 0, mind = n;
    for (long x = 0; x < n; x++) { long k = deg[x]; if (k > maxd) maxd = k; if (k < mind) mind = k;
        qsort(adj + st[x], k, 4, cmpi);
        for (int64_t i = st[x] + 1; i < st[x + 1]; i++) if (adj[i] == adj[i - 1]) { printf("RESULT INVALID repeated edge at %ld\n", x); return 1; } }
    int32_t *P = malloc(n * 4); FILE *fp = fopen(v[5], "rb");
    if (!fp || fread(P, 4, n, fp) != (size_t)n) { printf("RESULT INVALID cannot read %ld permutation entries\n", n); return 1; } fclose(fp);
    char *hit = calloc(n, 1);
    for (long x = 0; x < n; x++) { if (P[x] < 0 || P[x] >= n || hit[P[x]]) { printf("RESULT INVALID not a permutation (at %ld)\n", x); return 1; } hit[P[x]] = 1; }
    for (long i = 0; i < m; i++) if (!has_edge(P[U[i]], P[W[i]])) { printf("RESULT INVALID the permutation is not an automorphism (edge %d %d)\n", U[i], W[i]); return 1; }
    free(U); free(W);
    int *col = malloc(n * sizeof(int)); for (long i = 0; i < n; i++) col[i] = -1;
    long *qq = malloc(n * 8); long h = 0, t = 0; col[0] = 0; qq[t++] = 0; int bip = 1;
    while (h < t) { long x = qq[h++]; for (int64_t i = st[x]; i < st[x + 1]; i++) { long y = adj[i]; if (col[y] < 0) { col[y] = 1 - col[x]; qq[t++] = y; } else if (col[y] == col[x]) bip = 0; } }
    if (t != n) { printf("RESULT INVALID disconnected (%ld of %ld)\n", t, n); return 1; }
    free(qq); free(col);
    memset(hit, 0, n); src = malloc(n * 8); nsrc = 0; long maxcyc = 0;
    for (long x = 0; x < n; x++) if (!hit[x]) { src[nsrc++] = x; long y = x, len = 0; while (!hit[y]) { hit[y] = 1; y = P[y]; len++; } if (len > maxcyc) maxcyc = len; }
    free(hit); free(P);
    fprintf(stderr, "n=%ld m=%ld sources=%ld batches=%ld\n", n, m, nsrc, (nsrc + 64 * WW - 1) / (64 * WW));
    pthread_t *th = malloc(T * sizeof(pthread_t));
    for (int i = 0; i < T; i++) pthread_create(&th[i], NULL, work, NULL);
    for (int i = 0; i < T; i++) pthread_join(th[i], NULL);
    if (bad) { printf("RESULT INVALID unreached\n"); return 1; }
    printf("n=%ld edges=%ld degree min=%ld max=%ld bipartite=%s diameter=%d (permutation checked as an automorphism; %ld sources = cycles, longest %ld)\n",
           n, m, mind, maxd, bip ? "yes" : "no", diam, nsrc, maxcyc);
    if (bip && maxd <= d && diam <= D) printf("RESULT VALID d=%d D=%d n=%ld\n", d, D, n); else printf("RESULT INVALID\n");
    return 0;
}
