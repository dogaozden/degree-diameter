/* apsp_fast.c: research/lifts/coordinator_check/apsp_mt.c with two changes that leave every result the same:
   (1) a BFS level whose frontier is small (fewer than n/16 vertices) is done by pushing from the frontier list instead
   of pulling over all n vertices; (2) a batch stops as soon as every vertex has been reached by all its sources (a
   further level would find nothing), instead of after one more empty level. Each vertex carries W words (64*W sources
   per batch, W = 4 by default); int adjacency. The same checks (simple, max degree, bipartite, connected, exact
   diameter), BFS from every vertex, no symmetry assumed; batches are shared out over T threads. Optional source range
   [LO, HI) for split runs (the diameter printed is then the largest eccentricity of those sources). Progress on stderr.
   Usage: apsp_fast EDGES d D [T [LO HI]]     (build: cc -O3 -march=native -pthread -o apsp_fast apsp_fast.c) */
#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#ifndef W
#define W 4
#endif
#ifndef SPARSE_DIV
#define SPARSE_DIV 16
#endif
static long n, *st; static int *adj;
static long lo, hi, next_s0, done = 0; static int diam = 0, bad = 0;
static pthread_mutex_t mu = PTHREAD_MUTEX_INITIALIZER;
static void *work(void *unused) {
    size_t sz = (size_t)((n * 8 * W + 63) / 64) * 64;
    uint64_t *vis = aligned_alloc(64, sz), *fr = aligned_alloc(64, sz), *nx = aligned_alloc(64, sz);
    int *list = malloc(n * sizeof(int)), *nlist = malloc(n * sizeof(int));
    int my = 0;
    for (;;) {
        pthread_mutex_lock(&mu); long s0 = next_s0; next_s0 += 64 * W; int stop = bad; pthread_mutex_unlock(&mu);
        if (s0 >= hi || stop) break;
        memset(vis, 0, sz); memset(fr, 0, sz); memset(nx, 0, sz);
        long ns = (hi - s0 < 64 * W) ? hi - s0 : 64 * W;
        uint64_t full[W];
        for (int w = 0; w < W; w++) {
            long k = ns - 64 * w;
            full[w] = k >= 64 ? ~0ULL : (k <= 0 ? 0ULL : ((1ULL << k) - 1));
        }
        long nl = 0;
        for (long k = 0; k < ns; k++) {
            vis[(s0 + k) * W + k / 64] |= 1ULL << (k % 64); fr[(s0 + k) * W + k / 64] |= 1ULL << (k % 64);
            list[nl++] = (int)(s0 + k);
        }
        int lev = 0, sparse = 1;
        for (;;) {
            int any = 0;
            if (sparse) {                                  /* push from the frontier list; nx is all zero here */
                long nn = 0;
                for (long j = 0; j < nl; j++) {
                    long u = list[j]; const uint64_t *f = fr + u * W;
                    for (long i = st[u]; i < st[u + 1]; i++) {
                        long y = adj[i]; uint64_t o = 0, wasz = 0;
                        for (int w = 0; w < W; w++) { uint64_t add = f[w] & ~vis[y * W + w]; wasz |= nx[y * W + w]; nx[y * W + w] |= add; o |= add; }
                        if (o && !wasz) nlist[nn++] = (int)y;
                    }
                }
                for (long j = 0; j < nl; j++) for (int w = 0; w < W; w++) fr[(long)list[j] * W + w] = 0;
                for (long j = 0; j < nn; j++) for (int w = 0; w < W; w++) vis[(long)nlist[j] * W + w] |= nx[(long)nlist[j] * W + w];
                uint64_t *tmp = fr; fr = nx; nx = tmp;     /* nx (the old fr) is all zero again */
                int *tl = list; list = nlist; nlist = tl; nl = nn;
                any = nn > 0;
                if (nn > n / SPARSE_DIV) sparse = 0;
            } else {                                       /* pull over all vertices */
                for (long x = 0; x < n; x++) {
                    uint64_t acc[W];
                    for (int w = 0; w < W; w++) acc[w] = 0;
                    for (long i = st[x]; i < st[x + 1]; i++) { const uint64_t *f = fr + (long)adj[i] * W; for (int w = 0; w < W; w++) acc[w] |= f[w]; }
                    uint64_t o = 0;
                    for (int w = 0; w < W; w++) { acc[w] &= ~vis[x * W + w]; nx[x * W + w] = acc[w]; o |= acc[w]; }
                    if (o) any = 1;
                }
                if (any) { for (long j = 0; j < n * W; j++) vis[j] |= nx[j]; uint64_t *tmp = fr; fr = nx; nx = tmp; }
            }
            if (!any) break;
            lev++;
            int all = 1;                                   /* everything reached: a further level finds nothing */
            for (long x = 0; x < n && all; x++) for (int w = 0; w < W; w++) if (vis[x * W + w] != full[w]) { all = 0; break; }
            if (all) break;
        }
        for (long x = 0; x < n; x++) { int miss = 0; for (int w = 0; w < W; w++) if (vis[x * W + w] != full[w]) miss = 1;
            if (miss) { pthread_mutex_lock(&mu); bad = 1; pthread_mutex_unlock(&mu); break; } }
        if (lev > my) my = lev;
        pthread_mutex_lock(&mu); done += ns;
        if ((done / (64 * W)) % 64 == 0 || done == hi - lo) { fprintf(stderr, "%ld of %ld sources done (%ld)\n", done, hi - lo, (long)time(NULL)); fflush(stderr); }
        pthread_mutex_unlock(&mu);
    }
    pthread_mutex_lock(&mu); if (my > diam) diam = my; pthread_mutex_unlock(&mu);
    free(vis); free(fr); free(nx); free(list); free(nlist); return NULL;
}
int main(int c, char **v) {
    FILE *f = fopen(v[1], "r"); int d = atoi(v[2]), D = atoi(v[3]), T = c > 4 ? atoi(v[4]) : 1; long m = 0, cap = 1 << 20;
    if (fscanf(f, "%ld", &n) != 1) return 2;
    lo = c > 6 ? atol(v[5]) : 0; hi = c > 6 ? atol(v[6]) : n; next_s0 = lo;
    if (lo < 0 || hi > n || lo >= hi) { printf("bad range\n"); return 2; }
    long *U = malloc(cap * 8), *Wd = malloc(cap * 8); long a, b;
    while (fscanf(f, "%ld %ld", &a, &b) == 2) { if (m == cap) { cap *= 2; U = realloc(U, cap * 8); Wd = realloc(Wd, cap * 8); } U[m] = a; Wd[m] = b; m++; }
    long *deg = calloc(n + 1, 8);
    for (long i = 0; i < m; i++) { if (U[i] == Wd[i] || U[i] < 0 || Wd[i] < 0 || U[i] >= n || Wd[i] >= n) { printf("BAD edge %ld\n", i); return 1; } deg[U[i]]++; deg[Wd[i]]++; }
    st = calloc(n + 1, 8); for (long i = 0; i < n; i++) st[i + 1] = st[i] + deg[i];
    adj = malloc(2 * m * 4); long *pos = calloc(n, 8);
    for (long i = 0; i < m; i++) { adj[st[U[i]] + pos[U[i]]++] = (int)Wd[i]; adj[st[Wd[i]] + pos[Wd[i]]++] = (int)U[i]; }
    free(U); free(Wd);
    long maxd = 0, mind = n;
    for (long x = 0; x < n; x++) { long k = deg[x]; if (k > maxd) maxd = k; if (k < mind) mind = k;
        for (long i = st[x]; i < st[x + 1]; i++) for (long j = i + 1; j < st[x + 1]; j++) if (adj[i] == adj[j]) { printf("RESULT INVALID repeated edge at %ld\n", x); return 1; } }
    int *col = malloc(n * sizeof(int)); for (long i = 0; i < n; i++) col[i] = -1;
    long *q = malloc(n * 8); long h = 0, t = 0; col[0] = 0; q[t++] = 0; int bip = 1;
    while (h < t) { long x = q[h++]; for (long i = st[x]; i < st[x + 1]; i++) { long y = adj[i]; if (col[y] < 0) { col[y] = 1 - col[x]; q[t++] = y; } else if (col[y] == col[x]) bip = 0; } }
    if (t != n) { printf("RESULT INVALID disconnected (%ld of %ld)\n", t, n); return 1; }
    pthread_t *th = malloc(T * sizeof(pthread_t));
    for (int i = 0; i < T; i++) pthread_create(&th[i], NULL, work, NULL);
    for (int i = 0; i < T; i++) pthread_join(th[i], NULL);
    if (bad) { printf("RESULT INVALID unreached\n"); return 1; }
    printf("n=%ld edges=%ld degree min=%ld max=%ld bipartite=%s diameter=%d sources=%ld..%ld\n", n, m, mind, maxd, bip ? "yes" : "no", diam, lo, hi);
    if (bip && maxd <= d && diam <= D) printf("RESULT VALID d=%d D=%d n=%ld%s\n", d, D, n, (lo == 0 && hi == n) ? "" : " (sources in the range only)");
    else printf("RESULT INVALID\n");
    return 0;
}
