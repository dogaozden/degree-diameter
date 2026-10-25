/* apsp_mt.c for level-cover graphs: same checks (simple, max degree, bipartite, connected, exact diameter), but BFS only from
   one vertex per orbit of a cyclic level shift, after checking edge by edge that the shift is an automorphism.
   Layout assumed: vertices [0, L*B) are L levels of B vertices each, vertices [L*B, n) are hubs. The shift maps v to
   (v + B) mod L*B on levels and fixes every hub. If it maps every edge to an edge it is an automorphism (a bijection that
   maps E into E maps E onto E), eccentricity is constant on orbits, and the sources [0, B) plus all hubs meet every orbit,
   so the largest eccentricity among them is the diameter.
   Usage: apsp_orb EDGES d D T L B       (build: cc -O2 -pthread -o apsp_orb apsp_orb.c) */
#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
static long n, *st, *adj, *src, nsrc;
static long next_k = 0; static int diam = 0, bad = 0;
static pthread_mutex_t mu = PTHREAD_MUTEX_INITIALIZER;
static int cmpl(const void *a, const void *b) { long x = *(const long *)a, y = *(const long *)b; return x < y ? -1 : x > y; }
static int has_edge(long u, long v) {
    long lo = st[u], hi = st[u + 1] - 1;
    while (lo <= hi) { long m = (lo + hi) / 2; if (adj[m] == v) return 1; if (adj[m] < v) lo = m + 1; else hi = m - 1; }
    return 0;
}
static void *work(void *unused) {
    uint64_t *vis = malloc(n * 8), *fr = malloc(n * 8), *nx = malloc(n * 8); int my = 0;
    for (;;) {
        pthread_mutex_lock(&mu); long k0 = next_k; next_k += 64; int stop = bad; pthread_mutex_unlock(&mu);
        if (k0 >= nsrc || stop) break;
        memset(vis, 0, n * 8); memset(fr, 0, n * 8);
        int ns = (nsrc - k0 < 64) ? (int)(nsrc - k0) : 64; uint64_t full = ns == 64 ? ~0ULL : ((1ULL << ns) - 1);
        for (int k = 0; k < ns; k++) { vis[src[k0 + k]] |= 1ULL << k; fr[src[k0 + k]] |= 1ULL << k; }
        int lev = 0;
        for (;;) { int any = 0;
            for (long x = 0; x < n; x++) { uint64_t acc = 0; for (long i = st[x]; i < st[x + 1]; i++) acc |= fr[adj[i]]; acc &= ~vis[x]; nx[x] = acc; if (acc) any = 1; }
            if (!any) break; lev++; for (long x = 0; x < n; x++) vis[x] |= nx[x]; uint64_t *tmp = fr; fr = nx; nx = tmp; }
        for (long x = 0; x < n; x++) if (vis[x] != full) { pthread_mutex_lock(&mu); bad = 1; pthread_mutex_unlock(&mu); break; }
        if (lev > my) my = lev;
    }
    pthread_mutex_lock(&mu); if (my > diam) diam = my; pthread_mutex_unlock(&mu);
    free(vis); free(fr); free(nx); return NULL;
}
int main(int c, char **v) {
    if (c < 7) { printf("usage: apsp_orb EDGES d D T L B\n"); return 2; }
    FILE *f = fopen(v[1], "r"); int d = atoi(v[2]), D = atoi(v[3]), T = atoi(v[4]); long L = atol(v[5]), B = atol(v[6]), m = 0, cap = 1 << 20;
    if (fscanf(f, "%ld", &n) != 1) return 2;
    if (L < 1 || B < 1 || L * B > n) { printf("BAD layout L=%ld B=%ld n=%ld\n", L, B, n); return 2; }
    long *U = malloc(cap * 8), *W = malloc(cap * 8); long a, b;
    while (fscanf(f, "%ld %ld", &a, &b) == 2) { if (m == cap) { cap *= 2; U = realloc(U, cap * 8); W = realloc(W, cap * 8); } U[m] = a; W[m] = b; m++; }
    long *deg = calloc(n + 1, 8);
    for (long i = 0; i < m; i++) { if (U[i] == W[i] || U[i] < 0 || W[i] < 0 || U[i] >= n || W[i] >= n) { printf("BAD edge %ld\n", i); return 1; } deg[U[i]]++; deg[W[i]]++; }
    st = calloc(n + 1, 8); for (long i = 0; i < n; i++) st[i + 1] = st[i] + deg[i];
    adj = malloc(2 * m * 8); long *pos = calloc(n, 8);
    for (long i = 0; i < m; i++) { adj[st[U[i]] + pos[U[i]]++] = W[i]; adj[st[W[i]] + pos[W[i]]++] = U[i]; }
    long maxd = 0, mind = n;
    for (long x = 0; x < n; x++) { long k = deg[x]; if (k > maxd) maxd = k; if (k < mind) mind = k;
        qsort(adj + st[x], k, 8, cmpl);
        for (long i = st[x] + 1; i < st[x + 1]; i++) if (adj[i] == adj[i - 1]) { printf("RESULT INVALID repeated edge at %ld\n", x); return 1; } }
    long LB = L * B;
    for (long i = 0; i < m; i++) {
        long pu = U[i] < LB ? (U[i] + B) % LB : U[i], pv = W[i] < LB ? (W[i] + B) % LB : W[i];
        if (!has_edge(pu, pv)) { printf("RESULT INVALID the level shift is not an automorphism (edge %ld %ld)\n", U[i], W[i]); return 1; }
    }
    int *col = malloc(n * sizeof(int)); for (long i = 0; i < n; i++) col[i] = -1;
    long *q = malloc(n * 8); long h = 0, t = 0; col[0] = 0; q[t++] = 0; int bip = 1;
    while (h < t) { long x = q[h++]; for (long i = st[x]; i < st[x + 1]; i++) { long y = adj[i]; if (col[y] < 0) { col[y] = 1 - col[x]; q[t++] = y; } else if (col[y] == col[x]) bip = 0; } }
    if (t != n) { printf("RESULT INVALID disconnected (%ld of %ld)\n", t, n); return 1; }
    nsrc = B + (n - LB); src = malloc(nsrc * 8);
    for (long i = 0; i < B; i++) src[i] = i;
    for (long i = LB; i < n; i++) src[B + i - LB] = i;
    pthread_t *th = malloc(T * sizeof(pthread_t));
    for (int i = 0; i < T; i++) pthread_create(&th[i], NULL, work, NULL);
    for (int i = 0; i < T; i++) pthread_join(th[i], NULL);
    if (bad) { printf("RESULT INVALID unreached\n"); return 1; }
    printf("n=%ld edges=%ld degree min=%ld max=%ld bipartite=%s diameter=%d (level shift L=%ld B=%ld checked as an automorphism; %ld sources)\n",
           n, m, mind, maxd, bip ? "yes" : "no", diam, L, B, nsrc);
    if (bip && maxd <= d && diam <= D) printf("RESULT VALID d=%d D=%d n=%ld\n", d, D, n); else printf("RESULT INVALID\n");
    return 0;
}
