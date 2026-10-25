/* orbcat.c: diagnostic companion of research/lifts/coordinator_check/apsp_orb.c for level-cover graphs.
   Same layout (L levels of B vertices, then hubs; the level shift v -> (v + B) mod L*B fixing hubs is checked edge by
   edge to be an automorphism). BFS to depth D from one vertex per orbit (level 0 and all hubs) and, instead of stopping
   at the first miss, counts ordered pairs (source, target) at distance > D by type: main-main, main-hub, hub-main,
   hub-hub. Each level-0 source stands for its L shifts, so main-source counts are multiplied by L.
   With argument FREED (a file of vertex ids, optional) it also counts misses whose source is in that list.
   Usage: orbcat EDGES D T L B [listfile]          build: cc -O2 -pthread -o orbcat orbcat.c */
#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
static long n, *st, *adj, *src, nsrc, LB, B, L; static int D;
static long next_k = 0; static long long miss[4]; static long long *missby; static long worst_src = -1; static long long worst = 0;
static pthread_mutex_t mu = PTHREAD_MUTEX_INITIALIZER;
static int cmpl(const void *a, const void *b) { long x = *(const long *)a, y = *(const long *)b; return x < y ? -1 : x > y; }
static int has_edge(long u, long v) {
    long lo = st[u], hi = st[u + 1] - 1;
    while (lo <= hi) { long m = (lo + hi) / 2; if (adj[m] == v) return 1; if (adj[m] < v) lo = m + 1; else hi = m - 1; }
    return 0;
}
static void *work(void *unused) {
    uint64_t *vis = malloc(n * 8), *fr = malloc(n * 8), *nx = malloc(n * 8);
    long long loc[4] = {0, 0, 0, 0}; long long *cnt = calloc(64, sizeof(long long));
    for (;;) {
        pthread_mutex_lock(&mu); long k0 = next_k; next_k += 64; pthread_mutex_unlock(&mu);
        if (k0 >= nsrc) break;
        memset(vis, 0, n * 8); memset(fr, 0, n * 8);
        int ns = (nsrc - k0 < 64) ? (int)(nsrc - k0) : 64; uint64_t full = ns == 64 ? ~0ULL : ((1ULL << ns) - 1);
        for (int k = 0; k < ns; k++) { vis[src[k0 + k]] |= 1ULL << k; fr[src[k0 + k]] |= 1ULL << k; }
        for (int lev = 1; lev <= D; lev++) {
            for (long x = 0; x < n; x++) { uint64_t acc = 0; for (long i = st[x]; i < st[x + 1]; i++) acc |= fr[adj[i]]; acc &= ~vis[x]; nx[x] = acc; }
            for (long x = 0; x < n; x++) vis[x] |= nx[x]; uint64_t *tmp = fr; fr = nx; nx = tmp;
        }
        memset(cnt, 0, 64 * sizeof(long long));
        for (long x = 0; x < n; x++) { uint64_t m = ~vis[x] & full; if (!m) continue; int th = x >= LB;
            while (m) { int k = __builtin_ctzll(m); m &= m - 1; int sh = src[k0 + k] >= LB; loc[sh * 2 + th] += sh ? 1 : L; cnt[k]++; } }
        pthread_mutex_lock(&mu);
        for (int k = 0; k < ns; k++) { missby[k0 + k] = cnt[k]; if (cnt[k] > worst) { worst = cnt[k]; worst_src = src[k0 + k]; } }
        pthread_mutex_unlock(&mu);
    }
    pthread_mutex_lock(&mu); for (int i = 0; i < 4; i++) miss[i] += loc[i]; pthread_mutex_unlock(&mu);
    free(vis); free(fr); free(nx); free(cnt); return NULL;
}
int main(int c, char **v) {
    if (c < 6) { printf("usage: orbcat EDGES D T L B [listfile]\n"); return 2; }
    FILE *f = fopen(v[1], "r"); D = atoi(v[2]); int T = atoi(v[3]); L = atol(v[4]); B = atol(v[5]); long m = 0, cap = 1 << 20;
    if (!f || fscanf(f, "%ld", &n) != 1) return 2;
    long *U = malloc(cap * 8), *W = malloc(cap * 8); long a, b;
    while (fscanf(f, "%ld %ld", &a, &b) == 2) { if (m == cap) { cap *= 2; U = realloc(U, cap * 8); W = realloc(W, cap * 8); } U[m] = a; W[m] = b; m++; }
    long *deg = calloc(n + 1, 8);
    for (long i = 0; i < m; i++) { if (U[i] == W[i] || U[i] < 0 || W[i] < 0 || U[i] >= n || W[i] >= n) { printf("BAD edge %ld\n", i); return 1; } deg[U[i]]++; deg[W[i]]++; }
    st = calloc(n + 1, 8); for (long i = 0; i < n; i++) st[i + 1] = st[i] + deg[i];
    adj = malloc(2 * m * 8); long *pos = calloc(n, 8);
    for (long i = 0; i < m; i++) { adj[st[U[i]] + pos[U[i]]++] = W[i]; adj[st[W[i]] + pos[W[i]]++] = U[i]; }
    long maxd = 0, mind = n;
    for (long x = 0; x < n; x++) { long k = deg[x]; if (k > maxd) maxd = k; if (k < mind) mind = k; qsort(adj + st[x], k, 8, cmpl);
        for (long i = st[x] + 1; i < st[x + 1]; i++) if (adj[i] == adj[i - 1]) { printf("repeated edge at %ld\n", x); return 1; } }
    LB = L * B;
    for (long i = 0; i < m; i++) { long pu = U[i] < LB ? (U[i] + B) % LB : U[i], pv = W[i] < LB ? (W[i] + B) % LB : W[i];
        if (!has_edge(pu, pv)) { printf("level shift is not an automorphism (edge %ld %ld)\n", U[i], W[i]); return 1; } }
    nsrc = B + (n - LB); src = malloc(nsrc * 8); missby = calloc(nsrc, sizeof(long long));
    for (long i = 0; i < B; i++) src[i] = i;
    for (long i = LB; i < n; i++) src[B + i - LB] = i;
    pthread_t *th = malloc(T * sizeof(pthread_t));
    for (int i = 0; i < T; i++) pthread_create(&th[i], NULL, work, NULL);
    for (int i = 0; i < T; i++) pthread_join(th[i], NULL);
    printf("n=%ld edges=%ld degree min=%ld max=%ld; ordered pairs at distance > %d: main-main %lld, main-hub %lld, hub-main %lld, hub-hub %lld\n",
           n, m, mind, maxd, D, miss[0], miss[1], miss[2], miss[3]);
    long bad0 = 0, badh = 0; for (long k = 0; k < nsrc; k++) if (missby[k]) { if (src[k] < LB) bad0++; else badh++; }
    printf("sources with misses: level-0 %ld of %ld, hubs %ld of %ld; worst source %ld (%lld misses)\n", bad0, B, badh, n - LB, worst_src, worst);
    if (c > 6) { FILE *g = fopen(v[6], "r"); long x; long long tot = 0; long cntl = 0; char *in = calloc(n, 1);
        while (g && fscanf(g, "%ld", &x) == 1) if (x >= 0 && x < n) in[x] = 1;
        for (long k = 0; k < nsrc; k++) if (in[src[k]]) { tot += missby[k]; cntl++; }
        printf("listed sources: %ld, their misses %lld\n", cntl, tot); }
    for (long k = 0, shown = 0; k < nsrc && shown < 12; k++) if (missby[k]) { printf("  src %ld misses %lld\n", src[k], missby[k]); shown++; }
    return 0;
}
