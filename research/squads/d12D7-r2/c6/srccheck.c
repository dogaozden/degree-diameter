/* srccheck.c: BFS (bit-parallel, 64 sources per pass, T threads) from every source in [a, b) to depth D; reports the
   number of (source, target) pairs at distance > D, the worst source and the largest eccentricity seen. Also checks
   simple, max degree, bipartite, connected. Use with a = first hub id to check all hub rows of the distance matrix
   (with main-main pairs settled separately, e.g. by an apsp of the graph without hubs).
   Usage: srccheck EDGES d D T a b       build: cc -O2 -pthread -o srccheck srccheck.c */
#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
static long n, *st, *adj, A, Bend; static int D;
static long next_k; static long long missTot = 0; static long worst = -1; static long long worstc = 0; static int ecc = 0;
static pthread_mutex_t mu = PTHREAD_MUTEX_INITIALIZER;
static int cmpl(const void *a, const void *b) { long x = *(const long *)a, y = *(const long *)b; return x < y ? -1 : x > y; }
static void *work(void *u) {
    uint64_t *vis = malloc(n * 8), *fr = malloc(n * 8), *nx = malloc(n * 8); long long cnt[64];
    for (;;) {
        pthread_mutex_lock(&mu); long k0 = next_k; next_k += 64; pthread_mutex_unlock(&mu);
        if (k0 >= Bend) break;
        int ns = (Bend - k0 < 64) ? (int)(Bend - k0) : 64; uint64_t full = ns == 64 ? ~0ULL : ((1ULL << ns) - 1);
        memset(vis, 0, n * 8); memset(fr, 0, n * 8);
        for (int k = 0; k < ns; k++) { vis[k0 + k] |= 1ULL << k; fr[k0 + k] |= 1ULL << k; }
        int lev = 0;
        for (;;) { int any = 0;
            for (long x = 0; x < n; x++) { uint64_t acc = 0; for (long i = st[x]; i < st[x + 1]; i++) acc |= fr[adj[i]]; acc &= ~vis[x]; nx[x] = acc; if (acc) any = 1; }
            if (!any) break; lev++; for (long x = 0; x < n; x++) vis[x] |= nx[x]; uint64_t *t = fr; fr = nx; nx = t;
            if (lev >= D) { /* stop at depth D: count what is missing */ break; } }
        memset(cnt, 0, sizeof cnt);
        for (long x = 0; x < n; x++) { uint64_t m = ~vis[x] & full; while (m) { int k = __builtin_ctzll(m); m &= m - 1; cnt[k]++; } }
        pthread_mutex_lock(&mu);
        for (int k = 0; k < ns; k++) { missTot += cnt[k]; if (cnt[k] > worstc) { worstc = cnt[k]; worst = k0 + k; } }
        if (lev > ecc) ecc = lev;
        pthread_mutex_unlock(&mu);
    }
    free(vis); free(fr); free(nx); return NULL;
}
int main(int c, char **v) {
    if (c < 7) { printf("usage: srccheck EDGES d D T a b\n"); return 2; }
    FILE *f = fopen(v[1], "r"); int d = atoi(v[2]); D = atoi(v[3]); int T = atoi(v[4]); A = atol(v[5]); Bend = atol(v[6]); long m = 0, cap = 1 << 20;
    if (!f || fscanf(f, "%ld", &n) != 1) return 2; if (Bend > n) Bend = n; next_k = A;
    long *U = malloc(cap * 8), *W = malloc(cap * 8); long a, b;
    while (fscanf(f, "%ld %ld", &a, &b) == 2) { if (m == cap) { cap *= 2; U = realloc(U, cap * 8); W = realloc(W, cap * 8); } U[m] = a; W[m] = b; m++; }
    long *deg = calloc(n + 1, 8);
    for (long i = 0; i < m; i++) { if (U[i] == W[i] || U[i] < 0 || W[i] < 0 || U[i] >= n || W[i] >= n) { printf("BAD edge %ld\n", i); return 1; } deg[U[i]]++; deg[W[i]]++; }
    st = calloc(n + 1, 8); for (long i = 0; i < n; i++) st[i + 1] = st[i] + deg[i];
    adj = malloc(2 * m * 8); long *pos = calloc(n, 8);
    for (long i = 0; i < m; i++) { adj[st[U[i]] + pos[U[i]]++] = W[i]; adj[st[W[i]] + pos[W[i]]++] = U[i]; }
    long maxd = 0, mind = n;
    for (long x = 0; x < n; x++) { long k = deg[x]; if (k > maxd) maxd = k; if (k < mind) mind = k; qsort(adj + st[x], k, 8, cmpl);
        for (long i = st[x] + 1; i < st[x + 1]; i++) if (adj[i] == adj[i - 1]) { printf("RESULT INVALID repeated edge at %ld\n", x); return 1; } }
    int *col = malloc(n * sizeof(int)); for (long i = 0; i < n; i++) col[i] = -1;
    long *qq = malloc(n * 8); long h = 0, t = 0; col[0] = 0; qq[t++] = 0; int bip = 1;
    while (h < t) { long x = qq[h++]; for (long i = st[x]; i < st[x + 1]; i++) { long y = adj[i]; if (col[y] < 0) { col[y] = 1 - col[x]; qq[t++] = y; } else if (col[y] == col[x]) bip = 0; } }
    pthread_t *th = malloc(T * sizeof(pthread_t));
    for (int i = 0; i < T; i++) pthread_create(&th[i], NULL, work, NULL);
    for (int i = 0; i < T; i++) pthread_join(th[i], NULL);
    printf("n=%ld edges=%ld degree min=%ld max=%ld bipartite=%s connected=%s; sources [%ld,%ld): pairs at distance > %d: %lld (worst source %ld: %lld)\n",
           n, m, mind, maxd, bip ? "yes" : "no", t == n ? "yes" : "no", A, Bend, D, missTot, worst, worstc);
    printf("%s\n", (missTot == 0 && bip && t == n && maxd <= d) ? "SOURCES OK" : "SOURCES FAIL");
    return 0;
}
