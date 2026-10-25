/* hubfar.c: BFS (bit-parallel, 64 sources per batch) from every source in a list, to depth D; prints every vertex not
   reached within D as "far SRC TGT".  With the hub ids as sources and D = 7 this is the hub part of the (15,7) check:
   the one-transition surgery theorem covers all pairs of non-hub vertices, so the graph has diameter <= 7 iff no line
   is printed (and it prints the max eccentricity over the sources, and degree / bipartite facts).
   usage: hubfar EDGES D T SOURCES.txt     (SOURCES: ids, or a range "lo hi" on the first line prefixed by 'R') */
#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
static long n, *st; static int *adj; static long *srcs, nsrc; static int D;
static long next_s0 = 0; static int diam = 0; static long nfar = 0;
static pthread_mutex_t mu = PTHREAD_MUTEX_INITIALIZER;
static void *work(void *unused) {
    uint64_t *vis = malloc(n * 8), *fr = malloc(n * 8), *nx = malloc(n * 8); int my = 0;
    for (;;) {
        pthread_mutex_lock(&mu); long s0 = next_s0; next_s0 += 64; pthread_mutex_unlock(&mu);
        if (s0 >= nsrc) break;
        memset(vis, 0, n * 8); memset(fr, 0, n * 8);
        int ns = (nsrc - s0 < 64) ? (int)(nsrc - s0) : 64; uint64_t full = ns == 64 ? ~0ULL : ((1ULL << ns) - 1);
        for (int k = 0; k < ns; k++) { vis[srcs[s0 + k]] |= 1ULL << k; fr[srcs[s0 + k]] |= 1ULL << k; }
        int lev = 0;
        for (;;) { int any = 0;
            for (long x = 0; x < n; x++) { uint64_t acc = 0; for (long i = st[x]; i < st[x + 1]; i++) acc |= fr[adj[i]]; acc &= ~vis[x]; nx[x] = acc; if (acc) any = 1; }
            if (!any) break; lev++; for (long x = 0; x < n; x++) vis[x] |= nx[x]; uint64_t *tmp = fr; fr = nx; nx = tmp;
            if (lev == D) break; }
        long loc = 0;
        for (long x = 0; x < n; x++) if (vis[x] != full) {
            uint64_t m = full & ~vis[x];
            pthread_mutex_lock(&mu);
            for (int k = 0; k < ns; k++) if (m >> k & 1) { if (nfar < 2000000) printf("far %ld %ld\n", srcs[s0 + k], x); nfar++; loc++; }
            pthread_mutex_unlock(&mu);
        }
        if (loc) lev = D + 1;
        if (lev > my) my = lev;
    }
    pthread_mutex_lock(&mu); if (my > diam) diam = my; pthread_mutex_unlock(&mu);
    free(vis); free(fr); free(nx); return NULL;
}
int main(int c, char **v) {
    if (c < 5) { fprintf(stderr, "usage: hubfar EDGES D T SOURCES\n"); return 1; }
    FILE *f = fopen(v[1], "r"); D = atoi(v[2]); int T = atoi(v[3]); long m = 0, cap = 1 << 20;
    if (fscanf(f, "%ld", &n) != 1) return 2;
    int *U = malloc(cap * 4), *W = malloc(cap * 4); long a, b;
    while (fscanf(f, "%ld %ld", &a, &b) == 2) { if (m == cap) { cap *= 2; U = realloc(U, cap * 4); W = realloc(W, cap * 4); } U[m] = a; W[m] = b; m++; }
    fclose(f);
    long *deg = calloc(n + 1, 8);
    for (long i = 0; i < m; i++) { if (U[i] == W[i] || U[i] < 0 || W[i] < 0 || U[i] >= n || W[i] >= n) { printf("BAD edge %ld\n", i); return 1; } deg[U[i]]++; deg[W[i]]++; }
    st = calloc(n + 1, 8); for (long i = 0; i < n; i++) st[i + 1] = st[i] + deg[i];
    adj = malloc(2 * m * 4); long *pos = calloc(n, 8);
    for (long i = 0; i < m; i++) { adj[st[U[i]] + pos[U[i]]++] = W[i]; adj[st[W[i]] + pos[W[i]]++] = U[i]; }
    free(U); free(W);
    long maxd = 0, mind = n;
    for (long x = 0; x < n; x++) { long k = deg[x]; if (k > maxd) maxd = k; if (k < mind) mind = k;
        for (long i = st[x]; i < st[x + 1]; i++) for (long j = i + 1; j < st[x + 1]; j++) if (adj[i] == adj[j]) { printf("repeated edge at %ld\n", x); return 1; } }
    int *col = malloc(n * sizeof(int)); for (long i = 0; i < n; i++) col[i] = -1;
    long *qq = malloc(n * 8); long h = 0, t = 0; col[0] = 0; qq[t++] = 0; int bip = 1;
    while (h < t) { long x = qq[h++]; for (long i = st[x]; i < st[x + 1]; i++) { long y = adj[i]; if (col[y] < 0) { col[y] = 1 - col[x]; qq[t++] = y; } else if (col[y] == col[x]) bip = 0; } }
    FILE *fs = fopen(v[4], "r"); long cs = 1024; srcs = malloc(cs * 8); nsrc = 0; char tag[8];
    if (fscanf(fs, " %1[R]", tag) == 1) { long lo, hi; if (fscanf(fs, "%ld %ld", &lo, &hi) != 2) return 2; srcs = realloc(srcs, (hi - lo) * 8); for (long s = lo; s < hi; s++) srcs[nsrc++] = s; }
    else { long s; while (fscanf(fs, "%ld", &s) == 1) { if (nsrc == cs) { cs *= 2; srcs = realloc(srcs, cs * 8); } srcs[nsrc++] = s; } }
    fclose(fs);
    fprintf(stderr, "n=%ld edges=%ld degree min=%ld max=%ld bipartite=%s connected=%s sources=%ld\n", n, m, mind, maxd, bip ? "yes" : "no", t == n ? "yes" : "no", nsrc);
    pthread_t *th = malloc(T * sizeof(pthread_t));
    for (int i = 0; i < T; i++) pthread_create(&th[i], NULL, work, NULL);
    for (int i = 0; i < T; i++) pthread_join(th[i], NULL);
    printf("n=%ld edges=%ld degree min=%ld max=%ld bipartite=%s connected=%s sources=%ld far_pairs=%ld max_ecc=%s%d\n", n, m, mind, maxd,
           bip ? "yes" : "no", t == n ? "yes" : "no", nsrc, nfar, nfar ? ">" : "", nfar ? D : diam);
    return 0;
}
