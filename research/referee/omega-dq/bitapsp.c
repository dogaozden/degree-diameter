/* bitapsp.c (referee omega-dq): all-pairs check of a small graph, 64 BFS sources at a time, no symmetry used.
   Reads "N" then edges "u v". Prints n, edges, degree range, bipartite, connected, diameter, and for a regular graph
   of degree d the girth: if every source has the largest possible sphere sizes d(d-1)^(i-1) for i <= r and some source
   does not at r+1, then a bipartite graph has girth exactly 2r+2 (2r+1 or 2r+2 in general).
   usage: bitapsp edges.txt [threads] */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <pthread.h>

static int n; static long m; static int *off, *adj;
static int nthreads = 4, nbatch;
#define MAXL 64
static long long lvltot[MAXL]; static int maxecc = 0; static long unreached = 0;
static pthread_mutex_t mu = PTHREAD_MUTEX_INITIALIZER;
static int next_batch = 0;

static void *work(void *arg) {
    (void)arg;
    uint64_t *vis = malloc(8L * n), *fr = malloc(8L * n), *nf = malloc(8L * n);
    long long loc[MAXL] = {0}; int locmax = 0; long locun = 0;
    for (;;) {
        pthread_mutex_lock(&mu); int b = next_batch++; pthread_mutex_unlock(&mu);
        if (b >= nbatch) break;
        int s0 = 64 * b, ns = n - s0 < 64 ? n - s0 : 64;
        uint64_t full = ns == 64 ? ~0ULL : ((1ULL << ns) - 1);
        for (int v = 0; v < n; v++) vis[v] = fr[v] = 0;
        for (int i = 0; i < ns; i++) vis[s0 + i] = fr[s0 + i] = 1ULL << i;
        int lev = 0;
        for (;;) {
            long cnt = 0;
            for (int v = 0; v < n; v++) {
                uint64_t a = 0;
                for (int e = off[v]; e < off[v + 1]; e++) a |= fr[adj[e]];
                a &= ~vis[v]; nf[v] = a;
                cnt += __builtin_popcountll(a);
            }
            if (!cnt) break;
            lev++;
            for (int v = 0; v < n; v++) { vis[v] |= nf[v]; }
            uint64_t *t = fr; fr = nf; nf = t;
            if (lev < MAXL) loc[lev] += cnt;
        }
        if (lev > locmax) locmax = lev;
        for (int v = 0; v < n; v++) locun += __builtin_popcountll(full & ~vis[v]);
    }
    pthread_mutex_lock(&mu);
    for (int i = 0; i < MAXL; i++) lvltot[i] += loc[i];
    if (locmax > maxecc) maxecc = locmax; unreached += locun;
    pthread_mutex_unlock(&mu);
    free(vis); free(fr); free(nf); return NULL;
}

int main(int argc, char **argv) {
    FILE *f = fopen(argv[1], "r"); if (!f) return 1;
    if (argc > 2) nthreads = atoi(argv[2]);
    if (fscanf(f, "%d", &n) != 1) return 1;
    long cap = 1 << 20; int *eu = malloc(4 * cap), *ev = malloc(4 * cap); m = 0;
    int u, v;
    while (fscanf(f, "%d %d", &u, &v) == 2) {
        if (m == cap) { cap *= 2; eu = realloc(eu, 4 * cap); ev = realloc(ev, 4 * cap); }
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) { printf("bad edge %d %d\n", u, v); return 1; }
        eu[m] = u; ev[m] = v; m++;
    }
    off = calloc(n + 1, sizeof(int));
    for (long e = 0; e < m; e++) { off[eu[e] + 1]++; off[ev[e] + 1]++; }
    for (int i = 0; i < n; i++) off[i + 1] += off[i];
    adj = malloc(sizeof(int) * 2 * m); int *pos = malloc(sizeof(int) * n);
    for (int i = 0; i < n; i++) pos[i] = off[i];
    for (long e = 0; e < m; e++) { adj[pos[eu[e]]++] = ev[e]; adj[pos[ev[e]]++] = eu[e]; }
    int dmin = 1 << 30, dmax = 0, multi = 0;
    int *mark = malloc(sizeof(int) * n); for (int i = 0; i < n; i++) mark[i] = -1;
    for (int i = 0; i < n; i++) {
        int d = off[i + 1] - off[i]; if (d < dmin) dmin = d; if (d > dmax) dmax = d;
        for (int e = off[i]; e < off[i + 1]; e++) { if (mark[adj[e]] == i) multi++; mark[adj[e]] = i; }
    }
    /* 2-colouring by BFS */
    int *col = malloc(sizeof(int) * n), *qu = malloc(sizeof(int) * n), bip = 1, comps = 0;
    for (int i = 0; i < n; i++) col[i] = -1;
    for (int s = 0; s < n; s++) if (col[s] < 0) {
        comps++; int h = 0, t = 0; qu[t++] = s; col[s] = 0;
        while (h < t) { int x = qu[h++]; for (int e = off[x]; e < off[x + 1]; e++) { int y = adj[e];
            if (col[y] < 0) { col[y] = 1 - col[x]; qu[t++] = y; } else if (col[y] == col[x]) bip = 0; } }
    }
    printf("n=%d edges=%ld degree min=%d max=%d multi-edges=%d bipartite=%s components=%d\n",
           n, m, dmin, dmax, multi, bip ? "yes" : "no", comps);
    nbatch = (n + 63) / 64;
    pthread_t th[64];
    for (int i = 0; i < nthreads; i++) pthread_create(&th[i], NULL, work, NULL);
    for (int i = 0; i < nthreads; i++) pthread_join(th[i], NULL);
    printf("sphere sizes summed over all %d sources:", n);
    for (int i = 1; i <= maxecc; i++) printf(" %lld", lvltot[i]);
    printf("\nunreached pairs=%ld diameter=%d\n", unreached, unreached ? -1 : maxecc);
    if (dmin == dmax) {
        long long d = dmin, mx = d; int r = 0;
        for (int i = 1; i <= maxecc; i++) { if (lvltot[i] == (long long)n * mx) r = i; else break; mx *= (d - 1); }
        printf("all spheres maximal up to radius %d -> girth %s%d\n", r, bip ? "" : ">= ", 2 * r + (bip ? 2 : 1));
    }
    return 0;
}
