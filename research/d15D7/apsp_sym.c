/* apsp_sym.c: check an edge list for max degree d and diameter D, using a cyclic symmetry that it verifies itself.
   cell-15-7 job, 2026-10-24. Same input format and verdict line as research/lifts/coordinator_check/apsp.c.
   The symmetry: sigma(v) = (v + B) mod (r*B) for v < r*B, sigma(v) = v for v >= r*B (for the (2k+1)-copy hexagon
   graphs B = 2N and r = 2k+1: it rotates the copies and fixes the hubs). The program checks that sigma maps every
   edge to an edge (so sigma is an automorphism), then runs bit-parallel BFS from the vertices 0..B-1 and r*B..n-1,
   which meet every sigma-orbit. Also checks: simple, bipartite, connected, max degree.
   Usage: apsp_sym EDGES d D B r [threads] */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#ifdef _OPENMP
#include <omp.h>
#endif
static int cmpl(const void *a, const void *b) { long x = *(const long *)a, y = *(const long *)b; return x < y ? -1 : x > y; }
int main(int c, char **v) {
    if (c < 6) { fprintf(stderr, "usage: apsp_sym EDGES d D B r [threads]\n"); return 2; }
    FILE *f = fopen(v[1], "r"); int d = atoi(v[2]), D = atoi(v[3]); long B = atol(v[4]); int r = atoi(v[5]);
    int T = c > 6 ? atoi(v[6]) : 1;
    long n, m = 0, cap = 1 << 22;
    if (!f || fscanf(f, "%ld", &n) != 1) return 2;
    long *U = malloc(cap * 8), *W = malloc(cap * 8); long a, b;
    while (fscanf(f, "%ld %ld", &a, &b) == 2) { if (m == cap) { cap *= 2; U = realloc(U, cap * 8); W = realloc(W, cap * 8); } U[m] = a; W[m] = b; m++; }
    fclose(f);
    long *deg = calloc(n + 1, 8);
    for (long i = 0; i < m; i++) { if (U[i] == W[i] || U[i] < 0 || W[i] < 0 || U[i] >= n || W[i] >= n) { printf("RESULT INVALID bad edge %ld\n", i); return 1; } deg[U[i]]++; deg[W[i]]++; }
    long *st = calloc(n + 1, 8); for (long i = 0; i < n; i++) st[i + 1] = st[i] + deg[i];
    long *adj = malloc(2 * m * 8), *pos = calloc(n, 8);
    for (long i = 0; i < m; i++) { adj[st[U[i]] + pos[U[i]]++] = W[i]; adj[st[W[i]] + pos[W[i]]++] = U[i]; }
    free(U); free(W); free(pos);
    long maxd = 0, mind = n;
    for (long x = 0; x < n; x++) {
        long k = deg[x]; if (k > maxd) maxd = k; if (k < mind) mind = k;
        qsort(adj + st[x], k, 8, cmpl);
        for (long i = st[x] + 1; i < st[x + 1]; i++) if (adj[i] == adj[i - 1]) { printf("RESULT INVALID repeated edge at %ld\n", x); return 1; }
    }
    /* sigma is an automorphism? (a bijection mapping edges to edges, and the edge count is finite, so this suffices) */
    if (r * B > n) { printf("RESULT INVALID r*B > n\n"); return 1; }
    long bad = 0;
    for (long x = 0; x < n && !bad; x++) {
        long sx = x < r * B ? (x + B) % (r * B) : x;
        if (deg[sx] != deg[x]) { bad = 1; break; }
        for (long i = st[x]; i < st[x + 1]; i++) {
            long y = adj[i], sy = y < r * B ? (y + B) % (r * B) : y;
            long lo = st[sx], hi = st[sx + 1] - 1, found = 0;
            while (lo <= hi) { long md = (lo + hi) / 2; if (adj[md] == sy) { found = 1; break; } if (adj[md] < sy) lo = md + 1; else hi = md - 1; }
            if (!found) { bad = 1; break; }
        }
    }
    if (bad) { printf("RESULT INVALID sigma is not an automorphism\n"); return 1; }
    int *col = malloc(n * sizeof(int)); for (long i = 0; i < n; i++) col[i] = -1;
    long *q = malloc(n * 8); long h = 0, t = 0; col[0] = 0; q[t++] = 0; int bip = 1;
    while (h < t) { long x = q[h++]; for (long i = st[x]; i < st[x + 1]; i++) { long y = adj[i]; if (col[y] < 0) { col[y] = 1 - col[x]; q[t++] = y; } else if (col[y] == col[x]) bip = 0; } }
    if (t != n) { printf("RESULT INVALID disconnected (%ld of %ld)\n", t, n); return 1; }
    free(q); free(col);
    int *adj32 = malloc(2 * m * sizeof(int)); for (long i = 0; i < 2 * m; i++) adj32[i] = (int)adj[i]; free(adj);
    long nsrc = B + (n - r * B); long *src = malloc(nsrc * 8);
    for (long i = 0; i < B; i++) src[i] = i;
    for (long i = r * B; i < n; i++) src[B + i - r * B] = i;
    long nbatch = (nsrc + 63) / 64; int diam = 0, unreached = 0; long done = 0;
#ifdef _OPENMP
    omp_set_num_threads(T);
#endif
    #pragma omp parallel
    {
        uint64_t *vis = malloc(n * 8), *fr = malloc(n * 8), *nx = malloc(n * 8);
        #pragma omp for schedule(dynamic, 4)
        for (long bt = 0; bt < nbatch; bt++) {
            memset(vis, 0, n * 8); memset(fr, 0, n * 8);
            long s0 = bt * 64; int ns = (nsrc - s0 < 64) ? (int)(nsrc - s0) : 64; uint64_t full = ns == 64 ? ~0ULL : ((1ULL << ns) - 1);
            for (int k = 0; k < ns; k++) { vis[src[s0 + k]] |= 1ULL << k; fr[src[s0 + k]] |= 1ULL << k; }
            int lev = 0;
            for (;;) { int any = 0;
                for (long x = 0; x < n; x++) { uint64_t acc = 0; for (long i = st[x]; i < st[x + 1]; i++) acc |= fr[adj32[i]]; acc &= ~vis[x]; nx[x] = acc; if (acc) any = 1; }
                if (!any) break; lev++; for (long x = 0; x < n; x++) vis[x] |= nx[x]; uint64_t *tmp = fr; fr = nx; nx = tmp; }
            int un = 0; for (long x = 0; x < n; x++) if (vis[x] != full) { un = 1; break; }
            #pragma omp critical
            { if (lev > diam) diam = lev; if (un) unreached = 1; done++;
              if (done % 500 == 0) { fprintf(stderr, "batch %ld/%ld diam so far %d\n", done, nbatch, diam); } }
        }
        free(vis); free(fr); free(nx);
    }
    if (unreached) { printf("RESULT INVALID unreached\n"); return 1; }
    printf("n=%ld edges=%ld degree min=%ld max=%ld bipartite=%s sigma(B=%ld,r=%d) automorphism=yes sources=%ld diameter=%d\n",
           n, m, mind, maxd, bip ? "yes" : "no", B, r, nsrc, diam);
    if (bip && maxd <= d && diam <= D) printf("RESULT VALID d=%d D=%d n=%ld\n", d, D, n); else printf("RESULT INVALID\n");
    return 0;
}
