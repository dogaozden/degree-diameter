/* symcheck.c (job cell-12-7): independent check of an edge list whose vertices 0..R*M-1 are (x, c) = x*M + c
 * (c in Z_M) and whose remaining vertices R*M.. are extra vertices that the shift should fix.
 * 1. simple, max degree <= d, bipartite, connected;
 * 2. the shift (x, c) -> (x, c+1 mod M), extra vertices fixed, maps every edge to an edge (an automorphism);
 * 3. bit-parallel BFS (64 sources per pass) from every vertex with c = 0 and every extra vertex. By 2 every vertex is
 *    in the shift orbit of one of these, so the maximum eccentricity found is the diameter.
 * usage: symcheck EDGES d D M [threads]          (does not use any construction data: only the edge list) */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#ifdef _OPENMP
#include <omp.h>
#endif
static int cmpl(const void *a, const void *b) { long x = *(const long *)a, y = *(const long *)b; return x < y ? -1 : x > y; }
int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage: symcheck EDGES d D M [threads]\n"); return 1; }
    FILE *f = fopen(argv[1], "r"); int dmax = atoi(argv[2]), D = atoi(argv[3]), M = atoi(argv[4]);
    long n; if (fscanf(f, "%ld", &n) != 1) return 2;
    long cap = 1 << 22, m = 0; long *U = malloc(cap * 8), *W = malloc(cap * 8); long a, b;
    while (fscanf(f, "%ld %ld", &a, &b) == 2) { if (m == cap) { cap *= 2; U = realloc(U, cap * 8); W = realloc(W, cap * 8); } U[m] = a; W[m] = b; m++; }
    fclose(f);
    long *deg = calloc(n, 8);
    for (long i = 0; i < m; i++) { if (U[i] == W[i] || U[i] < 0 || W[i] < 0 || U[i] >= n || W[i] >= n) { printf("RESULT INVALID bad edge %ld\n", i); return 1; } deg[U[i]]++; deg[W[i]]++; }
    long *st = calloc(n + 1, 8); for (long i = 0; i < n; i++) st[i + 1] = st[i] + deg[i];
    int *adj = malloc(2 * m * sizeof(int)); long *pos = calloc(n, 8);
    for (long i = 0; i < m; i++) { adj[st[U[i]] + pos[U[i]]++] = (int)W[i]; adj[st[W[i]] + pos[W[i]]++] = (int)U[i]; }
    long md = 0; for (long x = 0; x < n; x++) if (deg[x] > md) md = deg[x];
    /* simple: sort each adjacency list */
    for (long x = 0; x < n; x++) {
        long k = deg[x]; int *A = adj + st[x];
        for (long i = 1; i < k; i++) { int v = A[i]; long j = i - 1; while (j >= 0 && A[j] > v) { A[j + 1] = A[j]; j--; } A[j + 1] = v; }
        for (long i = 1; i < k; i++) if (A[i] == A[i - 1]) { printf("RESULT INVALID repeated edge at %ld\n", x); return 1; }
    }
    /* bipartite + connected */
    int *col = malloc(n * sizeof(int)); for (long i = 0; i < n; i++) col[i] = -1;
    int *q = malloc(n * sizeof(int)); long h = 0, t = 0; col[0] = 0; q[t++] = 0; int bip = 1;
    while (h < t) { int x = q[h++]; for (long i = st[x]; i < st[x + 1]; i++) { int y = adj[i]; if (col[y] < 0) { col[y] = 1 - col[x]; q[t++] = y; } else if (col[y] == col[x]) bip = 0; } }
    printf("n=%ld edges=%ld max degree=%ld bipartite=%s connected=%s\n", n, m, md, bip ? "yes" : "no", t == n ? "yes" : "no");
    if (!bip || t != n || md > dmax) { printf("RESULT INVALID\n"); return 1; }
    /* the shift */
    long R = 0; { long maxold = -1; (void)maxold; }
    /* old vertices are 0 .. R*M-1 where R*M is the largest multiple of M with all of them in the cover part:
       we take R = n / M (integer part) and the extras are n - R*M vertices */
    R = n / M; long extras = n - R * M;
    long *key = malloc(m * 8);
    for (long i = 0; i < m; i++) { long x = U[i], y = W[i]; if (x > y) { long z = x; x = y; y = z; } key[i] = x * n + y; }
    qsort(key, m, 8, cmpl);
    long notmapped = 0;
    for (long i = 0; i < m; i++) {
        long x = U[i], y = W[i];
        long sx = x < R * M ? (x / M) * M + (x % M + 1) % M : x;
        long sy = y < R * M ? (y / M) * M + (y % M + 1) % M : y;
        if (sx > sy) { long z = sx; sx = sy; sy = z; }
        long k = sx * n + sy; long lo = 0, hi = m - 1, found = 0;
        while (lo <= hi) { long mid = (lo + hi) / 2; if (key[mid] == k) { found = 1; break; } if (key[mid] < k) lo = mid + 1; else hi = mid - 1; }
        if (!found) notmapped++;
    }
    printf("shift by one copy (M=%d, %ld cover vertices, %ld extra vertices fixed): %ld edges not mapped to edges\n", M, R * M, extras, notmapped);
    if (notmapped) { printf("RESULT INVALID (shift is not an automorphism; use apsp)\n"); return 1; }
    free(key);
    /* sources: c = 0 vertices and extras */
    long ns = 0; long *src = malloc((R + extras) * 8);
    for (long x = 0; x < R; x++) src[ns++] = x * M;
    for (long e = 0; e < extras; e++) src[ns++] = R * M + e;
    int nth = argc > 5 ? atoi(argv[5]) : 1;
#ifdef _OPENMP
    omp_set_num_threads(nth);
#endif
    int diam = 0; long badpairs = 0;
    long nb = (ns + 63) / 64;
    #pragma omp parallel reduction(max:diam) reduction(+:badpairs)
    {
        uint64_t *vis = malloc(n * 8), *fr = malloc(n * 8), *nx = malloc(n * 8);
        #pragma omp for schedule(dynamic, 4)
        for (long bi = 0; bi < nb; bi++) {
            long s0 = bi * 64; int k = (int)((ns - s0 < 64) ? ns - s0 : 64);
            uint64_t full = k == 64 ? ~0ULL : ((1ULL << k) - 1);
            memset(vis, 0, n * 8); memset(fr, 0, n * 8);
            for (int j = 0; j < k; j++) { vis[src[s0 + j]] |= 1ULL << j; fr[src[s0 + j]] |= 1ULL << j; }
            int lev = 0;
            for (;;) {
                int any = 0;
                for (long v = 0; v < n; v++) {
                    uint64_t acc = 0;
                    for (long i = st[v]; i < st[v + 1]; i++) acc |= fr[adj[i]];
                    acc &= ~vis[v]; nx[v] = acc; if (acc) any = 1;
                }
                if (!any) break;
                lev++;
                for (long v = 0; v < n; v++) { vis[v] |= nx[v]; }
                uint64_t *tmp = fr; fr = nx; nx = tmp;
            }
            long unreached = 0; for (long v = 0; v < n; v++) if ((vis[v] & full) != full) unreached++;
            if (unreached) { badpairs += unreached; lev = 99; }
            if (lev > diam) diam = lev;
            if (lev > D) {
                /* count pairs beyond D by a plain BFS of each source in this pass */
                int *dd = malloc(n * sizeof(int)); int *qq = malloc(n * sizeof(int));
                for (int j = 0; j < k; j++) {
                    for (long v = 0; v < n; v++) dd[v] = -1; long hh = 0, tt = 0; dd[src[s0 + j]] = 0; qq[tt++] = (int)src[s0 + j];
                    while (hh < tt) { int x = qq[hh++]; for (long i = st[x]; i < st[x + 1]; i++) { int y = adj[i]; if (dd[y] < 0) { dd[y] = dd[x] + 1; qq[tt++] = y; } } }
                    for (long v = 0; v < n; v++) if (dd[v] < 0 || dd[v] > D) badpairs++;
                }
                free(dd); free(qq);
            }
        }
        free(vis); free(fr); free(nx);
    }
    printf("sources %ld (one per shift orbit), max eccentricity %d, pairs beyond D=%d: %ld\n", ns, diam, D, badpairs);
    if (diam <= D && badpairs == 0) printf("RESULT VALID d=%d D=%d n=%ld (diameter %d)\n", dmax, D, n, diam);
    else printf("RESULT INVALID\n");
    return 0;
}
