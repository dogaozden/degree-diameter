/* apsp_cyc.c: independent diameter check of an edge list that has a cyclic automorphism of "copies".
   Written for cell (14,7), 2026-10-24 (second session), from the definitions only; it shares no code with ucheck12.
   Input: edge list "n" then "u v" lines (as written by unit_edges.py). Vertices 0..NB-1 are lift vertices x*m + c
   (copy c in Z_m); vertices NB..n-1 are extra vertices (unit hubs, super-hubs), which the shift must fix.
   1. Checks: no loops, no repeated edges, max degree <= d, connected, bipartite.
   2. Checks that phi(x*m + c) = x*m + (c+1 mod m) (identity on extra vertices) maps every edge to an edge, so phi is
      an automorphism of order m.
   3. Bit-parallel BFS (64 sources per pass) from every vertex with c = 0 and from every extra vertex, to depth D.
      Every vertex is phi^k of one of these sources, so all pairs are within D iff all these BFS reach everything.
   Usage: apsp_cyc EDGES d D m [THREADS]
   Compile: gcc -O3 -march=native -fopenmp -o apsp_cyc apsp_cyc.c */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <omp.h>

static int cmpl(const void *a, const void *b) { long x = *(const long *)a, y = *(const long *)b; return x < y ? -1 : x > y; }

int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage: apsp_cyc EDGES d D m [THREADS]\n"); return 2; }
    int d = atoi(argv[2]), D = atoi(argv[3]), m = atoi(argv[4]), nth = argc > 5 ? atoi(argv[5]) : 1;
    FILE *f = fopen(argv[1], "r"); long n;
    if (!f || fscanf(f, "%ld", &n) != 1) { printf("RESULT INVALID cannot read\n"); return 2; }
    long cap = 1 << 22, E = 0; int32_t *U = malloc(cap * 4), *W = malloc(cap * 4); long a, b;
    while (fscanf(f, "%ld %ld", &a, &b) == 2) {
        if (E == cap) { cap *= 2; U = realloc(U, cap * 4); W = realloc(W, cap * 4); }
        U[E] = (int32_t)a; W[E] = (int32_t)b; E++;
        if (a < 0 || b < 0 || a >= n || b >= n || a == b) { printf("RESULT INVALID bad edge %ld: %ld %ld\n", E, a, b); return 1; }
    }
    fclose(f);
    long *deg = calloc(n + 1, sizeof(long));
    for (long i = 0; i < E; i++) { deg[U[i]]++; deg[W[i]]++; }
    long *st = malloc((n + 1) * sizeof(long)); st[0] = 0; for (long i = 0; i < n; i++) st[i + 1] = st[i] + deg[i];
    long *adj = malloc(2 * E * sizeof(long)); long *pos = calloc(n, sizeof(long));
    for (long i = 0; i < E; i++) { adj[st[U[i]] + pos[U[i]]++] = W[i]; adj[st[W[i]] + pos[W[i]]++] = U[i]; }
    free(U); free(W); free(pos);
    long maxd = 0, mind = n;
    for (long x = 0; x < n; x++) {
        qsort(adj + st[x], deg[x], sizeof(long), cmpl);
        if (deg[x] > maxd) maxd = deg[x]; if (deg[x] < mind) mind = deg[x];
        for (long i = st[x] + 1; i < st[x + 1]; i++) if (adj[i] == adj[i - 1]) { printf("RESULT INVALID repeated edge at %ld\n", x); return 1; }
    }
    /* NB (environment): number of lift vertices x*m + c; vertices NB..n-1 are the extra vertices. */
    long NB = getenv("NB") ? atol(getenv("NB")) : -1;
    if (NB < 0) { printf("RESULT INVALID set NB (number of lift vertices, a multiple of m)\n"); return 2; }
    if (NB % m || NB > n) { printf("RESULT INVALID NB not a multiple of m\n"); return 2; }
    /* bipartite + connected */
    int *col = malloc(n * sizeof(int)); for (long i = 0; i < n; i++) col[i] = -1;
    long *qu = malloc(n * sizeof(long)); long h = 0, t = 0; int bip = 1; col[0] = 0; qu[t++] = 0;
    while (h < t) { long x = qu[h++]; for (long i = st[x]; i < st[x + 1]; i++) { long y = adj[i]; if (col[y] < 0) { col[y] = 1 - col[x]; qu[t++] = y; } else if (col[y] == col[x]) bip = 0; } }
    if (t != n) { printf("RESULT INVALID disconnected (%ld of %ld reached)\n", t, n); return 1; }
    /* phi is an automorphism */
    long bad = 0;
    for (long x = 0; x < n && bad == 0; x++) {
        long px = x < NB ? (x / m) * m + (x % m + 1) % m : x;
        if (deg[px] != deg[x]) { bad++; break; }
        for (long i = st[x]; i < st[x + 1]; i++) {
            long y = adj[i], py = y < NB ? (y / m) * m + (y % m + 1) % m : y;
            if (!bsearch(&py, adj + st[px], deg[px], sizeof(long), cmpl)) { bad++; break; }
        }
    }
    if (bad) { printf("RESULT INVALID the copy shift is not an automorphism\n"); return 1; }
    fprintf(stderr, "n=%ld edges=%ld degree %ld..%ld bipartite=%s; copy shift is an automorphism (m=%d, NB=%ld)\n",
            n, E, mind, maxd, bip ? "yes" : "no", m, NB);
    /* sources */
    long ns = 0; long *src = malloc(sizeof(long) * (NB / m + (n - NB) + 1));
    for (long x = 0; x < NB; x += m) src[ns++] = x;
    for (long x = NB; x < n; x++) src[ns++] = x;
    long nblk = (ns + 63) / 64, done = 0; long worst = 0, nbad = 0; double t0 = omp_get_wtime();
    #pragma omp parallel num_threads(nth) reduction(max:worst) reduction(+:nbad)
    {
        uint64_t *vis = malloc(n * 8), *fr = malloc(n * 8), *nx = malloc(n * 8);
        #pragma omp for schedule(dynamic, 4)
        for (long bi = 0; bi < nblk; bi++) {
            long s0 = bi * 64; int k = (int)((ns - s0) < 64 ? (ns - s0) : 64);
            uint64_t full = k == 64 ? ~0ULL : ((1ULL << k) - 1);
            memset(vis, 0, n * 8); memset(fr, 0, n * 8);
            for (int j = 0; j < k; j++) { vis[src[s0 + j]] |= 1ULL << j; fr[src[s0 + j]] |= 1ULL << j; }
            int lev = 0;
            for (lev = 1; lev <= D; lev++) {
                int any = 0;
                for (long x = 0; x < n; x++) { uint64_t acc = 0; for (long i = st[x]; i < st[x + 1]; i++) acc |= fr[adj[i]];
                    acc &= ~vis[x]; nx[x] = acc; if (acc) any = 1; }
                for (long x = 0; x < n; x++) vis[x] |= nx[x];
                uint64_t *tmp = fr; fr = nx; nx = tmp;
                if (!any) break;
            }
            long miss = 0; for (long x = 0; x < n; x++) miss += __builtin_popcountll(full & ~vis[x]);
            if (miss) { nbad += miss; if (worst < D + 1) worst = D + 1; }
            long dd;
            #pragma omp atomic capture
            dd = ++done;
            if (dd % 500 == 0) fprintf(stderr, "  %ld of %ld blocks, %.0fs\n", dd, nblk, omp_get_wtime() - t0);
        }
        free(vis); free(fr); free(nx);
    }
    printf("n=%ld edges=%ld degree min=%ld max=%ld bipartite=%s copy-shift automorphism m=%d (NB=%ld); sources %ld; "
           "pairs beyond %d: %ld; %.0fs\n", n, E, mind, maxd, bip ? "yes" : "no", m, NB, ns, D, nbad, omp_get_wtime() - t0);
    if (bip && maxd <= d && nbad == 0) printf("RESULT VALID d=%d D=%d n=%ld\n", d, D, n); else printf("RESULT INVALID\n");
    return 0;
}
