/* gcheck.c: count vertex pairs at distance > D in an explicit graph, from a chosen set of sources
   (own-d8-compound job, 2026-10-26). Bit-parallel BFS, 64 sources per batch, OpenMP over batches.

   Input: first number n, then edges "a b" (0-based), as for apsp.c.
   Usage: gcheck EDGES D [all | r:K:seed | range:a:b]
   Output: "GCOST bad_pairs sources S maxdeg d ecc_max e" where bad_pairs counts (source, target) pairs with distance > D
           (unreachable counts too) and ecc_max is the largest eccentricity seen (99 if disconnected).
   Use a source set that meets every orbit of a known automorphism group (e.g. one level of a Z_5-symmetric graph)
   to get an exact answer; with 'all' it is an exact all-pairs check. Exit 0 iff no bad pair. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: gcheck EDGES D [srcspec]\n"); return 2; }
    FILE *f = fopen(argv[1], "r"); if (!f) { perror("open"); return 2; }
    int D = atoi(argv[2]); const char *spec = argc > 3 ? argv[3] : "all";
    long n, m = 0, cap = 1 << 20;
    if (fscanf(f, "%ld", &n) != 1) return 2;
    long *U = malloc(cap * 8), *W = malloc(cap * 8); long a, b;
    while (fscanf(f, "%ld %ld", &a, &b) == 2) {
        if (a < 0 || b < 0 || a >= n || b >= n || a == b) { fprintf(stderr, "bad edge %ld %ld\n", a, b); return 2; }
        if (m == cap) { cap *= 2; U = realloc(U, cap * 8); W = realloc(W, cap * 8); }
        U[m] = a; W[m] = b; m++;
    }
    fclose(f);
    long *deg = calloc(n + 1, 8);
    for (long i = 0; i < m; i++) { deg[U[i]]++; deg[W[i]]++; }
    long *st = calloc(n + 1, 8); for (long i = 0; i < n; i++) st[i + 1] = st[i] + deg[i];
    long *adj = malloc(2 * m * 8 + 8), *pos = calloc(n, 8);
    for (long i = 0; i < m; i++) { adj[st[U[i]] + pos[U[i]]++] = W[i]; adj[st[W[i]] + pos[W[i]]++] = U[i]; }
    long maxd = 0; long multi = 0;
    for (long x = 0; x < n; x++) { if (deg[x] > maxd) maxd = deg[x];
        for (long i = st[x]; i < st[x + 1]; i++) for (long j = i + 1; j < st[x + 1]; j++) if (adj[i] == adj[j]) multi++; }
    if (multi) fprintf(stderr, "warning: %ld repeated edges\n", multi);
    long ns = 0; long *src = malloc(sizeof(long) * (n + 64));
    if (!strcmp(spec, "all")) { for (long i = 0; i < n; i++) src[ns++] = i; }
    else if (!strncmp(spec, "range:", 6)) { long s0, s1; sscanf(spec + 6, "%ld:%ld", &s0, &s1); for (long i = s0; i < s1 && i < n; i++) src[ns++] = i; }
    else if (spec[0] == 'r') { long K; unsigned long long seed; sscanf(spec, "r:%ld:%llu", &K, &seed);
        uint64_t s = 0x9E3779B97F4A7C15ULL ^ (seed * 0xD1B54A32D192ED03ULL + 1);
        for (long i = 0; i < K; i++) { s ^= s << 13; s ^= s >> 7; s ^= s << 17; src[ns++] = (long)(s % (uint64_t)n); } }
    long nb = (ns + 63) / 64;
    long long badtot = 0; int eccmax = 0;
    #pragma omp parallel
    {
        uint64_t *vis = malloc(n * 8), *fr = malloc(n * 8), *nx = malloc(n * 8);
        #pragma omp for schedule(dynamic, 1) reduction(+:badtot)
        for (long bi = 0; bi < nb; bi++) {
            long k0 = bi * 64; int cnt = (ns - k0 < 64) ? (int)(ns - k0) : 64;
            uint64_t full = cnt == 64 ? ~0ULL : ((1ULL << cnt) - 1);
            memset(vis, 0, n * 8); memset(fr, 0, n * 8);
            for (int k = 0; k < cnt; k++) { vis[src[k0 + k]] |= 1ULL << k; fr[src[k0 + k]] |= 1ULL << k; }
            int lev = 0, done = 0;
            while (!done) {
                int any = 0;
                for (long x = 0; x < n; x++) { uint64_t acc = 0; for (long i = st[x]; i < st[x + 1]; i++) acc |= fr[adj[i]];
                    acc &= ~vis[x]; nx[x] = acc; if (acc) any = 1; }
                if (!any) break;
                lev++;
                for (long x = 0; x < n; x++) vis[x] |= nx[x];
                uint64_t *t = fr; fr = nx; nx = t;
                if (lev == D) {   /* count what is still missing after D levels */
                    long long bad = 0; for (long x = 0; x < n; x++) bad += __builtin_popcountll(full & ~vis[x]);
                    badtot += bad;
                    if (!bad) { done = 1; }
                }
            }
            int e = lev; for (long x = 0; x < n; x++) if ((vis[x] & full) != full) { e = 99; break; }
            #pragma omp critical
            { if (e > eccmax) eccmax = e; }
            if (lev < D) { /* finished before level D: nothing missing unless disconnected */
                long long bad = 0; for (long x = 0; x < n; x++) bad += __builtin_popcountll(full & ~vis[x]); badtot += bad; }
        }
        free(vis); free(fr); free(nx);
    }
    printf("GCOST %lld sources %ld maxdeg %ld ecc_max %d n %ld edges %ld\n", badtot, ns, maxd, eccmax, n, m);
    return badtot ? 1 : 0;
}
