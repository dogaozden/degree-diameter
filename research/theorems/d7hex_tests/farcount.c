/* Bit-parallel BFS (as in research/lifts/coordinator_check/apsp_mt.c) from a set of sources; counts the ordered pairs
   (s, t) with d(s, t) > D (unreachable counts as far) and prints the first few.  Sources: all vertices, or the list in
   SRCFILE (one vertex id per line).
   Usage: farcount EDGES D [SRCFILE]     (build: cc -O2 -o farcount farcount.c) */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
int main(int c, char **v) {
    FILE *f = fopen(v[1], "r"); int D = atoi(v[2]); long n, m = 0, cap = 1 << 16, a, b;
    if (fscanf(f, "%ld", &n) != 1) return 2;
    long *U = malloc(cap * 8), *W = malloc(cap * 8);
    while (fscanf(f, "%ld %ld", &a, &b) == 2) { if (m == cap) { cap *= 2; U = realloc(U, cap * 8); W = realloc(W, cap * 8); } U[m] = a; W[m] = b; m++; }
    long *deg = calloc(n + 1, 8), *st = calloc(n + 1, 8), *pos = calloc(n, 8);
    for (long i = 0; i < m; i++) { deg[U[i]]++; deg[W[i]]++; }
    for (long i = 0; i < n; i++) st[i + 1] = st[i] + deg[i];
    long *adj = malloc(2 * m * 8);
    for (long i = 0; i < m; i++) { adj[st[U[i]] + pos[U[i]]++] = W[i]; adj[st[W[i]] + pos[W[i]]++] = U[i]; }
    long ns_all = n, *src = NULL;
    if (c > 3) { FILE *g = fopen(v[3], "r"); long cap2 = 1024, k = 0, x; src = malloc(cap2 * 8);
        while (fscanf(g, "%ld", &x) == 1) { if (k == cap2) { cap2 *= 2; src = realloc(src, cap2 * 8); } src[k++] = x; } ns_all = k; }
    uint64_t *vis = malloc(n * 8), *fr = malloc(n * 8), *nx = malloc(n * 8);
    long far = 0, shown = 0;
    for (long s0 = 0; s0 < ns_all; s0 += 64) {
        int ns = (ns_all - s0 < 64) ? (int)(ns_all - s0) : 64;
        memset(vis, 0, n * 8); memset(fr, 0, n * 8);
        for (int k = 0; k < ns; k++) { long s = src ? src[s0 + k] : s0 + k; vis[s] |= 1ULL << k; fr[s] |= 1ULL << k; }
        for (int lev = 0; lev < D; lev++) {
            for (long x = 0; x < n; x++) { uint64_t acc = 0; for (long i = st[x]; i < st[x + 1]; i++) acc |= fr[adj[i]]; nx[x] = acc & ~vis[x]; }
            for (long x = 0; x < n; x++) vis[x] |= nx[x]; uint64_t *t = fr; fr = nx; nx = t;
        }
        uint64_t full = ns == 64 ? ~0ULL : ((1ULL << ns) - 1);
        for (long x = 0; x < n; x++) { uint64_t miss = full & ~vis[x]; while (miss) { int k = __builtin_ctzll(miss); miss &= miss - 1; far++;
            if (shown < 10) { printf("far: %ld %ld\n", src ? src[s0 + k] : s0 + k, x); shown++; } } }
    }
    printf("n=%ld sources=%ld D=%d far_ordered_pairs=%ld\n", n, ns_all, D, far);
    return 0;
}
