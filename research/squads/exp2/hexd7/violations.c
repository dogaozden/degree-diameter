/* Count ordered pairs at distance > D in an edge list, optionally after deleting some edges.
   Bit-parallel BFS, 64 sources at a time (as apsp.c). Usage: violations EDGES D [a1 b1 a2 b2 ...]
   (each pair a b names an edge to delete). Prints the number of ordered pairs with distance > D or infinite,
   and the number of sources involved. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
int main(int c, char **v) {
    FILE *f = fopen(v[1], "r"); int D = atoi(v[2]); long n, m = 0, cap = 1 << 20;
    if (!f || fscanf(f, "%ld", &n) != 1) return 2;
    long *U = malloc(cap * 8), *W = malloc(cap * 8); long a, b;
    while (fscanf(f, "%ld %ld", &a, &b) == 2) {
        if (m == cap) { cap *= 2; U = realloc(U, cap * 8); W = realloc(W, cap * 8); }
        int del = 0;
        for (int k = 3; k + 1 < c; k += 2) { long x = atol(v[k]), y = atol(v[k + 1]); if ((a == x && b == y) || (a == y && b == x)) del = 1; }
        if (del) continue;
        U[m] = a; W[m] = b; m++;
    }
    long *deg = calloc(n + 1, 8);
    for (long i = 0; i < m; i++) { deg[U[i]]++; deg[W[i]]++; }
    long *st = calloc(n + 1, 8); for (long i = 0; i < n; i++) st[i + 1] = st[i] + deg[i];
    long *adj = malloc((2 * m + 1) * 8), *pos = calloc(n, 8);
    for (long i = 0; i < m; i++) { adj[st[U[i]] + pos[U[i]]++] = W[i]; adj[st[W[i]] + pos[W[i]]++] = U[i]; }
    uint64_t *vis = malloc(n * 8), *fr = malloc(n * 8), *nx = malloc(n * 8);
    long bad = 0, badsrc = 0;
    for (long s0 = 0; s0 < n; s0 += 64) {
        memset(vis, 0, n * 8); memset(fr, 0, n * 8);
        int ns = (n - s0 < 64) ? (int)(n - s0) : 64;
        for (int k = 0; k < ns; k++) { vis[s0 + k] |= 1ULL << k; fr[s0 + k] |= 1ULL << k; }
        for (int lev = 0; lev < D; lev++) {
            for (long x = 0; x < n; x++) { uint64_t acc = 0; for (long i = st[x]; i < st[x + 1]; i++) acc |= fr[adj[i]]; acc &= ~vis[x]; nx[x] = acc; }
            for (long x = 0; x < n; x++) vis[x] |= nx[x];
            uint64_t *t = fr; fr = nx; nx = t;
        }
        uint64_t full = ns == 64 ? ~0ULL : ((1ULL << ns) - 1), srcbad = 0;
        for (long x = 0; x < n; x++) { uint64_t miss = ~vis[x] & full; if (miss) { bad += __builtin_popcountll(miss); srcbad |= miss; } }
        badsrc += __builtin_popcountll(srcbad);
    }
    printf("n=%ld edges=%ld deleted=%d pairs_beyond_D=%ld sources_with_misses=%ld\n", n, m, (c - 3) / 2, bad, badsrc);
    return 0;
}
