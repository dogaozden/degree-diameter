/* ecc.c: all-sources BFS on an edge list ("n" then "u v" lines). Prints, per source with ecc > D,
   the number of targets beyond D. Usage: ecc EDGES D [maxprint]. Vertex classes by id: see the caller. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int main(int argc, char **argv) {
    FILE *f = fopen(argv[1], "r"); int D = atoi(argv[2]); int maxp = argc > 3 ? atoi(argv[3]) : 40;
    long n; if (fscanf(f, "%ld", &n) != 1) return 2;
    long cap = 1 << 20, m = 0; long *U = malloc(cap * 8), *W = malloc(cap * 8), a, b;
    while (fscanf(f, "%ld %ld", &a, &b) == 2) { if (m == cap) { cap *= 2; U = realloc(U, cap * 8); W = realloc(W, cap * 8); }
        U[m] = a; W[m] = b; m++; }
    long *deg = calloc(n + 1, 8); for (long i = 0; i < m; i++) { deg[U[i]]++; deg[W[i]]++; }
    long *st = calloc(n + 1, 8); for (long i = 0; i < n; i++) st[i + 1] = st[i] + deg[i];
    long *adj = malloc(2 * m * 8 + 8), *pos = calloc(n + 1, 8);
    for (long i = 0; i < m; i++) { adj[st[U[i]] + pos[U[i]]++] = W[i]; adj[st[W[i]] + pos[W[i]]++] = U[i]; }
    int *dist = malloc(n * sizeof(int)), *que = malloc(n * sizeof(int));
    long bad_src = 0, bad_pairs = 0, printed = 0;
    for (long s = 0; s < n; s++) {
        for (long v = 0; v < n; v++) dist[v] = -1;
        long h = 0, t = 0; dist[s] = 0; que[t++] = s;
        while (h < t) { long v = que[h++]; for (long i = st[v]; i < st[v + 1]; i++) { long w = adj[i]; if (dist[w] < 0) { dist[w] = dist[v] + 1; que[t++] = w; } } }
        long beyond = n - t; for (long k = 0; k < t; k++) if (dist[que[k]] > D) beyond++;
        if (beyond) { bad_src++; bad_pairs += beyond; if (printed < maxp) { printf("src %ld deg %ld beyond %ld\n", s, deg[s], beyond); printed++; } }
    }
    printf("SUMMARY bad_sources %ld bad_pairs %ld (D=%d)\n", bad_src, bad_pairs, D);
    return 0;
}
