/* cov.c (job d7-family): BFS from each source to depth D; prints the number of vertices reached in the id range [lo, hi).
   usage: cov EDGES D lo hi SOURCES.txt [BITS_OUT]   (BITS_OUT: for each source a bitmap over [lo,hi)) */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
int main(int c, char **v) {
    FILE *f = fopen(v[1], "r"); long n, m = 0, cap = 1 << 22; int D = atoi(v[2]); long lo = atol(v[3]), hi = atol(v[4]);
    fscanf(f, "%ld", &n); int *U = malloc(cap * 4), *W = malloc(cap * 4); long a, b;
    while (fscanf(f, "%ld %ld", &a, &b) == 2) { if (m == cap) { cap *= 2; U = realloc(U, cap * 4); W = realloc(W, cap * 4); } U[m] = a; W[m] = b; m++; }
    long *st = calloc(n + 1, 8); for (long i = 0; i < m; i++) { st[U[i] + 1]++; st[W[i] + 1]++; }
    for (long i = 0; i < n; i++) st[i + 1] += st[i];
    int *adj = malloc(2 * m * 4); long *pos = calloc(n, 8);
    for (long i = 0; i < m; i++) { adj[st[U[i]] + pos[U[i]]++] = W[i]; adj[st[W[i]] + pos[W[i]]++] = U[i]; }
    int *dist = malloc(n * 4); int *qu = malloc(n * 4);
    FILE *g = fopen(v[5], "r"); FILE *bo = c > 6 ? fopen(v[6], "wb") : NULL; long s;
    long nb = hi - lo; uint8_t *bits = calloc((nb + 7) / 8, 1);
    while (fscanf(g, "%ld", &s) == 1) {
        for (long i = 0; i < n; i++) dist[i] = -1;
        long h = 0, t = 0; dist[s] = 0; qu[t++] = s; long cnt = 0;
        while (h < t) { long x = qu[h++]; if (x >= lo && x < hi) cnt++; if (dist[x] == D) continue;
            for (long i = st[x]; i < st[x + 1]; i++) { long y = adj[i]; if (dist[y] < 0) { dist[y] = dist[x] + 1; qu[t++] = y; } } }
        printf("%ld %ld\n", s, cnt); fflush(stdout);
        if (bo) { memset(bits, 0, (nb + 7) / 8); for (long i = 0; i < t; i++) { long x = qu[i]; if (x >= lo && x < hi) bits[(x - lo) >> 3] |= 1 << ((x - lo) & 7); } fwrite(bits, 1, (nb + 7) / 8, bo); }
    }
    return 0;
}
