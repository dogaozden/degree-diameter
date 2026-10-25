/* All-pairs distances of a small graph given as an apsp edge list (first line n, then "a b" per edge).
   Writes an n x n uint8 matrix (255 = unreachable) to OUT.  Used for the incidence graph of H(q), q <= 5.
   Usage: dist EDGES OUT     (build: cc -O2 -o dist dist.c) */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
int main(int c, char **v) {
    if (c < 3) return 2;
    FILE *f = fopen(v[1], "r"); long n, m = 0, cap = 1 << 16, a, b;
    if (fscanf(f, "%ld", &n) != 1) return 2;
    long *U = malloc(cap * 8), *W = malloc(cap * 8);
    while (fscanf(f, "%ld %ld", &a, &b) == 2) { if (m == cap) { cap *= 2; U = realloc(U, cap * 8); W = realloc(W, cap * 8); } U[m] = a; W[m] = b; m++; }
    long *deg = calloc(n + 1, 8), *st = calloc(n + 1, 8), *pos = calloc(n, 8);
    for (long i = 0; i < m; i++) { deg[U[i]]++; deg[W[i]]++; }
    for (long i = 0; i < n; i++) st[i + 1] = st[i] + deg[i];
    long *adj = malloc(2 * m * 8);
    for (long i = 0; i < m; i++) { adj[st[U[i]] + pos[U[i]]++] = W[i]; adj[st[W[i]] + pos[W[i]]++] = U[i]; }
    uint8_t *row = malloc(n); long *q = malloc(n * 8);
    FILE *o = fopen(v[2], "wb");
    for (long s = 0; s < n; s++) {
        memset(row, 255, n); row[s] = 0; long h = 0, t = 0; q[t++] = s;
        while (h < t) { long x = q[h++]; for (long i = st[x]; i < st[x + 1]; i++) { long y = adj[i]; if (row[y] == 255) { row[y] = row[x] + 1; q[t++] = y; } } }
        fwrite(row, 1, n, o);
    }
    fclose(o); return 0;
}
