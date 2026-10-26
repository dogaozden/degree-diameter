/* ecc.c (table-audit): eccentricity of given source vertices in an edge-list graph ("n" then "u v" lines).
   Prints, per source, its eccentricity and how many vertices sit at each distance beyond LIMIT.
   Usage: ecc EDGES LIMIT s1 [s2 ...] */
#include <stdio.h>
#include <stdlib.h>
int main(int argc, char **argv) {
    FILE *f = fopen(argv[1], "r"); int lim = atoi(argv[2]); long n, m = 0, cap = 1 << 20, a, b;
    if (fscanf(f, "%ld", &n) != 1) return 2;
    long *U = malloc(cap * 8), *W = malloc(cap * 8);
    while (fscanf(f, "%ld %ld", &a, &b) == 2) { if (m == cap) { cap *= 2; U = realloc(U, cap * 8); W = realloc(W, cap * 8); } U[m] = a; W[m] = b; m++; }
    long *st = calloc(n + 1, 8), *adj = malloc(2 * m * 8), *pos = calloc(n, 8);
    for (long i = 0; i < m; i++) { st[U[i] + 1]++; st[W[i] + 1]++; }
    for (long i = 0; i < n; i++) st[i + 1] += st[i];
    for (long i = 0; i < m; i++) { adj[st[U[i]] + pos[U[i]]++] = W[i]; adj[st[W[i]] + pos[W[i]]++] = U[i]; }
    int *d = malloc(n * sizeof(int)); long *q = malloc(n * 8);
    for (int k = 3; k < argc; k++) {
        long s = atol(argv[k]); for (long i = 0; i < n; i++) d[i] = -1;
        long h = 0, t = 0; d[s] = 0; q[t++] = s;
        while (h < t) { long x = q[h++]; for (long i = st[x]; i < st[x + 1]; i++) if (d[adj[i]] < 0) { d[adj[i]] = d[x] + 1; q[t++] = adj[i]; } }
        int e = 0; long far[64] = {0}, un = n - t;
        for (long i = 0; i < n; i++) { if (d[i] > e) e = d[i]; if (d[i] > lim && d[i] < 64) far[d[i]]++; }
        printf("source %ld: ecc %d, unreached %ld", s, e, un);
        for (int j = lim + 1; j < 64; j++) if (far[j]) printf(", %ld at distance %d", far[j], j);
        printf("\n");
    }
    return 0;
}
