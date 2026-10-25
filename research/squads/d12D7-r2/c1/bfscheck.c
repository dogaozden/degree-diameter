/* bfscheck.c: independent single-source BFS on an EDGES file (first line n, then "u v" lines).
   Usage: bfscheck EDGES D src1 [src2 ...]  -> per source: #vertices at distance > D, eccentricity, #unreached. */
#include <stdio.h>
#include <stdlib.h>
int main(int argc, char **argv) {
    if (argc < 4) { fprintf(stderr, "usage: bfscheck EDGES D src...\n"); return 2; }
    FILE *f = fopen(argv[1], "r"); int D = atoi(argv[2]);
    long n; if (!f || fscanf(f, "%ld", &n) != 1) return 1;
    long cap = 1 << 22, m = 0; long *U = malloc(cap * sizeof(long)), *W = malloc(cap * sizeof(long)), a, b;
    while (fscanf(f, "%ld %ld", &a, &b) == 2) { if (m == cap) { cap *= 2; U = realloc(U, cap * sizeof(long)); W = realloc(W, cap * sizeof(long)); } U[m] = a; W[m] = b; m++; }
    fclose(f);
    long *deg = calloc(n + 1, sizeof(long)), *st = calloc(n + 1, sizeof(long)), *adj = malloc(2 * m * sizeof(long)), *pos = calloc(n, sizeof(long));
    for (long i = 0; i < m; i++) { if (U[i] < 0 || W[i] < 0 || U[i] >= n || W[i] >= n) { printf("BAD edge\n"); return 1; } deg[U[i]]++; deg[W[i]]++; }
    for (long i = 0; i < n; i++) st[i + 1] = st[i] + deg[i];
    for (long i = 0; i < m; i++) { adj[st[U[i]] + pos[U[i]]++] = W[i]; adj[st[W[i]] + pos[W[i]]++] = U[i]; }
    long mind = 1L << 40, maxd = 0; for (long x = 0; x < n; x++) { if (deg[x] < mind) mind = deg[x]; if (deg[x] > maxd) maxd = deg[x]; }
    printf("n=%ld m=%ld degree min=%ld max=%ld\n", n, m, mind, maxd);
    int *dist = malloc(n * sizeof(int)), *q = malloc(n * sizeof(int));
    for (int k = 3; k < argc; k++) {
        long s = atol(argv[k]);
        for (long x = 0; x < n; x++) dist[x] = -1;
        long h = 0, t = 0; dist[s] = 0; q[t++] = s; int ecc = 0;
        while (h < t) { long x = q[h++]; for (long i = st[x]; i < st[x + 1]; i++) { long y = adj[i]; if (dist[y] < 0) { dist[y] = dist[x] + 1; if (dist[y] > ecc) ecc = dist[y]; q[t++] = y; } } }
        long far = 0; for (long x = 0; x < n; x++) if (dist[x] > D || dist[x] < 0) far++;
        printf("src %ld: reached %ld/%ld, ecc %d, #at distance > %d: %ld\n", s, t, n, ecc, D, far);
    }
    return 0;
}
