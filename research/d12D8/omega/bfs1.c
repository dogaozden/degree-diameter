/* Plain BFS from one source on an edge-list graph ("n" then "u v" lines): prints the number of vertices at each distance
   and, for each extra argument t, the distance d(s,t).   Usage: bfs1 EDGES s [t ...]   (build: cc -O2 -o bfs1 bfs1.c) */
#include <stdio.h>
#include <stdlib.h>
int main(int c, char **v) {
    FILE *f = fopen(v[1], "r"); long n, m = 0, cap = 1 << 20, a, b; if (fscanf(f, "%ld", &n) != 1) return 2;
    long *U = malloc(cap * 8), *W = malloc(cap * 8);
    while (fscanf(f, "%ld %ld", &a, &b) == 2) { if (m == cap) { cap *= 2; U = realloc(U, cap * 8); W = realloc(W, cap * 8); } U[m] = a; W[m] = b; m++; }
    long *st = calloc(n + 1, 8), *pos = calloc(n, 8), *adj = malloc(2 * m * 8);
    for (long i = 0; i < m; i++) { st[U[i] + 1]++; st[W[i] + 1]++; } for (long i = 0; i < n; i++) st[i + 1] += st[i];
    for (long i = 0; i < m; i++) { adj[st[U[i]] + pos[U[i]]++] = W[i]; adj[st[W[i]] + pos[W[i]]++] = U[i]; }
    long s = atol(v[2]); int *d = malloc(n * sizeof(int)); for (long i = 0; i < n; i++) d[i] = -1;
    long *qq = malloc(n * 8), h = 0, t = 0; d[s] = 0; qq[t++] = s;
    while (h < t) { long x = qq[h++]; for (long i = st[x]; i < st[x + 1]; i++) if (d[adj[i]] < 0) { d[adj[i]] = d[x] + 1; qq[t++] = adj[i]; } }
    long cnt[64] = {0}; int ecc = 0; for (long i = 0; i < n; i++) { if (d[i] < 0) { printf("unreached %ld\n", i); return 1; } cnt[d[i]]++; if (d[i] > ecc) ecc = d[i]; }
    printf("source %ld: eccentricity %d; counts", s, ecc); for (int k = 0; k <= ecc; k++) printf(" %ld", cnt[k]); printf("\n");
    for (int k = 3; k < c; k++) printf("d(%ld, %s) = %d\n", s, v[k], d[atol(v[k])]);
    return 0;
}
