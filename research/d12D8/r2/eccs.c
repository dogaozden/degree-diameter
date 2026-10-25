/* eccs.c: eccentricity of given source vertices in an edge-list graph ("n" then "a b" lines). usage: eccs EDGES s1 s2 ... */
#include <stdio.h>
#include <stdlib.h>
int main(int c, char **v) {
    FILE *f = fopen(v[1], "r"); long n, m = 0, cap = 1 << 22, a, b; if (fscanf(f, "%ld", &n) != 1) return 1;
    long *U = malloc(cap * 8), *W = malloc(cap * 8);
    while (fscanf(f, "%ld %ld", &a, &b) == 2) { if (m == cap) { cap *= 2; U = realloc(U, cap * 8); W = realloc(W, cap * 8); } U[m] = a; W[m] = b; m++; }
    long *st = calloc(n + 1, 8); for (long i = 0; i < m; i++) { st[U[i] + 1]++; st[W[i] + 1]++; }
    for (long i = 0; i < n; i++) st[i + 1] += st[i];
    long *adj = malloc(2 * m * 8), *pos = calloc(n, 8);
    for (long i = 0; i < m; i++) { adj[st[U[i]] + pos[U[i]]++] = W[i]; adj[st[W[i]] + pos[W[i]]++] = U[i]; }
    int *d = malloc(n * sizeof(int)); long *q = malloc(n * 8);
    for (int k = 2; k < c; k++) { long s = atol(v[k]); for (long i = 0; i < n; i++) d[i] = -1;
        long h = 0, t = 0; d[s] = 0; q[t++] = s; int e = 0;
        while (h < t) { long x = q[h++]; for (long i = st[x]; i < st[x + 1]; i++) { long y = adj[i]; if (d[y] < 0) { d[y] = d[x] + 1; if (d[y] > e) e = d[y]; q[t++] = y; } } }
        long cnt[16] = {0}; for (long i = 0; i < n; i++) if (d[i] >= 0 && d[i] < 16) cnt[d[i]]++;
        printf("source %ld: reached %ld of %ld, eccentricity %d; counts by distance:", s, t, n, e);
        for (int i = 0; i <= e; i++) printf(" %ld", cnt[i]); printf("\n"); }
    return 0; }
