/* distance histogram from given sources: hist EDGES src... */
#include <stdio.h>
#include <stdlib.h>
int main(int c, char **v) {
    FILE *f = fopen(v[1], "r"); long n, m = 0, a, b;
    fscanf(f, "%ld", &n);
    long *U = malloc(sizeof(long) * 300000), *W = malloc(sizeof(long) * 300000);
    while (fscanf(f, "%ld %ld", &a, &b) == 2) { U[m] = a; W[m] = b; m++; }
    long *deg = calloc(n + 1, sizeof(long));
    for (long i = 0; i < m; i++) { deg[U[i]]++; deg[W[i]]++; }
    long *st = calloc(n + 1, sizeof(long)); for (long i = 0; i < n; i++) st[i + 1] = st[i] + deg[i];
    long *adj = malloc(2 * m * sizeof(long)), *pos = calloc(n, sizeof(long));
    for (long i = 0; i < m; i++) { adj[st[U[i]] + pos[U[i]]++] = W[i]; adj[st[W[i]] + pos[W[i]]++] = U[i]; }
    long *d = malloc(n * sizeof(long)), *q = malloc(n * sizeof(long));
    for (int k = 2; k < c; k++) {
        long s = atol(v[k]); for (long i = 0; i < n; i++) d[i] = -1;
        long h = 0, t = 0; d[s] = 0; q[t++] = s;
        while (h < t) { long x = q[h++]; for (long i = st[x]; i < st[x + 1]; i++) { long y = adj[i]; if (d[y] < 0) { d[y] = d[x] + 1; q[t++] = y; } } }
        long cnt[64] = {0}; for (long i = 0; i < n; i++) cnt[d[i]]++;
        printf("src %ld:", s); for (int j = 0; j < 8; j++) printf(" d%d=%ld", j, cnt[j]); printf("\n");
    }
}
