/* violations: for each source in list (or all if "all"), count vertices at distance > D; print total and per-source max.
   usage: viol EDGES D src... | viol EDGES D all */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int main(int c, char **v) {
    FILE *f = fopen(v[1], "r"); int D = atoi(v[2]); long n, m = 0, a, b;
    if (fscanf(f, "%ld", &n) != 1) return 2;
    long cap = 1 << 19; long *U = malloc(cap * sizeof(long)), *W = malloc(cap * sizeof(long));
    while (fscanf(f, "%ld %ld", &a, &b) == 2) { U[m] = a; W[m] = b; m++; }
    long *deg = calloc(n + 1, sizeof(long));
    for (long i = 0; i < m; i++) { deg[U[i]]++; deg[W[i]]++; }
    long *st = calloc(n + 1, sizeof(long)); for (long i = 0; i < n; i++) st[i + 1] = st[i] + deg[i];
    long *adj = malloc(2 * m * sizeof(long)), *pos = calloc(n + 1, sizeof(long));
    for (long i = 0; i < m; i++) { adj[st[U[i]] + pos[U[i]]++] = W[i]; adj[st[W[i]] + pos[W[i]]++] = U[i]; }
    long *d = malloc(n * sizeof(long)), *q = malloc(n * sizeof(long));
    long total = 0; long nsrc = 0;
    int all = (c > 3 && strcmp(v[3], "all") == 0);
    long lim = all ? n : c;
    for (long k = 3; k < (all ? 4 : c); k++) {
        long s = atol(v[k]); if (all) s = k - 3;
        for (long i = 0; i < n; i++) d[i] = -1;
        long h = 0, t = 0; d[s] = 0; q[t++] = s;
        while (h < t) { long x = q[h++]; for (long i = st[x]; i < st[x + 1]; i++) { long y = adj[i]; if (d[y] < 0) { d[y] = d[x] + 1; q[t++] = y; } } }
        long bad = 0; for (long i = 0; i < n; i++) if (d[i] < 0 || d[i] > D) bad++;
        total += bad; nsrc++;
        if (!all) printf("src %ld: vertices beyond D: %ld\n", s, bad);
        if (all && (k - 3) % 2000 == 0) fprintf(stderr, "done %ld\n", k - 3);
        if (all) { if (k - 3 >= 0) { } }
    }
    printf("sources %ld total_beyond %ld\n", nsrc, total);
    return 0;
}
