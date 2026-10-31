/* Independent all-pairs check of an edge list: simple, max degree, bipartite, connected, exact diameter.
   Bit-parallel BFS, 64 sources at a time; no symmetry assumed. Usage: apsp EDGES d D */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
int main(int c, char **v) {
    FILE *f = fopen(v[1], "r"); int d = atoi(v[2]), D = atoi(v[3]); long n, m = 0, cap = 1 << 20;
    if (fscanf(f, "%ld", &n) != 1) return 2;
    long *U = malloc(cap * 8), *W = malloc(cap * 8); long a, b;
    while (fscanf(f, "%ld %ld", &a, &b) == 2) { if (m == cap) { cap *= 2; U = realloc(U, cap * 8); W = realloc(W, cap * 8); } U[m] = a; W[m] = b; m++; }
    long *deg = calloc(n + 1, 8);
    for (long i = 0; i < m; i++) { if (U[i] == W[i] || U[i] < 0 || W[i] < 0 || U[i] >= n || W[i] >= n) { printf("BAD edge %ld\n", i); return 1; } deg[U[i]]++; deg[W[i]]++; }
    long *st = calloc(n + 1, 8); for (long i = 0; i < n; i++) st[i + 1] = st[i] + deg[i];
    long *adj = malloc(2 * m * 8), *pos = calloc(n, 8);
    for (long i = 0; i < m; i++) { adj[st[U[i]] + pos[U[i]]++] = W[i]; adj[st[W[i]] + pos[W[i]]++] = U[i]; }
    long maxd = 0, mind = n;
    for (long x = 0; x < n; x++) { long k = deg[x]; if (k > maxd) maxd = k; if (k < mind) mind = k;
        for (long i = st[x]; i < st[x + 1]; i++) for (long j = i + 1; j < st[x + 1]; j++) if (adj[i] == adj[j]) { printf("RESULT INVALID repeated edge at %ld\n", x); return 1; } }
    int *col = malloc(n * sizeof(int)); for (long i = 0; i < n; i++) col[i] = -1;
    long *q = malloc(n * 8); long h = 0, t = 0; col[0] = 0; q[t++] = 0; int bip = 1;
    while (h < t) { long x = q[h++]; for (long i = st[x]; i < st[x + 1]; i++) { long y = adj[i]; if (col[y] < 0) { col[y] = 1 - col[x]; q[t++] = y; } else if (col[y] == col[x]) bip = 0; } }
    if (t != n) { printf("RESULT INVALID disconnected (%ld of %ld)\n", t, n); return 1; }
    uint64_t *vis = malloc(n * 8), *fr = malloc(n * 8), *nx = malloc(n * 8); int diam = 0;
    for (long s0 = 0; s0 < n; s0 += 64) {
        memset(vis, 0, n * 8); memset(fr, 0, n * 8);
        int ns = (n - s0 < 64) ? (int)(n - s0) : 64; uint64_t full = ns == 64 ? ~0ULL : ((1ULL << ns) - 1);
        for (int k = 0; k < ns; k++) { vis[s0 + k] |= 1ULL << k; fr[s0 + k] |= 1ULL << k; }
        int lev = 0;
        for (;;) { int any = 0;
            for (long x = 0; x < n; x++) { uint64_t acc = 0; for (long i = st[x]; i < st[x + 1]; i++) acc |= fr[adj[i]]; acc &= ~vis[x]; nx[x] = acc; if (acc) any = 1; }
            if (!any) break; lev++; for (long x = 0; x < n; x++) vis[x] |= nx[x]; uint64_t *tmp = fr; fr = nx; nx = tmp; }
        for (long x = 0; x < n; x++) if (vis[x] != full) { printf("RESULT INVALID unreached\n"); return 1; }
        if (lev > diam) diam = lev;
    }
    printf("n=%ld edges=%ld degree min=%ld max=%ld bipartite=%s diameter=%d\n", n, m, mind, maxd, bip ? "yes" : "no", diam);
    if (bip && maxd <= d && diam <= D) printf("RESULT VALID d=%d D=%d n=%ld\n", d, D, n); else printf("RESULT INVALID\n");
    return 0;
}
