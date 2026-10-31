/* score37: shared scorer for job handsoff-37 (bipartite degree-diameter cell d = 3, D = 7).
   Reads an edge list in apsp.c format (first number n, then pairs "a b", 0-based) and prints one line:
     n=<n> edges=<m> maxdeg=<..> simple=<yes|no> bipartite=<yes|no> connected=<yes|no> far=<F> diam=<d or -1>
   far = number of UNORDERED vertex pairs at distance > 7 (unreachable pairs count too). far = 0 with
   maxdeg <= 3, simple, bipartite, connected means diameter <= 7: a candidate (still run apsp.c on it).
   Bit-parallel BFS, 64 sources at a time, stops at depth 7 for the far count, then continues for the exact
   diameter only if far = 0. Usage: score37 EDGES   (exit code 0 = candidate, 1 = not)
   Build: gcc -O3 -march=native -o score37 score37.c */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
int main(int c, char **v) {
    if (c < 2) { fprintf(stderr, "usage: score37 EDGES\n"); return 2; }
    FILE *f = fopen(v[1], "r"); if (!f) { perror(v[1]); return 2; }
    long n, m = 0, cap = 1 << 16, a, b;
    if (fscanf(f, "%ld", &n) != 1) return 2;
    long *U = malloc(cap * 8), *W = malloc(cap * 8);
    while (fscanf(f, "%ld %ld", &a, &b) == 2) { if (m == cap) { cap *= 2; U = realloc(U, cap * 8); W = realloc(W, cap * 8); } U[m] = a; W[m] = b; m++; }
    fclose(f);
    long *deg = calloc(n + 1, 8); int simple = 1;
    for (long i = 0; i < m; i++) { if (U[i] == W[i] || U[i] < 0 || W[i] < 0 || U[i] >= n || W[i] >= n) { printf("BAD edge %ld\n", i); return 1; } deg[U[i]]++; deg[W[i]]++; }
    long *st = calloc(n + 1, 8); for (long i = 0; i < n; i++) st[i + 1] = st[i] + deg[i];
    long *adj = malloc(2 * m * 8 + 8), *pos = calloc(n, 8);
    for (long i = 0; i < m; i++) { adj[st[U[i]] + pos[U[i]]++] = W[i]; adj[st[W[i]] + pos[W[i]]++] = U[i]; }
    long maxd = 0;
    for (long x = 0; x < n; x++) { if (deg[x] > maxd) maxd = deg[x];
        for (long i = st[x]; i < st[x + 1]; i++) for (long j = i + 1; j < st[x + 1]; j++) if (adj[i] == adj[j]) simple = 0; }
    int *col = malloc(n * sizeof(int)); for (long i = 0; i < n; i++) col[i] = -1;
    long *q = malloc(n * 8), h = 0, t = 0; int bip = 1; long comps = 0;
    for (long s = 0; s < n; s++) if (col[s] < 0) { comps++; col[s] = 0; q[t++] = s;
        while (h < t) { long x = q[h++]; for (long i = st[x]; i < st[x + 1]; i++) { long y = adj[i]; if (col[y] < 0) { col[y] = 1 - col[x]; q[t++] = y; } else if (col[y] == col[x]) bip = 0; } } }
    uint64_t *vis = malloc(n * 8), *fr = malloc(n * 8), *nx = malloc(n * 8);
    long long farord = 0; int diam = 0;
    for (long s0 = 0; s0 < n; s0 += 64) {
        memset(vis, 0, n * 8); memset(fr, 0, n * 8);
        int ns = (n - s0 < 64) ? (int)(n - s0) : 64; uint64_t full = ns == 64 ? ~0ULL : ((1ULL << ns) - 1);
        for (int k = 0; k < ns; k++) { vis[s0 + k] |= 1ULL << k; fr[s0 + k] |= 1ULL << k; }
        int lev = 0;
        for (;;) { int any = 0;
            for (long x = 0; x < n; x++) { uint64_t acc = 0; for (long i = st[x]; i < st[x + 1]; i++) acc |= fr[adj[i]]; acc &= ~vis[x]; nx[x] = acc; if (acc) any = 1; }
            if (!any) break; lev++; for (long x = 0; x < n; x++) vis[x] |= nx[x]; uint64_t *tmp = fr; fr = nx; nx = tmp;
            if (lev == 7) { for (long x = 0; x < n; x++) farord += __builtin_popcountll(full & ~vis[x]); }
        }
        if (lev < 7) for (long x = 0; x < n; x++) farord += __builtin_popcountll(full & ~vis[x]);
        for (long x = 0; x < n; x++) if (vis[x] != full) { diam = -1; break; }
        if (diam >= 0 && lev > diam) diam = lev;
    }
    long long far = farord / 2;
    printf("n=%ld edges=%ld maxdeg=%ld simple=%s bipartite=%s connected=%s far=%lld diam=%d\n", n, m, maxd,
           simple ? "yes" : "no", bip ? "yes" : "no", comps == 1 ? "yes" : "no", far, diam);
    return (far == 0 && maxd <= 3 && simple && bip && comps == 1) ? 0 : 1;
}
