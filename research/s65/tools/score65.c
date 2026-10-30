/* score65.c: squad scorer for (6,5). Reads an edge list (first number n, then pairs u v, 0-based) and prints
 *   SCORE n=<n> maxdeg=<d> bipartite=<yes|no> simple=<yes|no> bad=<unordered pairs at distance > D> diam=<..>
 * bad = 0 with maxdeg <= 6, bipartite, simple and n > 684 is a candidate record (then run apsp.c).
 * Bit-parallel BFS, 64 sources at a time, depth capped at D (default 5; env D). usage: score65 EDGES */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int main(int argc, char **argv) {
    if (argc < 2) return 2;
    FILE *f = fopen(argv[1], "r"); if (!f) { printf("SCORE error cannot open\n"); return 2; }
    int D = getenv("D") ? atoi(getenv("D")) : 5;
    long n, m = 0, cap = 1 << 16, a, b;
    if (fscanf(f, "%ld", &n) != 1) return 2;
    long *U = malloc(cap * 8), *W = malloc(cap * 8);
    while (fscanf(f, "%ld %ld", &a, &b) == 2) { if (m == cap) { cap *= 2; U = realloc(U, cap * 8); W = realloc(W, cap * 8); } U[m] = a; W[m] = b; m++; }
    fclose(f);
    long *deg = calloc(n + 1, 8); int simple = 1;
    for (long i = 0; i < m; i++) { if (U[i] == W[i] || U[i] < 0 || W[i] < 0 || U[i] >= n || W[i] >= n) { printf("SCORE error bad edge %ld\n", i); return 1; } deg[U[i]]++; deg[W[i]]++; }
    long *st = calloc(n + 1, 8); for (long i = 0; i < n; i++) st[i + 1] = st[i] + deg[i];
    long *adj = malloc(2 * m * 8 + 8), *pos = calloc(n, 8);
    for (long i = 0; i < m; i++) { adj[st[U[i]] + pos[U[i]]++] = W[i]; adj[st[W[i]] + pos[W[i]]++] = U[i]; }
    long maxd = 0; for (long x = 0; x < n; x++) { if (deg[x] > maxd) maxd = deg[x];
        for (long i = st[x]; i < st[x + 1]; i++) for (long j = i + 1; j < st[x + 1]; j++) if (adj[i] == adj[j]) simple = 0; }
    int *col = malloc(n * sizeof(int)); for (long i = 0; i < n; i++) col[i] = -1; int bip = 1;
    long *q = malloc(n * 8);
    for (long s = 0; s < n; s++) if (col[s] < 0) { long h = 0, t = 0; col[s] = 0; q[t++] = s;
        while (h < t) { long x = q[h++]; for (long i = st[x]; i < st[x + 1]; i++) { long y = adj[i]; if (col[y] < 0) { col[y] = 1 - col[x]; q[t++] = y; } else if (col[y] == col[x]) bip = 0; } } }
    uint64_t *vis = malloc(n * 8), *fr = malloc(n * 8), *nx = malloc(n * 8);
    long long badord = 0; int diam = 0, beyond = 0;
    for (long s0 = 0; s0 < n; s0 += 64) {
        memset(vis, 0, n * 8); memset(fr, 0, n * 8);
        int ns = (n - s0 < 64) ? (int)(n - s0) : 64;
        for (int k = 0; k < ns; k++) { vis[s0 + k] |= 1ULL << k; fr[s0 + k] |= 1ULL << k; }
        for (int lev = 1; lev <= D; lev++) {
            int any = 0;
            for (long x = 0; x < n; x++) { uint64_t acc = 0; for (long i = st[x]; i < st[x + 1]; i++) acc |= fr[adj[i]]; acc &= ~vis[x]; nx[x] = acc; if (acc) any = 1; }
            for (long x = 0; x < n; x++) vis[x] |= nx[x];
            uint64_t *tmp = fr; fr = nx; nx = tmp;
            if (any && lev > diam) diam = lev;
            if (!any) break;
        }
        uint64_t full = ns == 64 ? ~0ULL : ((1ULL << ns) - 1);
        for (long x = 0; x < n; x++) { uint64_t miss = full & ~vis[x]; if (miss) { badord += __builtin_popcountll(miss); beyond = 1; } }
    }
    printf("SCORE n=%ld edges=%ld maxdeg=%ld bipartite=%s simple=%s bad=%lld diam=%s%d\n", n, m, maxd, bip ? "yes" : "no",
           simple ? "yes" : "no", badord / 2, beyond ? ">" : "", beyond ? D : diam);
    return 0;
}
