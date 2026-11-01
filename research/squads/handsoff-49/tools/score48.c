/* score48: scorer for any edge list (big-squad-4-8 job).
   Input: "n" then lines "u v" (0-based). Checks simple, max degree, bipartite, connected; counts unordered vertex
   pairs at distance > D (unreachable pairs count too) and the exact diameter. Bit-parallel BFS, 64 sources at a time.
   Usage: score48 EDGES [d D]    (default d=4 D=8)
   Last line: RESULT VALID n=... | RESULT INVALID n=... far=... reason=...   Exit code 0 iff VALID. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
int main(int c, char **v) {
    if (c < 2) { fprintf(stderr, "usage: score48 EDGES [d D]\n"); return 2; }
    int d = c > 2 ? atoi(v[2]) : 4, D = c > 3 ? atoi(v[3]) : 8;
    FILE *f = fopen(v[1], "r"); if (!f) { printf("RESULT INVALID cannot open\n"); return 2; }
    long n, m = 0, cap = 1 << 16;
    if (fscanf(f, "%ld", &n) != 1 || n <= 0) { printf("RESULT INVALID bad header\n"); return 2; }
    long *U = malloc(cap * 8), *W = malloc(cap * 8), a, b;
    while (fscanf(f, "%ld %ld", &a, &b) == 2) {
        if (m == cap) { cap *= 2; U = realloc(U, cap * 8); W = realloc(W, cap * 8); }
        U[m] = a; W[m] = b; m++;
    }
    long *deg = calloc(n, 8);
    for (long i = 0; i < m; i++) {
        if (U[i] == W[i] || U[i] < 0 || W[i] < 0 || U[i] >= n || W[i] >= n) { printf("RESULT INVALID n=%ld reason=bad_edge_%ld\n", n, i); return 1; }
        deg[U[i]]++; deg[W[i]]++;
    }
    long *st = calloc(n + 1, 8); for (long i = 0; i < n; i++) st[i + 1] = st[i] + deg[i];
    long *adj = malloc((2 * m + 1) * 8), *pos = calloc(n, 8);
    for (long i = 0; i < m; i++) { adj[st[U[i]] + pos[U[i]]++] = W[i]; adj[st[W[i]] + pos[W[i]]++] = U[i]; }
    long maxd = 0, mind = n;
    for (long x = 0; x < n; x++) {
        if (deg[x] > maxd) maxd = deg[x]; if (deg[x] < mind) mind = deg[x];
        for (long i = st[x]; i < st[x + 1]; i++) for (long j = i + 1; j < st[x + 1]; j++)
            if (adj[i] == adj[j]) { printf("RESULT INVALID n=%ld reason=repeated_edge_at_%ld\n", n, x); return 1; }
    }
    int *col = malloc(n * sizeof(int)); for (long i = 0; i < n; i++) col[i] = -1;
    long *q = malloc(n * 8); int bip = 1; long comps = 0;
    for (long s = 0; s < n; s++) {
        if (col[s] >= 0) continue; comps++;
        long h = 0, t = 0; col[s] = 0; q[t++] = s;
        while (h < t) { long x = q[h++]; for (long i = st[x]; i < st[x + 1]; i++) { long y = adj[i];
            if (col[y] < 0) { col[y] = 1 - col[x]; q[t++] = y; } else if (col[y] == col[x]) bip = 0; } }
    }
    uint64_t *vis = malloc(n * 8), *fr = malloc(n * 8), *nx = malloc(n * 8);
    int diam = 0; long long far = 0; /* ordered pairs (s,x) with dist > D or unreachable */
    for (long s0 = 0; s0 < n; s0 += 64) {
        memset(vis, 0, n * 8); memset(fr, 0, n * 8);
        int ns = (n - s0 < 64) ? (int)(n - s0) : 64; uint64_t full = ns == 64 ? ~0ULL : ((1ULL << ns) - 1);
        for (int k = 0; k < ns; k++) { vis[s0 + k] |= 1ULL << k; fr[s0 + k] |= 1ULL << k; }
        int lev = 0;
        for (;;) {
            int any = 0;
            for (long x = 0; x < n; x++) { uint64_t acc = 0; for (long i = st[x]; i < st[x + 1]; i++) acc |= fr[adj[i]];
                acc &= ~vis[x]; nx[x] = acc; if (acc) any = 1; }
            if (!any) break;
            lev++;
            if (lev == D + 1) { /* everything still unvisited after level D is far */
                for (long x = 0; x < n; x++) far += __builtin_popcountll(full & ~vis[x]);
            }
            for (long x = 0; x < n; x++) vis[x] |= nx[x];
            uint64_t *tmp = fr; fr = nx; nx = tmp;
        }
        if (lev <= D) for (long x = 0; x < n; x++) far += __builtin_popcountll(full & ~vis[x]); /* unreachable */
        if (lev > diam) diam = lev;
    }
    int disconnected = comps > 1;
    printf("n=%ld edges=%ld degree min=%ld max=%ld bipartite=%s components=%ld diameter=%s%d far_pairs=%lld\n", n, m, mind, maxd,
           bip ? "yes" : "no", comps, disconnected ? ">=" : "", diam, far / 2);
    if (bip && !disconnected && maxd <= d && diam <= D) { printf("RESULT VALID d=%d D=%d n=%ld\n", d, D, n); return 0; }
    printf("RESULT INVALID n=%ld far=%lld reason=%s%s%s\n", n, far / 2, bip ? "" : "nonbipartite,", maxd > d ? "degree," : "",
           (disconnected || diam > D) ? "diameter" : "");
    return 1;
}
