#include <stdlib.h>
#include <string.h>
/* number of ordered pairs (u,v), u != v, with dist(u,v) > D in the graph on n vertices with m edges (unreachable counts).
   per_vertex (may be NULL) receives for each u the number of v with dist(u,v) > D. */
long count_bad(int n, int m, const int *eu, const int *ev, int D, long *per_vertex) {
    int *deg = calloc(n + 1, sizeof(int));
    for (int i = 0; i < m; i++) { deg[eu[i]]++; deg[ev[i]]++; }
    int *start = malloc((n + 1) * sizeof(int));
    start[0] = 0;
    for (int u = 0; u < n; u++) start[u + 1] = start[u] + deg[u];
    int *fill = malloc(n * sizeof(int));
    for (int u = 0; u < n; u++) fill[u] = start[u];
    int *adj = malloc((2 * m + 1) * sizeof(int));
    for (int i = 0; i < m; i++) {
        adj[fill[eu[i]]++] = ev[i];
        adj[fill[ev[i]]++] = eu[i];
    }
    int *dist = malloc(n * sizeof(int));
    int *q = malloc(n * sizeof(int));
    long bad = 0;
    for (int s = 0; s < n; s++) {
        for (int u = 0; u < n; u++) dist[u] = -1;
        int h = 0, t = 0;
        q[t++] = s; dist[s] = 0;
        while (h < t) {
            int u = q[h++];
            if (dist[u] == D) continue;
            for (int e = start[u]; e < start[u + 1]; e++) {
                int w = adj[e];
                if (dist[w] < 0) { dist[w] = dist[u] + 1; q[t++] = w; }
            }
        }
        long b = (long)(n - t);
        bad += b;
        if (per_vertex) per_vertex[s] = b;
    }
    free(deg); free(start); free(fill); free(adj); free(dist); free(q);
    return bad;
}

/* bit-parallel version: reach[v] = set of sources s with dist(s,v) <= k. Same output as count_bad. */
#include <stdint.h>
#include <string.h>
long count_bad_bits(int n, int m, const int *eu, const int *ev, int D, long *per_vertex) {
    int W = (n + 63) / 64;
    uint64_t *cur = calloc((size_t)n * W, sizeof(uint64_t));
    uint64_t *nxt = calloc((size_t)n * W, sizeof(uint64_t));
    for (int v = 0; v < n; v++) cur[(size_t)v * W + v / 64] |= (uint64_t)1 << (v % 64);
    for (int k = 0; k < D; k++) {
        memcpy(nxt, cur, (size_t)n * W * sizeof(uint64_t));
        for (int i = 0; i < m; i++) {
            uint64_t *a = nxt + (size_t)eu[i] * W; const uint64_t *b = cur + (size_t)ev[i] * W;
            uint64_t *c = nxt + (size_t)ev[i] * W; const uint64_t *d = cur + (size_t)eu[i] * W;
            for (int w = 0; w < W; w++) { a[w] |= b[w]; c[w] |= d[w]; }
        }
        uint64_t *t = cur; cur = nxt; nxt = t;
    }
    long bad = 0;
    for (int v = 0; v < n; v++) {
        long cnt = 0;
        for (int w = 0; w < W; w++) cnt += __builtin_popcountll(cur[(size_t)v * W + w]);
        long b = (long)n - cnt;           /* sources not reaching v (v itself is reached) */
        bad += b;
        if (per_vertex) per_vertex[v] = b;
    }
    free(cur); free(nxt);
    return bad;
}
