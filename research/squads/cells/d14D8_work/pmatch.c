/* pmatch.c: perfect matching of a bipartite graph (Hopcroft-Karp). Input (text): "n d" then n lines of d right-vertex
   ids (-1 = absent) for each left vertex; random seed as argv[1] shuffles adjacency order. Output: n lines, match[i]. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
static int n, d, *adj, *ml, *mr, *dist, *q;
static unsigned long long rs = 88172645463325252ULL;
static unsigned long long rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int bfs(void) {
    int h = 0, t = 0, found = 0;
    for (int i = 0; i < n; i++) { if (ml[i] < 0) { dist[i] = 0; q[t++] = i; } else dist[i] = -1; }
    while (h < t) { int u = q[h++];
        for (int k = 0; k < d; k++) { int v = adj[u * d + k]; if (v < 0) continue; int w = mr[v];
            if (w < 0) found = 1; else if (dist[w] < 0) { dist[w] = dist[u] + 1; q[t++] = w; } } }
    return found;
}
static int dfs(int u) {
    for (int k = 0; k < d; k++) { int v = adj[u * d + k]; if (v < 0) continue; int w = mr[v];
        if (w < 0 || (dist[w] == dist[u] + 1 && dfs(w))) { ml[u] = v; mr[v] = u; return 1; } }
    dist[u] = -1; return 0;
}
int main(int argc, char **argv) {
    if (argc > 1) rs ^= strtoull(argv[1], 0, 10) * 0x9E3779B97F4A7C15ULL + 7;
    if (scanf("%d %d", &n, &d) != 2) return 1;
    adj = malloc(sizeof(int) * n * d);
    for (int i = 0; i < n * d; i++) if (scanf("%d", &adj[i]) != 1) return 1;
    for (int i = 0; i < n; i++) for (int k = d - 1; k > 0; k--) { int j = rnd() % (k + 1); int t = adj[i*d+k]; adj[i*d+k] = adj[i*d+j]; adj[i*d+j] = t; }
    ml = malloc(sizeof(int) * n); mr = malloc(sizeof(int) * n); dist = malloc(sizeof(int) * n); q = malloc(sizeof(int) * n);
    memset(ml, -1, sizeof(int) * n); memset(mr, -1, sizeof(int) * n);
    int size = 0;
    while (bfs()) for (int i = 0; i < n; i++) if (ml[i] < 0 && dfs(i)) size++;
    fprintf(stderr, "matching size %d of %d\n", size, n);
    for (int i = 0; i < n; i++) printf("%d\n", ml[i]);
    return size == n ? 0 : 2;
}
