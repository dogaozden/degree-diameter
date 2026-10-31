/* farlist: list the vertex pairs at distance > D (big-squad-4-8 job). Usage: farlist EDGES [D]
   Prints "u v dist" for every unordered far pair (dist -1 = unreachable), then a per-vertex count summary. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int main(int c, char **v) {
    FILE *f = fopen(v[1], "r"); int D = c > 2 ? atoi(v[2]) : 8; int n, a, b, m = 0;
    if (!f || fscanf(f, "%d", &n) != 1) return 2;
    int *deg = calloc(n, sizeof(int)), cap = 1 << 16, *U = malloc(cap * 4), *W = malloc(cap * 4);
    while (fscanf(f, "%d %d", &a, &b) == 2) { if (m == cap) { cap *= 2; U = realloc(U, cap * 4); W = realloc(W, cap * 4); } U[m] = a; W[m] = b; m++; deg[a]++; deg[b]++; }
    int *st = calloc(n + 1, sizeof(int)); for (int i = 0; i < n; i++) st[i + 1] = st[i] + deg[i];
    int *adj = malloc(2 * m * sizeof(int)), *pos = calloc(n, sizeof(int));
    for (int i = 0; i < m; i++) { adj[st[U[i]] + pos[U[i]]++] = W[i]; adj[st[W[i]] + pos[W[i]]++] = U[i]; }
    int *dist = malloc(n * sizeof(int)), *q = malloc(n * sizeof(int)), *cnt = calloc(n, sizeof(int)); long tot = 0;
    for (int s = 0; s < n; s++) {
        for (int i = 0; i < n; i++) dist[i] = -1; dist[s] = 0; int h = 0, t = 0; q[t++] = s;
        while (h < t) { int x = q[h++]; for (int i = st[x]; i < st[x + 1]; i++) { int y = adj[i]; if (dist[y] < 0) { dist[y] = dist[x] + 1; q[t++] = y; } } }
        for (int x = s + 1; x < n; x++) if (dist[x] < 0 || dist[x] > D) { printf("%d %d %d\n", s, x, dist[x]); cnt[s]++; cnt[x]++; tot++; }
    }
    int nv = 0, mx = 0, arg = -1; for (int i = 0; i < n; i++) { if (cnt[i]) nv++; if (cnt[i] > mx) { mx = cnt[i]; arg = i; } }
    fprintf(stderr, "far pairs %ld, vertices involved %d, max per vertex %d (vertex %d)\n", tot, nv, mx, arg);
    return 0;
}
