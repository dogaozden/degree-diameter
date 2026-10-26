/* dcount EDGES D : reads "n" then "u v" lines; prints n, edges, max degree, bipartite, connected,
   number of unordered pairs at distance > D (or unreachable), and the max finite distance. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int main(int argc, char **argv) {
    FILE *f = fopen(argv[1], "r"); int D = atoi(argv[2]); int n; long m = 0;
    if (fscanf(f, "%d", &n) != 1) return 1;
    int *eu = malloc(sizeof(int) * 20000), *ev = malloc(sizeof(int) * 20000); int cap = 20000;
    int a, b; while (fscanf(f, "%d %d", &a, &b) == 2) { if (m == cap) { cap *= 2; eu = realloc(eu, sizeof(int) * cap); ev = realloc(ev, sizeof(int) * cap); } eu[m] = a; ev[m] = b; m++; }
    int *deg = calloc(n, sizeof(int)); for (long i = 0; i < m; i++) { deg[eu[i]]++; deg[ev[i]]++; }
    int maxd = 0, mind = 1 << 30; for (int i = 0; i < n; i++) { if (deg[i] > maxd) maxd = deg[i]; if (deg[i] < mind) mind = deg[i]; }
    int *start = calloc(n + 1, sizeof(int)); for (int i = 0; i < n; i++) start[i + 1] = start[i] + deg[i];
    int *pos = malloc(sizeof(int) * n); memcpy(pos, start, sizeof(int) * n); int *adj = malloc(sizeof(int) * 2 * m);
    for (long i = 0; i < m; i++) { adj[pos[eu[i]]++] = ev[i]; adj[pos[ev[i]]++] = eu[i]; }
    /* bipartite check via BFS colours */
    int *col = malloc(sizeof(int) * n); for (int i = 0; i < n; i++) col[i] = -1;
    int bip = 1; int *qu = malloc(sizeof(int) * n); int *dist = malloc(sizeof(int) * n);
    col[0] = 0; int h = 0, t = 0; qu[t++] = 0;
    while (h < t) { int x = qu[h++]; for (int k = start[x]; k < start[x + 1]; k++) { int y = adj[k]; if (col[y] < 0) { col[y] = 1 - col[x]; qu[t++] = y; } else if (col[y] == col[x]) bip = 0; } }
    int conn = (t == n);
    long bad = 0; int maxdist = 0; long badpairs_same = 0;
    for (int s = 0; s < n; s++) {
        for (int i = 0; i < n; i++) dist[i] = -1;
        h = 0; t = 0; dist[s] = 0; qu[t++] = s;
        while (h < t) { int x = qu[h++]; if (dist[x] >= D) continue; for (int k = start[x]; k < start[x + 1]; k++) { int y = adj[k]; if (dist[y] < 0) { dist[y] = dist[x] + 1; qu[t++] = y; } } }
        for (int i = s + 1; i < n; i++) { if (dist[i] < 0) bad++; }
        for (int i = 0; i < t; i++) if (dist[qu[i]] > maxdist) maxdist = dist[qu[i]];
    }
    printf("n %d edges %ld maxdeg %d mindeg %d bipartite %d connected %d pairs_gt_D %ld (D=%d)\n", n, m, maxd, mind, bip, conn, bad, D);
    return 0;
}
