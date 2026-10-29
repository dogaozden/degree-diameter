/* bfs.c: all-pairs BFS checker for a 2-coloured graph.
   stdin: n m, then n colours (0/1), then m edges "u v".
   argv: sameT diffT (distance thresholds for same-colour and different-colour pairs).
   stdout: n maxdeg maxsame sameviol maxdiff diffviol connected ex_u ex_v ex_d
   sameviol / diffviol count ordered pairs (u != v) exceeding the thresholds; disconnected pairs count as violations. */
#include <stdio.h>
#include <stdlib.h>
int main(int argc, char **argv) {
    int sameT = argc > 1 ? atoi(argv[1]) : 6, diffT = argc > 2 ? atoi(argv[2]) : 5;
    int n, m;
    if (scanf("%d %d", &n, &m) != 2) return 1;
    int *col = malloc(sizeof(int) * n);
    for (int i = 0; i < n; i++) if (scanf("%d", &col[i]) != 1) return 1;
    int *eu = malloc(sizeof(int) * (m + 1)), *ev = malloc(sizeof(int) * (m + 1));
    int *deg = calloc(n + 1, sizeof(int));
    for (int i = 0; i < m; i++) {
        if (scanf("%d %d", &eu[i], &ev[i]) != 2) return 1;
        deg[eu[i]]++; deg[ev[i]]++;
    }
    int *start = malloc(sizeof(int) * (n + 1));
    start[0] = 0; for (int i = 0; i < n; i++) start[i + 1] = start[i] + deg[i];
    int *fill = calloc(n, sizeof(int)); int *adj = malloc(sizeof(int) * (2 * m + 1));
    for (int i = 0; i < m; i++) {
        adj[start[eu[i]] + fill[eu[i]]++] = ev[i];
        adj[start[ev[i]] + fill[ev[i]]++] = eu[i];
    }
    int maxdeg = 0; for (int i = 0; i < n; i++) if (deg[i] > maxdeg) maxdeg = deg[i];
    int *dist = malloc(sizeof(int) * n), *q = malloc(sizeof(int) * n);
    int maxsame = 0, maxdiff = 0, connected = 1, ex_u = -1, ex_v = -1, ex_d = -1;
    long sameviol = 0, diffviol = 0;
    for (int s = 0; s < n; s++) {
        for (int i = 0; i < n; i++) dist[i] = -1;
        int h = 0, tl = 0; q[tl++] = s; dist[s] = 0;
        while (h < tl) {
            int x = q[h++];
            for (int k = start[x]; k < start[x + 1]; k++) {
                int y = adj[k];
                if (dist[y] < 0) { dist[y] = dist[x] + 1; q[tl++] = y; }
            }
        }
        for (int t = 0; t < n; t++) {
            if (t == s) continue;
            if (col[t] == col[s]) {
                if (dist[t] < 0) { connected = 0; sameviol++; continue; }
                if (dist[t] > maxsame) maxsame = dist[t];
                if (dist[t] > sameT) {
                    sameviol++;
                    if (ex_u < 0 || dist[t] > ex_d) { ex_u = s; ex_v = t; ex_d = dist[t]; }
                }
            } else {
                if (dist[t] < 0) { connected = 0; diffviol++; continue; }
                if (dist[t] > maxdiff) maxdiff = dist[t];
                if (dist[t] > diffT) diffviol++;
            }
        }
    }
    printf("%d %d %d %ld %d %ld %d %d %d %d\n", n, maxdeg, maxsame, sameviol, maxdiff, diffviol, connected, ex_u, ex_v, ex_d);
    return 0;
}
