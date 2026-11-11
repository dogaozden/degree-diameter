/* c8 helper: exact diameter of a simple undirected graph by BFS from every vertex.
   stdin : "n E" then E lines "a b" (0-based, distinct undirected edges, no loops).
   stdout: the diameter, or -1 if the graph is disconnected. */
#include <stdio.h>
#include <stdlib.h>

int main(void) {
    int n, E;
    if (scanf("%d %d", &n, &E) != 2 || n <= 0 || E < 0) return 2;
    int *ea = malloc(sizeof(int) * (size_t)(E > 0 ? E : 1));
    int *eb = malloc(sizeof(int) * (size_t)(E > 0 ? E : 1));
    int *deg = calloc((size_t)n, sizeof(int));
    for (int i = 0; i < E; i++) {
        if (scanf("%d %d", &ea[i], &eb[i]) != 2) return 2;
        if (ea[i] < 0 || ea[i] >= n || eb[i] < 0 || eb[i] >= n) return 2;
        deg[ea[i]]++;
        deg[eb[i]]++;
    }
    int *off = malloc(sizeof(int) * (size_t)(n + 1));
    off[0] = 0;
    for (int v = 0; v < n; v++) off[v + 1] = off[v] + deg[v];
    int *adj = malloc(sizeof(int) * (size_t)(off[n] > 0 ? off[n] : 1));
    int *fill = calloc((size_t)n, sizeof(int));
    for (int i = 0; i < E; i++) {
        int a = ea[i], b = eb[i];
        adj[off[a] + fill[a]++] = b;
        adj[off[b] + fill[b]++] = a;
    }
    int *dist = malloc(sizeof(int) * (size_t)n);
    int *queue = malloc(sizeof(int) * (size_t)n);
    int diam = 0;
    for (int s = 0; s < n; s++) {
        for (int v = 0; v < n; v++) dist[v] = -1;
        int head = 0, tail = 0;
        dist[s] = 0;
        queue[tail++] = s;
        while (head < tail) {
            int v = queue[head++];
            for (int k = off[v]; k < off[v + 1]; k++) {
                int t = adj[k];
                if (dist[t] < 0) {
                    dist[t] = dist[v] + 1;
                    queue[tail++] = t;
                }
            }
        }
        if (tail < n) {
            printf("-1\n");
            return 0;
        }
        if (dist[queue[tail - 1]] > diam) diam = dist[queue[tail - 1]];
    }
    printf("%d\n", diam);
    return 0;
}
