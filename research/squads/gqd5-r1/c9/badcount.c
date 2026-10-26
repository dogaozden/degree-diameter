/* usage: badcount EDGEFILE D  -> prints "maxdeg maxdist badpairs n" ; badpairs = ordered pairs with dist > D (or unreachable) */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int main(int argc, char **argv) {
    FILE *f = fopen(argv[1], "r"); int D = atoi(argv[2]);
    int n; if (fscanf(f, "%d", &n) != 1) return 1;
    int *eu = malloc(sizeof(int) * 4000000), *ev = malloc(sizeof(int) * 4000000); int m = 0;
    int a, b; while (fscanf(f, "%d %d", &a, &b) == 2) { eu[m] = a; ev[m] = b; m++; }
    int *deg = calloc(n, sizeof(int));
    for (int i = 0; i < m; i++) { deg[eu[i]]++; deg[ev[i]]++; }
    int *off = malloc(sizeof(int) * (n + 1)); off[0] = 0;
    for (int i = 0; i < n; i++) off[i + 1] = off[i] + deg[i];
    int *pos = malloc(sizeof(int) * n); for (int i = 0; i < n; i++) pos[i] = off[i];
    int *adj = malloc(sizeof(int) * 2 * m + 4);
    for (int i = 0; i < m; i++) { adj[pos[eu[i]]++] = ev[i]; adj[pos[ev[i]]++] = eu[i]; }
    int maxdeg = 0; for (int i = 0; i < n; i++) if (deg[i] > maxdeg) maxdeg = deg[i];
    int *dist = malloc(sizeof(int) * n), *queue = malloc(sizeof(int) * n);
    long long bad = 0; int maxd = 0;
    for (int s = 0; s < n; s++) {
        for (int i = 0; i < n; i++) dist[i] = -1;
        int h = 0, t = 0; queue[t++] = s; dist[s] = 0;
        while (h < t) { int u = queue[h++]; if (dist[u] >= D) continue;
            for (int k = off[u]; k < off[u + 1]; k++) { int w = adj[k]; if (dist[w] < 0) { dist[w] = dist[u] + 1; queue[t++] = w; } } }
        for (int i = 0; i < n; i++) { if (dist[i] < 0 || dist[i] > D) bad++; if (dist[i] > maxd) maxd = dist[i]; }
    }
    printf("maxdeg %d maxdist_within_D %d badpairs %lld n %d\n", maxdeg, maxd, bad, n);
    return 0;
}
