/* cost of a cubic bipartite graph given as adjacency n*3 (points 0..n/2-1, lines n/2..n-1).
   returns number of same-side unordered pairs at distance > 6 (or disconnected); *diam = diameter (999 if disconnected) */
#include <string.h>
int score(int n, const int *adj, int *diam) {
    static int dist[1024], q[1024];
    int h = n / 2, bad = 0, dm = 0;
    for (int s = 0; s < n; s++) {
        for (int i = 0; i < n; i++) dist[i] = -1;
        int hd = 0, tl = 0; q[tl++] = s; dist[s] = 0;
        while (hd < tl) { int u = q[hd++]; for (int e = 0; e < 3; e++) { int v = adj[3 * u + e]; if (dist[v] < 0) { dist[v] = dist[u] + 1; q[tl++] = v; } } }
        for (int t = 0; t < n; t++) {
            if (dist[t] < 0) { dm = 999; if (s < t && (s < h) == (t < h)) bad++; continue; }
            if (dist[t] > dm) dm = dist[t];
            if (s < t && (s < h) == (t < h) && dist[t] > 6) bad++;
        }
    }
    *diam = dm; return bad;
}
