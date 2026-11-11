/* critslack: for one edge (u,v) of a graph, list the pairs that become far (> D) when the edge is deleted, with their
   original distance (slack = D_max(pair) - original distance, D_max = D for opposite sides, D-1 for the same side).
   Usage: critslack EDGES u v D */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int n, *st, *adj, *deg; int du, dv;
static void bfs(int s, int *dist, int skipu, int skipv) {
    int *q = malloc(n * 4); for (int i = 0; i < n; i++) dist[i] = -1; dist[s] = 0; int h = 0, t = 0; q[t++] = s;
    while (h < t) { int x = q[h++]; for (int i = st[x]; i < st[x + 1]; i++) { int y = adj[i];
        if ((x == skipu && y == skipv) || (x == skipv && y == skipu)) continue; if (dist[y] < 0) { dist[y] = dist[x] + 1; q[t++] = y; } } }
    free(q);
}
int main(int c, char **v) {
    FILE *f = fopen(v[1], "r"); int u = atoi(v[2]), w = atoi(v[3]), D = atoi(v[4]); int m = 0, a, b, cap = 1 << 16;
    fscanf(f, "%d", &n); int *U = malloc(cap * 4), *W = malloc(cap * 4); deg = calloc(n, 4);
    while (fscanf(f, "%d %d", &a, &b) == 2) { if (m == cap) { cap *= 2; U = realloc(U, cap * 4); W = realloc(W, cap * 4); } U[m] = a; W[m] = b; m++; deg[a]++; deg[b]++; }
    st = calloc(n + 1, 4); for (int i = 0; i < n; i++) st[i + 1] = st[i] + deg[i]; adj = malloc(2 * m * 4); int *pos = calloc(n, 4);
    for (int i = 0; i < m; i++) { adj[st[U[i]] + pos[U[i]]++] = W[i]; adj[st[W[i]] + pos[W[i]]++] = U[i]; }
    int *d0 = malloc(n * 4), *d1 = malloc(n * 4), *du0 = malloc(n * 4), *dv0 = malloc(n * 4); long ab[16][16]; memset(ab, 0, sizeof ab); long hist[16][16]; memset(hist, 0, sizeof hist); long tot = 0;
    bfs(u, du0, u, w); bfs(w, dv0, u, w);
    int *side = malloc(n * 4); bfs(0, d0, -1, -1); for (int i = 0; i < n; i++) side[i] = d0[i] & 1;
    for (int s = 0; s < n; s++) { bfs(s, d0, -1, -1); bfs(s, d1, u, w);
        for (int t = s + 1; t < n; t++) { int lim = (side[s] == side[t]) ? D - 1 : D;
            if (d0[t] <= lim && (d1[t] < 0 || d1[t] > lim)) { tot++; hist[lim - d0[t]][side[s] == side[t]]++;
                if (lim == d0[t]) { int al, be; if (du0[s] + 1 + dv0[t] == d0[t]) { al = du0[s]; be = dv0[t]; } else { al = dv0[s]; be = du0[t]; } if (al > be) { int tmp = al; al = be; be = tmp; } ab[al][be]++; } } } }
    printf("edge %d-%d: %ld pairs become far\n", u, w, tot);
    for (int k = 0; k < 10; k++) if (hist[k][0] + hist[k][1]) printf("  slack %d: same-side %ld, opposite %ld\n", k, hist[k][1], hist[k][0]);
    printf("  slack-0 pairs by (min, max) of the distances of the two ends to the edge (in X - e):\n");
    for (int i = 0; i < 10; i++) for (int j = 0; j < 10; j++) if (ab[i][j]) printf("    (%d,%d): %ld\n", i, j, ab[i][j]);
    return 0;
}
