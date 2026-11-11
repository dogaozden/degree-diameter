/* damage profile of single-edge deletions in a bipartite graph with diameter 5 (same side <= 4) */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int n, deg[4096], adj[4096][8]; unsigned char *D0, *D1;
void bfs(int s, unsigned char *d, int dx, int dy) {
  static int q[4096]; for (int i = 0; i < n; i++) d[i] = 255; int h = 0, t = 0; d[s] = 0; q[t++] = s;
  while (h < t) { int x = q[h++]; for (int i = 0; i < deg[x]; i++) { int y = adj[x][i];
    if ((x == dx && y == dy) || (x == dy && y == dx)) continue; if (d[y] == 255) { d[y] = d[x] + 1; q[t++] = y; } } }
}
int main(int argc, char **argv) {
  FILE *f = fopen(argv[1], "r"); fscanf(f, "%d", &n); int u, v;
  while (fscanf(f, "%d %d", &u, &v) == 2) { adj[u][deg[u]++] = v; adj[v][deg[v]++] = u; }
  int half = n / 2;
  D0 = malloc((size_t)n * n); D1 = malloc((size_t)n * n);
  for (int s = 0; s < n; s++) bfs(s, D0 + (size_t)s * n, -1, -1);
  for (int k = 0; k < deg[0]; k++) {
    int x = 0, y = adj[0][k];
    for (int s = 0; s < n; s++) bfs(s, D1 + (size_t)s * n, x, y);
    int hist[8][8]; memset(hist, 0, sizeof hist); int tot = 0, byd[8] = {0};
    for (int a = 0; a < n; a++) for (int b = a + 1; b < n; b++) {
      int same = (a < half) == (b < half); int lim = same ? 4 : 5;
      if (D1[(size_t)a * n + b] <= lim) continue;
      tot++; byd[D0[(size_t)a * n + b]]++;
      /* orientation: a near x, b near y, or a near y, b near x */
      int p1 = D0[(size_t)a * n + x], r1 = D0[(size_t)b * n + y], p2 = D0[(size_t)a * n + y], r2 = D0[(size_t)b * n + x];
      int p, r; if (p1 + 1 + r1 == D0[(size_t)a * n + b]) { p = p1; r = r1; } else { p = r2; r = p2; }
      if (p > r) { int t = p; p = r; r = t; }
      hist[p][r]++;
    }
    printf("edge 0-%d: damaged %d; by old distance: d2 %d d3 %d d4 %d d5 %d; by (near,far) offsets:", y, tot, byd[2], byd[3], byd[4], byd[5]);
    for (int p = 0; p < 6; p++) for (int r = 0; r < 6; r++) if (hist[p][r]) printf(" (%d,%d):%d", p, r, hist[p][r]);
    printf("\n");
  }
  return 0;
}
