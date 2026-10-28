/* Referee checker: reads "n" then edges "u v" (0-based) from stdin; checks simple, bipartite (BFS 2-colouring),
   degree min/max, and the exact diameter by a plain BFS from every vertex (OpenMP). Written for this report.
   Usage: bfs [D [list]]; with "list", the pairs u < v at distance > D are written to stderr. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
static int cmpi(const void *a, const void *b) { int x = *(const int *)a, y = *(const int *)b; return (x > y) - (x < y); }
int main(int argc, char **argv) {
  int n; long m = 0, cap = 1 << 20;
  if (scanf("%d", &n) != 1) return 1;
  int *eu = malloc(cap * sizeof(int)), *ev = malloc(cap * sizeof(int)), u, v;
  while (scanf("%d %d", &u, &v) == 2) {
    if (m == cap) { cap *= 2; eu = realloc(eu, cap * sizeof(int)); ev = realloc(ev, cap * sizeof(int)); }
    if (u < 0 || v < 0 || u >= n || v >= n || u == v) { printf("BAD edge %d %d\n", u, v); return 1; }
    eu[m] = u; ev[m] = v; m++;
  }
  int *deg = calloc(n, sizeof(int));
  for (long i = 0; i < m; i++) { deg[eu[i]]++; deg[ev[i]]++; }
  long *off = malloc((n + 1) * sizeof(long)); off[0] = 0;
  for (int i = 0; i < n; i++) off[i + 1] = off[i] + deg[i];
  int *adj = malloc(2 * m * sizeof(int)), *fill = calloc(n, sizeof(int));
  for (long i = 0; i < m; i++) { adj[off[eu[i]] + fill[eu[i]]++] = ev[i]; adj[off[ev[i]] + fill[ev[i]]++] = eu[i]; }
  long multi = 0;
  for (int i = 0; i < n; i++) {
    qsort(adj + off[i], deg[i], sizeof(int), cmpi);
    for (long k = off[i] + 1; k < off[i + 1]; k++) if (adj[k] == adj[k - 1]) multi++;
  }
  int dmin = n, dmax = 0;
  for (int i = 0; i < n; i++) { if (deg[i] < dmin) dmin = deg[i]; if (deg[i] > dmax) dmax = deg[i]; }
  /* 2-colouring */
  int *col = malloc(n * sizeof(int)), *queue = malloc(n * sizeof(int)); int bip = 1, comps = 0;
  for (int i = 0; i < n; i++) col[i] = -1;
  for (int s = 0; s < n; s++) if (col[s] < 0) {
    comps++; int h = 0, t = 0; queue[t++] = s; col[s] = 0;
    while (h < t) { int x = queue[h++]; for (long k = off[x]; k < off[x + 1]; k++) { int y = adj[k];
      if (col[y] < 0) { col[y] = 1 - col[x]; queue[t++] = y; } else if (col[y] == col[x]) bip = 0; } }
  }
  int D = argc > 1 ? atoi(argv[1]) : 1 << 30; int list = argc > 2;
  int diam = 0; long far = 0, nA = 0;
  for (int i = 0; i < n; i++) nA += col[i] == 0;
  #pragma omp parallel
  {
    int *dist = malloc(n * sizeof(int)), *qu = malloc(n * sizeof(int)); int ldiam = 0; long lfar = 0;
    #pragma omp for schedule(dynamic, 16)
    for (int s = 0; s < n; s++) {
      for (int i = 0; i < n; i++) dist[i] = -1;
      int h = 0, t = 0; qu[t++] = s; dist[s] = 0;
      while (h < t) { int x = qu[h++]; for (long k = off[x]; k < off[x + 1]; k++) { int y = adj[k];
        if (dist[y] < 0) { dist[y] = dist[x] + 1; qu[t++] = y; } } }
      if (t < n) ldiam = 1 << 30;
      for (int i = 0; i < t; i++) { int d = dist[qu[i]]; if (d > ldiam) ldiam = d; if (d > D) lfar++;
        if (d > D && list && s < qu[i]) {
          #pragma omp critical
          fprintf(stderr, "%d %d\n", s, qu[i]);
        } }
    }
    #pragma omp critical
    { if (ldiam > diam) diam = ldiam; far += lfar; }
    free(dist); free(qu);
  }
  printf("n=%d edges=%ld multi=%ld components=%d bipartite=%s sides=%ld+%ld degree min=%d max=%d diameter=%d",
         n, m, multi, comps, bip ? "yes" : "no", nA, n - nA, dmin, dmax, diam);
  if (argc > 1) printf(" ordered_pairs_beyond_%d=%ld", D, far);
  printf("\n");
  return 0;
}
