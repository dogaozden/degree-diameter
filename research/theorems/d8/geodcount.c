/* geodcount.c -- for a voltage lift (liftdiam input format, group Z_M1 x Z_M2), count shortest paths
 * from every base source (v,0) to every lift vertex; print, for each distance d, the number of
 * (source,target) pairs at distance d and the histogram of geodesic counts (capped at 64), plus the minimum.
 * A Z_f-lift of this lift has diameter <= diam + 1 only if every pair at distance diam has >= f geodesics
 * (when diam is odd and the lift is bipartite, the walks of length <= diam + 1 between such a pair are geodesics).
 * usage: geodcount file [src_step] */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

int main(int argc, char **argv) {
  if (argc < 2) { fprintf(stderr, "usage: geodcount file [src_step]\n"); return 1; }
  int step = argc > 2 ? atoi(argv[2]) : 1;
  FILE *f = fopen(argv[1], "r");
  int NB, M1, M2, E;
  if (!f || fscanf(f, "%d %d %d %d", &NB, &M1, &M2, &E) != 4) { fprintf(stderr, "bad file\n"); return 1; }
  int M = M1 * M2;
  int *eu = malloc(sizeof(int) * E), *ev = malloc(sizeof(int) * E), *ea = malloc(sizeof(int) * E), *eb = malloc(sizeof(int) * E);
  int *deg = calloc(NB, sizeof(int));
  for (int i = 0; i < E; i++) {
    if (fscanf(f, "%d %d %d %d", &eu[i], &ev[i], &ea[i], &eb[i]) != 4) { fprintf(stderr, "short file\n"); return 1; }
    ea[i] = ((ea[i] % M1) + M1) % M1; eb[i] = ((eb[i] % M2) + M2) % M2; deg[eu[i]]++; deg[ev[i]]++;
  }
  long long V = (long long)NB * M;
  int *st = malloc(sizeof(int) * (NB + 1)); st[0] = 0;
  for (int v = 0; v < NB; v++) st[v + 1] = st[v] + deg[v];
  int *nbv = malloc(sizeof(int) * 2 * E), *nba = malloc(sizeof(int) * 2 * E), *nbb = malloc(sizeof(int) * 2 * E), *fill = calloc(NB, sizeof(int));
  for (int i = 0; i < E; i++) {
    int p = st[eu[i]] + fill[eu[i]]++; nbv[p] = ev[i]; nba[p] = ea[i]; nbb[p] = eb[i];
    p = st[ev[i]] + fill[ev[i]]++; nbv[p] = eu[i]; nba[p] = (M1 - ea[i]) % M1; nbb[p] = (M2 - eb[i]) % M2;
  }
  int *dist = malloc(sizeof(int) * V); long long *cnt = malloc(sizeof(long long) * V); int *queue = malloc(sizeof(int) * V);
  static long long hist[64][65]; static long long npairs[64]; long long mincnt[64]; int maxd = 0;
  for (int d = 0; d < 64; d++) mincnt[d] = -1;
  for (int s = 0; s < NB; s += step) {
    for (long long w = 0; w < V; w++) { dist[w] = -1; cnt[w] = 0; }
    int h = 0, t = 0; long long s0 = (long long)s * M; dist[s0] = 0; cnt[s0] = 1; queue[t++] = (int)s0;
    while (h < t) {
      int w = queue[h++]; int v = w / M, g = w % M, g1 = g / M2, g2 = g % M2;
      for (int e = st[v]; e < st[v + 1]; e++) {
        int u = nbv[e]; int h1 = g1 + nba[e]; if (h1 >= M1) h1 -= M1; int h2 = g2 + nbb[e]; if (h2 >= M2) h2 -= M2;
        long long x = (long long)u * M + h1 * M2 + h2;
        if (dist[x] < 0) { dist[x] = dist[w] + 1; cnt[x] = cnt[w]; queue[t++] = (int)x; }
        else if (dist[x] == dist[w] + 1) cnt[x] += cnt[w];
      }
    }
    for (long long w = 0; w < V; w++) {
      int d = dist[w]; if (d < 0) { fprintf(stderr, "disconnected lift\n"); return 1; }
      if (d > maxd) maxd = d;
      long long c = cnt[w]; npairs[d]++; hist[d][c > 64 ? 64 : c]++;
      if (mincnt[d] < 0 || c < mincnt[d]) mincnt[d] = c;
    }
  }
  printf("lift %lld vertices, sources step %d, diameter %d\n", V, step, maxd);
  for (int d = 1; d <= maxd; d++) {
    printf("d %d pairs %lld min_geodesics %lld hist(1..8,>8):", d, npairs[d], mincnt[d]);
    long long big = 0; for (int c = 9; c <= 64; c++) big += hist[d][c];
    for (int c = 1; c <= 8; c++) printf(" %lld", hist[d][c]);
    printf(" | %lld\n", big);
  }
  return 0;
}
