/* nbwalk.c -- for a voltage lift X (liftdiam input format, group Z_M1 x Z_M2), count for every edge xy of X the
 * non-backtracking walks of length <= L (default 7) from x to y.  A further lift of X by a group of order f has
 * diameter <= L + 1 only if every edge of X carries at least f such walks (a walk between the two ends of an edge
 * has odd length in a bipartite graph, and backtracking does not change the voltage), so min_w bounds f.
 * Sources: (v,0) for every base vertex v (the group acts transitively on each fibre).
 * usage: nbwalk file [L] [src_step]   (src_step > 1: sample every src_step-th base vertex as source) */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int NB, M1, M2, M, E, L = 7;
static int *st, *nbv, *nba, *nbb;
static long long *cnt; /* per target lift vertex: walks of length <= L ending there (odd lengths) */

static void dfs(long long w, int prev_dart_rev, int depth) {
  /* w = lift vertex; prev_dart_rev = index (in the adjacency of the current base vertex) that would backtrack */
  if (depth & 1) cnt[w]++;
  if (depth == L) return;
  int v = (int)(w / M), g = (int)(w % M), g1 = g / M2, g2 = g % M2;
  for (int e = st[v]; e < st[v + 1]; e++) {
    if (e == prev_dart_rev) continue;
    int u = nbv[e]; int h1 = g1 + nba[e]; if (h1 >= M1) h1 -= M1; int h2 = g2 + nbb[e]; if (h2 >= M2) h2 -= M2;
    /* find the reverse dart of e at u: same base edge, opposite voltage */
    int rev = -1;
    for (int r = st[u]; r < st[u + 1]; r++)
      if (nbv[r] == v && nba[r] == (M1 - nba[e]) % M1 && nbb[r] == (M2 - nbb[e]) % M2) { rev = r; break; }
    dfs((long long)u * M + h1 * M2 + h2, rev, depth + 1);
  }
}

int main(int argc, char **argv) {
  if (argc < 2) { fprintf(stderr, "usage: nbwalk file [L] [src_step]\n"); return 1; }
  if (argc > 2) L = atoi(argv[2]);
  int step = argc > 3 ? atoi(argv[3]) : 1;
  FILE *f = fopen(argv[1], "r");
  if (!f || fscanf(f, "%d %d %d %d", &NB, &M1, &M2, &E) != 4) { fprintf(stderr, "bad file\n"); return 1; }
  M = M1 * M2;
  int *eu = malloc(sizeof(int) * E), *ev = malloc(sizeof(int) * E), *ea = malloc(sizeof(int) * E), *eb = malloc(sizeof(int) * E), *deg = calloc(NB, sizeof(int));
  for (int i = 0; i < E; i++) {
    if (fscanf(f, "%d %d %d %d", &eu[i], &ev[i], &ea[i], &eb[i]) != 4) { fprintf(stderr, "short\n"); return 1; }
    ea[i] = ((ea[i] % M1) + M1) % M1; eb[i] = ((eb[i] % M2) + M2) % M2; deg[eu[i]]++; deg[ev[i]]++;
  }
  st = malloc(sizeof(int) * (NB + 1)); st[0] = 0; for (int v = 0; v < NB; v++) st[v + 1] = st[v] + deg[v];
  nbv = malloc(sizeof(int) * 2 * E); nba = malloc(sizeof(int) * 2 * E); nbb = malloc(sizeof(int) * 2 * E); int *fill = calloc(NB, sizeof(int));
  for (int i = 0; i < E; i++) {
    int p = st[eu[i]] + fill[eu[i]]++; nbv[p] = ev[i]; nba[p] = ea[i]; nbb[p] = eb[i];
    p = st[ev[i]] + fill[ev[i]]++; nbv[p] = eu[i]; nba[p] = (M1 - ea[i]) % M1; nbb[p] = (M2 - eb[i]) % M2;
  }
  long long V = (long long)NB * M; cnt = calloc(V, sizeof(long long));
  long long hist[17] = {0}, minw = -1, nedges = 0; double sumw = 0;
  for (int v = 0; v < NB; v += step) {
    long long s = (long long)v * M;
    /* collect the neighbour lift vertices of s, reset their counters, run the DFS, read them */
    for (int e = st[v]; e < st[v + 1]; e++) cnt[(long long)nbv[e] * M + nba[e] * M2 + nbb[e]] = 0;
    dfs(s, -1, 0);
    for (int e = st[v]; e < st[v + 1]; e++) {
      long long t = (long long)nbv[e] * M + nba[e] * M2 + nbb[e];
      long long c = cnt[t]; /* parallel darts to the same lift vertex share t; fine for a minimum */
      nedges++; sumw += c; hist[c > 16 ? 16 : c]++;
      if (minw < 0 || c < minw) minw = c;
    }
    for (int e = st[v]; e < st[v + 1]; e++) cnt[(long long)nbv[e] * M + nba[e] * M2 + nbb[e]] = 0;
    /* the DFS also touched other vertices; clear them lazily by a full reset every source (V is small) */
    memset(cnt, 0, sizeof(long long) * V);
  }
  printf("darts %lld  min_w %lld  mean_w %.2f  hist w=1..15,>=16:", nedges, minw, sumw / nedges);
  for (int c = 1; c <= 16; c++) printf(" %lld", hist[c]);
  printf("\n");
  return 0;
}
