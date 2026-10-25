/* verify.c -- independent check of a Z_M voltage lift (liftdiam format "NB M 1 E", then "u v a b" per base edge).
 * Builds the explicit lift graph (vertex v*M+g; base edge u-v with voltage a gives (u,g)-(v,(g+a) mod M)),
 * checks it is simple and regular, and runs a plain BFS from every base vertex (v,0). The group Z_M acts by
 * translation, so these BFS trees give the eccentricities of all lift vertices.
 * usage: verify file [D]   (default D = 8). Prints degree range, multi/loop count, connectivity, diameter,
 * and the number of lift vertices at distance > D from each base source (summed).
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

int main(int argc, char **argv) {
  if (argc < 2) { fprintf(stderr, "usage: verify file [D]\n"); return 1; }
  int D = argc > 2 ? atoi(argv[2]) : 8;
  FILE *f = fopen(argv[1], "r");
  if (!f) { perror("open"); return 1; }
  int NB, M1, M2, E;
  if (fscanf(f, "%d %d %d %d", &NB, &M1, &M2, &E) != 4) { fprintf(stderr, "bad header\n"); return 1; }
  if (M2 != 1) { fprintf(stderr, "this checker expects M2 = 1\n"); return 1; }
  int M = M1;
  long long V = (long long)NB * M;
  int *eu = malloc(sizeof(int) * E), *ev = malloc(sizeof(int) * E), *ea = malloc(sizeof(int) * E);
  for (int i = 0; i < E; i++) {
    int b;
    if (fscanf(f, "%d %d %d %d", &eu[i], &ev[i], &ea[i], &b) != 4) { fprintf(stderr, "bad edge %d\n", i); return 1; }
    ea[i] = ((ea[i] % M) + M) % M;
    if (eu[i] < 0 || eu[i] >= NB || ev[i] < 0 || ev[i] >= NB) { fprintf(stderr, "vertex out of range at edge %d\n", i); return 1; }
  }
  fclose(f);
  /* explicit lift adjacency: each lift vertex gets one entry per incident base edge (degree of base vertex) */
  int *deg = calloc(V, sizeof(int));
  for (int i = 0; i < E; i++) for (int g = 0; g < M; g++) { deg[(long long)eu[i] * M + g]++; deg[(long long)ev[i] * M + g]++; }
  int dmin = 1 << 30, dmax = 0;
  for (long long x = 0; x < V; x++) { if (deg[x] < dmin) dmin = deg[x]; if (deg[x] > dmax) dmax = deg[x]; }
  long long *start = malloc(sizeof(long long) * (V + 1)); start[0] = 0;
  for (long long x = 0; x < V; x++) start[x + 1] = start[x] + deg[x];
  int *adj = malloc(sizeof(int) * start[V]); long long *fill = calloc(V, sizeof(long long));
  for (int i = 0; i < E; i++) for (int g = 0; g < M; g++) {
    long long x = (long long)eu[i] * M + g, y = (long long)ev[i] * M + (g + ea[i]) % M;
    adj[start[x] + fill[x]++] = (int)y; adj[start[y] + fill[y]++] = (int)x;
  }
  /* simple-graph check: loops and repeated neighbours */
  long long loops = 0, multi = 0;
  for (long long x = 0; x < V; x++) {
    for (long long a = start[x]; a < start[x + 1]; a++) {
      if (adj[a] == x) loops++;
      for (long long b = a + 1; b < start[x + 1]; b++) if (adj[a] == adj[b]) multi++;
    }
  }
  /* BFS from every base vertex (v,0) */
  int *dist = malloc(sizeof(int) * V), *q = malloc(sizeof(int) * V);
  int diam = 0; long long unreached_total = 0; int connected = 1;
  for (int v = 0; v < NB; v++) {
    for (long long x = 0; x < V; x++) dist[x] = -1;
    long long src = (long long)v * M; int qh = 0, qt = 0;
    dist[src] = 0; q[qt++] = (int)src;
    while (qh < qt) {
      int x = q[qh++];
      for (long long a = start[x]; a < start[x + 1]; a++) {
        int y = adj[a];
        if (dist[y] < 0) { dist[y] = dist[x] + 1; q[qt++] = y; }
      }
    }
    if (qt != V) connected = 0;
    for (long long x = 0; x < V; x++) {
      if (dist[x] < 0) unreached_total++;
      else if (dist[x] > diam) diam = dist[x];
      if (dist[x] < 0 || dist[x] > D) { /* counted in unreached_total only if beyond D */ }
    }
  }
  /* unreached_total above counts unreached-at-all; recount beyond-D pairs separately for the D report */
  long long beyond = 0;
  for (int v = 0; v < NB; v++) {
    for (long long x = 0; x < V; x++) dist[x] = -1;
    long long src = (long long)v * M; int qh = 0, qt = 0;
    dist[src] = 0; q[qt++] = (int)src;
    while (qh < qt) {
      int x = q[qh++];
      if (dist[x] >= D) continue;
      for (long long a = start[x]; a < start[x + 1]; a++) {
        int y = adj[a];
        if (dist[y] < 0) { dist[y] = dist[x] + 1; q[qt++] = y; }
      }
    }
    beyond += V - qt;
  }
  printf("lift_vertices %lld base %d group Z_%d degree %d..%d loops %lld repeated_neighbour_pairs %lld connected %d\n",
         V, NB, M, dmin, dmax, loops, multi, connected);
  printf("diameter %d  pairs_beyond_D%d %lld  (all-pairs unreached-if-disconnected %lld)\n", diam, D, beyond, unreached_total);
  printf("VERDICT %s\n", (dmin == dmax && dmin == 7 && loops == 0 && multi == 0 && connected && beyond == 0) ? "VALID" : "NOT_VALID");
  return 0;
}
