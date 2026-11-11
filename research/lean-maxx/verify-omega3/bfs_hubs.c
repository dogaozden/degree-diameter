// BFS from every hub (vertices >= base); count (hub, vertex) pairs at distance >= 9 or unreachable,
// and the maximum finite distance seen.  Usage: bfs_hubs file.edges
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int main(int argc, char **argv) {
  FILE *f = fopen(argv[1], "r"); long V, E, base;
  if (fscanf(f, "%ld %ld %ld", &V, &E, &base) != 3) return 1;
  int *eu = malloc(E*sizeof(int)), *ev = malloc(E*sizeof(int));
  long *deg = calloc(V+1, sizeof(long));
  for (long i = 0; i < E; i++) { if (fscanf(f, "%d %d", &eu[i], &ev[i]) != 2) return 1; deg[eu[i]]++; deg[ev[i]]++; }
  long *off = calloc(V+2, sizeof(long));
  for (long i = 0; i < V; i++) off[i+1] = off[i] + deg[i];
  int *adj = malloc(2*E*sizeof(int)); long *pos = calloc(V, sizeof(long));
  for (long i = 0; i < E; i++) { adj[off[eu[i]] + pos[eu[i]]++] = ev[i]; adj[off[ev[i]] + pos[ev[i]]++] = eu[i]; }
  int *d = malloc(V*sizeof(int)), *q = malloc(V*sizeof(int));
  long far = 0, farHubMin = -1, farHubMax = -1; int maxd = 0; long unreach = 0;
  for (long s = base; s < V; s++) {
    memset(d, -1, V*sizeof(int)); long h = 0, t = 0; q[t++] = s; d[s] = 0;
    while (h < t) { int u = q[h++]; for (long j = off[u]; j < off[u+1]; j++) { int v = adj[j]; if (d[v] < 0) { d[v] = d[u]+1; q[t++] = v; } } }
    long fh = V - t;   // unreachable
    unreach += fh;
    for (long i = 0; i < t; i++) { if (d[q[i]] > maxd) maxd = d[q[i]]; if (d[q[i]] >= 9) fh++; }
    far += fh;
    if (farHubMin < 0 || fh < farHubMin) farHubMin = fh;
    if (fh > farHubMax) farHubMax = fh;
  }
  printf("hubs=%ld  far pairs (dist>=9 or unreachable, source a hub) = %ld  per-hub min/max = %ld/%ld  max finite dist = %d  unreachable = %ld\n",
         V - base, far, farHubMin, farHubMax, maxd, unreach);
  return 0;
}
