/* liftw.c -- weighted unreached pairs at depth D for a Z_M1 x Z_M2 voltage lift (c4 card).
 * usage: liftw base D srcfile
 *   base: "NB M1 M2 E" then E lines "u v a b" (dart u->v voltage (a,b); same format as liftdiam).
 *   srcfile: "ns" then ns lines "v w": lift vertex (v,0) is a source with weight w.
 * prints "WUNR <sum_i w_i*unreached_i> UNR_MAX <max_i unreached_i> NSRC <ns>".
 * Sources are batched 64 at a time in bitsets; BFS stops at depth D.
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

int main(int argc, char **argv) {
  if (argc < 4) { fprintf(stderr, "usage: liftw base D srcfile\n"); return 1; }
  FILE *f = fopen(argv[1], "r"); if (!f) { perror("base"); return 1; }
  int D = atoi(argv[2]);
  int NB, M1, M2, E;
  if (fscanf(f, "%d %d %d %d", &NB, &M1, &M2, &E) != 4) { fprintf(stderr, "bad header\n"); return 1; }
  int M = M1 * M2; long long V = (long long)NB * M;
  int *eu = malloc(sizeof(int) * E), *ev = malloc(sizeof(int) * E), *ea = malloc(sizeof(int) * E), *eb = malloc(sizeof(int) * E);
  int *deg = calloc(NB, sizeof(int));
  for (int i = 0; i < E; i++) {
    if (fscanf(f, "%d %d %d %d", &eu[i], &ev[i], &ea[i], &eb[i]) != 4) { fprintf(stderr, "bad edge\n"); return 1; }
    ea[i] = ((ea[i] % M1) + M1) % M1; eb[i] = ((eb[i] % M2) + M2) % M2;
    deg[eu[i]]++; deg[ev[i]]++;
  }
  fclose(f);
  int *adjstart = malloc(sizeof(int) * (NB + 1)); adjstart[0] = 0;
  for (int v = 0; v < NB; v++) adjstart[v + 1] = adjstart[v] + deg[v];
  int *adjv = malloc(sizeof(int) * 2 * E), *adja = malloc(sizeof(int) * 2 * E), *adjb = malloc(sizeof(int) * 2 * E);
  int *fill = calloc(NB, sizeof(int));
  for (int i = 0; i < E; i++) {
    int u = eu[i], v = ev[i];
    int p = adjstart[u] + fill[u]++; adjv[p] = v; adja[p] = ea[i]; adjb[p] = eb[i];
    p = adjstart[v] + fill[v]++; adjv[p] = u; adja[p] = (M1 - ea[i]) % M1; adjb[p] = (M2 - eb[i]) % M2;
  }
  FILE *sf = fopen(argv[3], "r"); if (!sf) { perror("src"); return 1; }
  int ns; if (fscanf(sf, "%d", &ns) != 1) { fprintf(stderr, "bad srcfile\n"); return 1; }
  int *sv = malloc(sizeof(int) * ns); long long *sw = malloc(sizeof(long long) * ns);
  for (int i = 0; i < ns; i++) if (fscanf(sf, "%d %lld", &sv[i], &sw[i]) != 2) { fprintf(stderr, "bad src line\n"); return 1; }
  fclose(sf);

  uint64_t *vis = malloc(sizeof(uint64_t) * V), *fr = malloc(sizeof(uint64_t) * V), *nx = malloc(sizeof(uint64_t) * V);
  if (!vis || !fr || !nx) { fprintf(stderr, "oom\n"); return 1; }
  long long total = 0, umax = 0;
  for (int s0 = 0; s0 < ns; s0 += 64) {
    int nb = ns - s0 < 64 ? ns - s0 : 64;
    uint64_t full = (nb == 64) ? ~0ULL : ((1ULL << nb) - 1);
    memset(vis, 0, sizeof(uint64_t) * V); memset(fr, 0, sizeof(uint64_t) * V);
    for (int i = 0; i < nb; i++) { long long w = (long long)sv[s0 + i] * M; fr[w] |= 1ULL << i; vis[w] |= 1ULL << i; }
    for (int level = 0; level < D; level++) {
      int any = 0;
      for (int v = 0; v < NB; v++) {
        uint64_t *nxv = nx + (long long)v * M;
        memset(nxv, 0, sizeof(uint64_t) * M);
        for (int e = adjstart[v]; e < adjstart[v + 1]; e++) {
          int u = adjv[e], a = adja[e], bb = adjb[e];
          uint64_t *fru = fr + (long long)u * M;
          for (int g1 = 0; g1 < M1; g1++) {
            int h1 = g1 + a; if (h1 >= M1) h1 -= M1;
            uint64_t *dst = nxv + g1 * M2; uint64_t *src = fru + h1 * M2;
            int k = M2 - bb;
            for (int g2 = 0; g2 < k; g2++) dst[g2] |= src[g2 + bb];
            for (int g2 = k; g2 < M2; g2++) dst[g2] |= src[g2 + bb - M2];
          }
        }
        uint64_t *visv = vis + (long long)v * M;
        for (int g = 0; g < M; g++) { uint64_t m = nxv[g] & ~visv[g]; nxv[g] = m; visv[g] |= m; if (m) any = 1; }
      }
      uint64_t *t = fr; fr = nx; nx = t;
      if (!any) break;
    }
    long long unr[64]; memset(unr, 0, sizeof unr);
    for (long long w = 0; w < V; w++) { uint64_t m = (~vis[w]) & full; while (m) { int i = __builtin_ctzll(m); unr[i]++; m &= m - 1; } }
    for (int i = 0; i < nb; i++) { total += sw[s0 + i] * unr[i]; if (unr[i] > umax) umax = unr[i]; }
  }
  printf("WUNR %lld UNR_MAX %lld NSRC %d\n", total, umax, ns);
  free(vis); free(fr); free(nx);
  return 0;
}
