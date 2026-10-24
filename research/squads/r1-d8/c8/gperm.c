/* gperm.c -- diameter check of a permutation-voltage lift of a base graph (exact, bitset multi-source BFS).
 *
 * Input file: first line "NB M E", then E records "u v p_0 ... p_{M-1}": the dart u->v carries the level
 * permutation i -> p_i, i.e. lift vertex (u,i) ~ (v,p_i). The dart v->u carries the inverse. Parallel darts allowed.
 * Lift vertices are indexed v*M + i.
 *
 * Usage: gperm file D mode step
 *   mode 0: BFS from every lift vertex (exact for arbitrary permutation voltages; NB*M sources)
 *   mode 1: BFS from (v,0) for every base vertex v (exact only when the voltages are right translations of a
 *           group G acting regularly on the levels: then left translations are automorphisms and each fibre is
 *           one orbit). Mode 1 is what the group lifts in gperm_lifts.py use.
 *   step  : keep every step-th source (sampling). The reported unreached count is then a LOWER bound.
 * Output: unreached_pairs (sum over sources of lift vertices not reached within D steps), max_ecc.
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

static int NB, M, E;
static int *adjstart, *adjv, *cmap; /* pull at v from neighbour adjv[e]: (v,j) <- (u, cmap[e*M+j]) */

int main(int argc, char **argv) {
  if (argc < 5) { fprintf(stderr, "usage: gperm file D mode step\n"); return 1; }
  FILE *f = strcmp(argv[1], "-") ? fopen(argv[1], "r") : stdin;
  if (!f) { perror("open"); return 1; }
  int D = atoi(argv[2]), mode = atoi(argv[3]), step = atoi(argv[4]);
  if (step < 1) step = 1;
  if (fscanf(f, "%d %d %d", &NB, &M, &E) != 3) { fprintf(stderr, "bad header\n"); return 1; }
  int *eu = malloc(sizeof(int) * E), *ev = malloc(sizeof(int) * E);
  int *perm = malloc(sizeof(int) * (size_t)E * M);
  int *deg = calloc(NB, sizeof(int));
  for (int e = 0; e < E; e++) {
    if (fscanf(f, "%d %d", &eu[e], &ev[e]) != 2) { fprintf(stderr, "bad edge %d\n", e); return 1; }
    deg[eu[e]]++; deg[ev[e]]++;
    int *p = perm + (size_t)e * M;
    for (int i = 0; i < M; i++) if (fscanf(f, "%d", &p[i]) != 1) { fprintf(stderr, "bad perm %d\n", e); return 1; }
    unsigned char *seen = calloc(M, 1);
    for (int i = 0; i < M; i++) { if (p[i] < 0 || p[i] >= M || seen[p[i]]) { fprintf(stderr, "not a permutation (edge %d)\n", e); return 1; } seen[p[i]] = 1; }
    free(seen);
  }
  fclose(f);
  adjstart = malloc(sizeof(int) * (NB + 1)); adjstart[0] = 0;
  for (int v = 0; v < NB; v++) adjstart[v + 1] = adjstart[v] + deg[v];
  adjv = malloc(sizeof(int) * 2 * E);
  cmap = malloc(sizeof(int) * (size_t)2 * E * M);
  int *fill = calloc(NB, sizeof(int));
  for (int e = 0; e < E; e++) {
    int u = eu[e], v = ev[e];
    int *p = perm + (size_t)e * M;
    int pos = adjstart[u] + fill[u]++;               /* at u: (u,i) <- (v, p_i) */
    adjv[pos] = v; memcpy(cmap + (size_t)pos * M, p, sizeof(int) * M);
    pos = adjstart[v] + fill[v]++;                   /* at v: (v,j) <- (u, pinv_j) */
    adjv[pos] = u; int *c = cmap + (size_t)pos * M;
    for (int i = 0; i < M; i++) c[p[i]] = i;
  }
  long long V = (long long)NB * M;
  /* sources */
  long long *src = malloc(sizeof(long long) * V); long long nsrc = 0; long long cnt = 0;
  if (mode == 0) { for (long long w = 0; w < V; w++) { if (cnt++ % step == 0) src[nsrc++] = w; } }
  else { for (int v = 0; v < NB; v++) { if (cnt++ % step == 0) src[nsrc++] = (long long)v * M; } }
  uint64_t *vis = malloc(8 * V), *fr = malloc(8 * V), *nx = malloc(8 * V);
  if (!vis || !fr || !nx) { fprintf(stderr, "oom\n"); return 1; }
  long long tot_unr = 0; int max_ecc = 0, capped = 0;
  for (long long b0 = 0; b0 < nsrc; b0 += 64) {
    int nb = (int)((nsrc - b0 < 64) ? (nsrc - b0) : 64);
    uint64_t full = (nb == 64) ? ~0ULL : ((1ULL << nb) - 1);
    memset(vis, 0, 8 * V); memset(fr, 0, 8 * V);
    for (int i = 0; i < nb; i++) { long long w = src[b0 + i]; fr[w] |= 1ULL << i; vis[w] |= 1ULL << i; }
    long long reached = nb, need = (long long)nb * V, unr_at_D = -1;
    int level = 0, ecc = -1;
    while (1) {
      if (level == D) {
        long long u = 0;
        for (long long w = 0; w < V; w++) { uint64_t m = (~vis[w]) & full; if (m) u += __builtin_popcountll(m); }
        unr_at_D = u; if (u == 0) ecc = D; break;
      }
      if (reached == need) { ecc = level; break; }
      if (level >= 4 * D) { capped = 1; break; }
      long long newbits = 0;
      for (int v = 0; v < NB; v++) {
        uint64_t *nxv = nx + (long long)v * M;
        memset(nxv, 0, 8 * (size_t)M);
        for (int e = adjstart[v]; e < adjstart[v + 1]; e++) {
          const uint64_t *fru = fr + (long long)adjv[e] * M; const int *c = cmap + (size_t)e * M;
          for (int j = 0; j < M; j++) nxv[j] |= fru[c[j]];
        }
        uint64_t *visv = vis + (long long)v * M;
        for (int j = 0; j < M; j++) { uint64_t m = nxv[j] & ~visv[j]; nxv[j] = m; visv[j] |= m; newbits += __builtin_popcountll(m); }
      }
      uint64_t *t = fr; fr = nx; nx = t;
      level++; reached += newbits;
      if (newbits == 0 && reached < need) { capped = 1; break; } /* disconnected */
    }
    if (unr_at_D < 0) unr_at_D = need - reached;
    tot_unr += unr_at_D;
    if (ecc > max_ecc) max_ecc = ecc;
  }
  printf("lift_vertices %lld base %d levels %d sources %lld mode %d step %d\n", V, NB, M, nsrc, mode, step);
  printf("D %d unreached_pairs %lld max_ecc %d%s\n", D, tot_unr, max_ecc, capped ? " (some disconnected or >4D)" : "");
  return 0;
}
