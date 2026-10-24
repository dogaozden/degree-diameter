/* liftdiam.c -- diameter of a regular voltage lift (abelian group Z_M1 x Z_M2), multi-source bitset BFS.
 *
 * Input (stdin or file): first line "NB M1 M2 E", then E lines "u v a b": base edge u-v whose dart u->v
 * carries voltage (a,b) in Z_M1 x Z_M2 (dart v->u carries the negative).  Parallel edges allowed.
 * Lift vertex (v,g), g=(g1,g2) indexed v*M + g1*M2 + g2 (M = M1*M2); (u,g) ~ (v, g+volt(u->v)).
 * The group acts by translation, so BFS from (v,0) for every base vertex v gives the exact diameter.
 *
 * Usage: liftdiam file D [threads] [src_step]
 *   D: report for each source the number of lift vertices not reached within D steps; prints total
 *      unreached (source,target) pairs, max eccentricity (capped at 4D), degree range, bipartiteness.
 *   src_step: only use base sources v with v % src_step == 0 (sampling; default 1 = all).
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <pthread.h>

static int NB, M1, M2, M, E;
static int *adjstart, *adjv, *adja, *adjb; /* base adjacency with dart voltages */
static int D, NT = 1, STEP = 1;
static long long V;
static long long tot_unreached = 0; static int max_ecc = 0; static int ecc_capped = 0;
static long long *unr_by_src;
static pthread_mutex_t mu = PTHREAD_MUTEX_INITIALIZER;
static int next_batch = 0, nbatches;
static int *srcs; static int nsrc;

static void *worker(void *arg) {
  (void)arg;
  uint64_t *vis = malloc(sizeof(uint64_t) * V), *fr = malloc(sizeof(uint64_t) * V), *nx = malloc(sizeof(uint64_t) * V);
  if (!vis || !fr || !nx) { fprintf(stderr, "oom\n"); exit(1); }
  for (;;) {
    pthread_mutex_lock(&mu); int b = next_batch++; pthread_mutex_unlock(&mu);
    if (b >= nbatches) break;
    int s0 = b * 64, s1 = s0 + 64; if (s1 > nsrc) s1 = nsrc;
    int nb = s1 - s0; uint64_t full = (nb == 64) ? ~0ULL : ((1ULL << nb) - 1);
    memset(vis, 0, sizeof(uint64_t) * V); memset(fr, 0, sizeof(uint64_t) * V);
    for (int i = 0; i < nb; i++) { long long w = (long long)srcs[s0 + i] * M; fr[w] |= 1ULL << i; vis[w] |= 1ULL << i; }
    long long unr_at_D = -1; int level = 0; int ecc_local = 0;
    long long reached_count_bits = nb; long long need = (long long)nb * V;
    long long unr_src[64]; memset(unr_src, 0, sizeof(unr_src));
    while (1) {
      if (level == D) {
        /* count unreached per source */
        long long u = 0;
        for (long long w = 0; w < V; w++) { uint64_t m = (~vis[w]) & full; if (m) { u += __builtin_popcountll(m); while (m) { int i = __builtin_ctzll(m); unr_src[i]++; m &= m - 1; } } }
        unr_at_D = u;
        if (u == 0) { ecc_local = D; break; }
      }
      if (reached_count_bits == need) { ecc_local = level; break; }
      if (level >= 4 * D) { ecc_local = -1; break; }
      /* pull step */
      long long newbits = 0;
      for (int v = 0; v < NB; v++) {
        uint64_t *nxv = nx + (long long)v * M;
        memset(nxv, 0, sizeof(uint64_t) * M);
        for (int e = adjstart[v]; e < adjstart[v + 1]; e++) {
          int u = adjv[e], a = adja[e], bb = adjb[e];
          uint64_t *fru = fr + (long long)u * M;
          for (int g1 = 0; g1 < M1; g1++) {
            int h1 = g1 + a; if (h1 >= M1) h1 -= M1;
            uint64_t *dst = nxv + g1 * M2; uint64_t *src = fru + h1 * M2;
            int k = M2 - bb; /* g2 in [0,k) maps to g2+bb ; g2 in [k,M2) maps to g2+bb-M2 */
            for (int g2 = 0; g2 < k; g2++) dst[g2] |= src[g2 + bb];
            for (int g2 = k; g2 < M2; g2++) dst[g2] |= src[g2 + bb - M2];
          }
        }
        uint64_t *visv = vis + (long long)v * M;
        for (int g = 0; g < M; g++) { uint64_t m = nxv[g] & ~visv[g]; nxv[g] = m; visv[g] |= m; newbits += __builtin_popcountll(m); }
      }
      uint64_t *t = fr; fr = nx; nx = t;
      level++;
      reached_count_bits += newbits;
      if (newbits == 0) { /* stalled before level D (disconnected lift): every unvisited vertex is unreached */
        if (unr_at_D < 0) {
          long long u = 0;
          for (long long w = 0; w < V; w++) { uint64_t m = (~vis[w]) & full; if (m) { u += __builtin_popcountll(m); while (m) { int i = __builtin_ctzll(m); unr_src[i]++; m &= m - 1; } } }
          unr_at_D = u;
        }
        ecc_local = -2; break;
      } /* fix found by squad card r1-d8/c1 */
    }
    if (unr_at_D < 0) unr_at_D = 0; /* finished before D */
    pthread_mutex_lock(&mu);
    tot_unreached += unr_at_D;
    for (int i = 0; i < nb; i++) unr_by_src[s0 + i] = unr_src[i];
    if (ecc_local < 0) ecc_capped = 1; else if (ecc_local > max_ecc) max_ecc = ecc_local;
    pthread_mutex_unlock(&mu);
  }
  free(vis); free(fr); free(nx);
  return NULL;
}

int main(int argc, char **argv) {
  if (argc < 3) { fprintf(stderr, "usage: liftdiam file D [threads] [src_step]\n"); return 1; }
  FILE *f = strcmp(argv[1], "-") ? fopen(argv[1], "r") : stdin;
  if (!f) { perror("open"); return 1; }
  D = atoi(argv[2]); if (argc > 3) NT = atoi(argv[3]); if (argc > 4) STEP = atoi(argv[4]);
  if (fscanf(f, "%d %d %d %d", &NB, &M1, &M2, &E) != 4) { fprintf(stderr, "bad header\n"); return 1; }
  M = M1 * M2; V = (long long)NB * M;
  int *eu = malloc(sizeof(int) * E), *ev = malloc(sizeof(int) * E), *ea = malloc(sizeof(int) * E), *eb = malloc(sizeof(int) * E);
  int *deg = calloc(NB, sizeof(int));
  for (int i = 0; i < E; i++) {
    if (fscanf(f, "%d %d %d %d", &eu[i], &ev[i], &ea[i], &eb[i]) != 4) { fprintf(stderr, "bad edge %d\n", i); return 1; }
    ea[i] = ((ea[i] % M1) + M1) % M1; eb[i] = ((eb[i] % M2) + M2) % M2;
    deg[eu[i]]++; deg[ev[i]]++;
  }
  adjstart = malloc(sizeof(int) * (NB + 1)); adjstart[0] = 0;
  for (int v = 0; v < NB; v++) adjstart[v + 1] = adjstart[v] + deg[v];
  adjv = malloc(sizeof(int) * 2 * E); adja = malloc(sizeof(int) * 2 * E); adjb = malloc(sizeof(int) * 2 * E);
  int *fill = calloc(NB, sizeof(int));
  /* pull formulation: for target lift vertex (v,g), neighbour (u, g + volt(v->u)) */
  for (int i = 0; i < E; i++) {
    int u = eu[i], v = ev[i];
    int p = adjstart[u] + fill[u]++; adjv[p] = v; adja[p] = ea[i]; adjb[p] = eb[i];            /* dart u->v */
    p = adjstart[v] + fill[v]++; adjv[p] = u; adja[p] = (M1 - ea[i]) % M1; adjb[p] = (M2 - eb[i]) % M2; /* dart v->u */
  }
  /* bipartiteness of base (lift of bipartite base is bipartite) */
  int *col = malloc(sizeof(int) * NB); for (int v = 0; v < NB; v++) col[v] = -1;
  int bip = 1; int *stack = malloc(sizeof(int) * NB);
  for (int s = 0; s < NB; s++) if (col[s] < 0) {
    int sp = 0; stack[sp++] = s; col[s] = 0;
    while (sp) { int v = stack[--sp]; for (int e = adjstart[v]; e < adjstart[v + 1]; e++) { int u = adjv[e]; if (col[u] < 0) { col[u] = 1 - col[v]; stack[sp++] = u; } else if (col[u] == col[v]) bip = 0; } }
  }
  /* lift degree = base degree, but parallel darts with equal voltage give multi-edges: check */
  int multi = 0;
  for (int v = 0; v < NB; v++) for (int e = adjstart[v]; e < adjstart[v + 1]; e++) for (int e2 = e + 1; e2 < adjstart[v + 1]; e2++)
    if (adjv[e] == adjv[e2] && adja[e] == adja[e2] && adjb[e] == adjb[e2]) multi++;
  int dmin = 1 << 30, dmax = 0; for (int v = 0; v < NB; v++) { if (deg[v] < dmin) dmin = deg[v]; if (deg[v] > dmax) dmax = deg[v]; }
  nsrc = 0; srcs = malloc(sizeof(int) * NB); for (int v = 0; v < NB; v += STEP) srcs[nsrc++] = v;
  nbatches = (nsrc + 63) / 64; unr_by_src = calloc(nsrc, sizeof(long long));
  pthread_t th[64]; for (int t = 0; t < NT; t++) pthread_create(&th[t], NULL, worker, NULL);
  for (int t = 0; t < NT; t++) pthread_join(th[t], NULL);
  int worst = 0; for (int i = 0; i < nsrc; i++) if (unr_by_src[i] > unr_by_src[worst]) worst = i;
  printf("lift_vertices %lld base %d group %dx%d degree %d..%d bipartite %d multi_edges %d sources %d\n", V, NB, M1, M2, dmin, dmax, bip, multi, nsrc);
  printf("D %d unreached_pairs %lld max_ecc %d%s worst_src %d (%lld)\n", D, tot_unreached, max_ecc, ecc_capped ? " (some >4D or disconnected)" : "", srcs[worst], unr_by_src[worst]);
  return 0;
}
