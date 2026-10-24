/* lanneal.c -- simulated annealing of voltages (Z_M) on H(q) + j hop matchings, cost = number of (source,target)
 * lift pairs at distance > D (exact: multi-source bitset BFS from every base vertex; small q only).
 * usage: lanneal ghfile j M iters T0 seed [holo(0/1)] [D]
 *   holo=0: H(q) flags keep voltage 0 (sheet model), only hop labels move; holo=1: flags move too.
 * Moves: change one dart voltage; swap the hop targets of two points (same matching).
 * Writes best base to lanneal_best_q{q}_j{j}_M{M}.txt in liftdiam format. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>

static int q, N, J, M, D = 8, HOLO;
static int NB, E; static int *eu, *ev, *evol; /* base edges u->v voltage */
static int *adjstart, *adje; /* adjacency: for vertex v, list of edge ids */
static uint64_t rng_s = 88172645463325252ULL;
static inline uint64_t rnd(void) { rng_s ^= rng_s << 13; rng_s ^= rng_s >> 7; rng_s ^= rng_s << 17; return rng_s; }
static uint64_t *vis, *fr, *nx;
static int *S[4]; /* hop targets */
static int hopedge[4][1 << 20]; /* edge id of hop k at point p (p < 2^20) */

static void build_adj(void) {
  int *deg = calloc(NB, sizeof(int));
  for (int i = 0; i < E; i++) { deg[eu[i]]++; deg[ev[i]]++; }
  adjstart[0] = 0; for (int v = 0; v < NB; v++) adjstart[v + 1] = adjstart[v] + deg[v];
  int *fill = calloc(NB, sizeof(int));
  for (int i = 0; i < E; i++) { adje[adjstart[eu[i]] + fill[eu[i]]++] = i; adje[adjstart[ev[i]] + fill[ev[i]]++] = i; }
  free(deg); free(fill);
}

static long long cost(void) {
  long long V = (long long)NB * M, tot = 0;
  for (int s0 = 0; s0 < NB; s0 += 64) {
    int nb = NB - s0 < 64 ? NB - s0 : 64; uint64_t full = nb == 64 ? ~0ULL : ((1ULL << nb) - 1);
    memset(vis, 0, sizeof(uint64_t) * V); memset(fr, 0, sizeof(uint64_t) * V);
    for (int i = 0; i < nb; i++) { vis[(long long)(s0 + i) * M] |= 1ULL << i; fr[(long long)(s0 + i) * M] |= 1ULL << i; }
    for (int lev = 0; lev < D; lev++) {
      for (int v = 0; v < NB; v++) {
        uint64_t *nxv = nx + (long long)v * M; memset(nxv, 0, sizeof(uint64_t) * M);
        for (int a = adjstart[v]; a < adjstart[v + 1]; a++) {
          int e = adje[a]; int u, w; /* neighbour u, dart v->u voltage w */
          if (eu[e] == v) { u = ev[e]; w = evol[e]; } else { u = eu[e]; w = (M - evol[e]) % M; }
          uint64_t *fu = fr + (long long)u * M; int k = M - w;
          for (int g = 0; g < k; g++) nxv[g] |= fu[g + w];
          for (int g = k; g < M; g++) nxv[g] |= fu[g + w - M];
        }
        uint64_t *vv = vis + (long long)v * M; for (int g = 0; g < M; g++) { nxv[g] &= ~vv[g]; vv[g] |= nxv[g]; }
      }
      uint64_t *t = fr; fr = nx; nx = t;
    }
    for (long long w = 0; w < V; w++) tot += __builtin_popcountll(full & ~vis[w]);
  }
  return tot;
}

int main(int argc, char **argv) {
  if (argc < 7) { fprintf(stderr, "usage: lanneal ghfile j M iters T0 seed [holo] [D]\n"); return 1; }
  FILE *f = fopen(argv[1], "r"); J = atoi(argv[2]); M = atoi(argv[3]); long long iters = atoll(argv[4]);
  double T0 = atof(argv[5]); rng_s ^= (uint64_t)atoll(argv[6]) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 20; i++) rnd();
  HOLO = argc > 7 ? atoi(argv[7]) : 0; if (argc > 8) D = atoi(argv[8]);
  if (fscanf(f, "%d %d", &q, &N) != 2) return 1;
  NB = 2 * N; E = N * (q + 1) + J * N;
  eu = malloc(sizeof(int) * E); ev = malloc(sizeof(int) * E); evol = calloc(E, sizeof(int));
  int e = 0;
  for (int k = 0; k < N; k++) for (int i = 0; i <= q; i++) { int p; if (fscanf(f, "%d", &p) != 1) return 1; eu[e] = p; ev[e] = N + k; evol[e] = HOLO ? (int)(rnd() % M) : 0; e++; }
  int nflags = e;
  for (int k = 0; k < J; k++) {
    S[k] = malloc(sizeof(int) * N); for (int p = 0; p < N; p++) S[k][p] = p;
    for (int i = N - 1; i > 0; i--) { int r = rnd() % (i + 1); int t = S[k][i]; S[k][i] = S[k][r]; S[k][r] = t; }
    for (int p = 0; p < N; p++) { eu[e] = p; ev[e] = N + S[k][p]; evol[e] = 1 + rnd() % (M - 1); hopedge[k][p] = e; e++; }
  }
  adjstart = malloc(sizeof(int) * (NB + 1)); adje = malloc(sizeof(int) * 2 * E); build_adj();
  long long V = (long long)NB * M; vis = malloc(8 * V); fr = malloc(8 * V); nx = malloc(8 * V);
  long long c = cost(), best = c; int *bestvol = malloc(sizeof(int) * E), *bestev = malloc(sizeof(int) * E);
  memcpy(bestvol, evol, sizeof(int) * E); memcpy(bestev, ev, sizeof(int) * E);
  fprintf(stderr, "initial cost %lld\n", c);
  for (long long it = 0; it < iters && c > 0; it++) {
    double T = T0 * (1.0 - (double)it / iters);
    int mt = rnd() % 10;
    if (mt < 8) { /* voltage change */
      int ei = HOLO ? (int)(rnd() % E) : nflags + (int)(rnd() % (E - nflags));
      int old = evol[ei]; int nv = rnd() % M; if (nv == old) continue;
      evol[ei] = nv; long long c2 = cost();
      if (c2 <= c || (T > 0 && exp((c - c2) / T) * 4294967296.0 > (double)(rnd() & 0xffffffffULL))) c = c2; else evol[ei] = old;
    } else { /* swap hop targets */
      int k = rnd() % J, p1 = rnd() % N, p2 = rnd() % N; if (p1 == p2) continue;
      int e1 = hopedge[k][p1], e2 = hopedge[k][p2]; int t = ev[e1]; ev[e1] = ev[e2]; ev[e2] = t;
      /* adjacency of lines changes: rebuild */
      build_adj(); long long c2 = cost();
      if (c2 <= c || (T > 0 && exp((c - c2) / T) * 4294967296.0 > (double)(rnd() & 0xffffffffULL))) c = c2;
      else { t = ev[e1]; ev[e1] = ev[e2]; ev[e2] = t; build_adj(); }
    }
    if (c < best) { best = c; memcpy(bestvol, evol, sizeof(int) * E); memcpy(bestev, ev, sizeof(int) * E); }
    if (it % 2000 == 0) fprintf(stderr, "it %lld T %.2f cost %lld best %lld\n", it, T, c, best);
  }
  printf("q %d j %d M %d holo %d best %lld\n", q, J, M, HOLO, best);
  char fn[256]; snprintf(fn, sizeof fn, "lanneal_best_q%d_j%d_M%d_h%d.txt", q, J, M, HOLO);
  FILE *o = fopen(fn, "w"); fprintf(o, "%d %d 1 %d\n", NB, M, E);
  for (int i = 0; i < E; i++) fprintf(o, "%d %d %d 0\n", eu[i], bestev[i], bestvol[i]);
  fclose(o);
  return 0;
}
