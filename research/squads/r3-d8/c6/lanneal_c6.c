/* lanneal_c6.c -- Z_M voltage (label) annealer on H(q) + J FIXED hop matchings. Adapted from lanneal2.c:
 * hop swaps are removed, so the matchings never change; every edge voltage (flags and hops) is annealed (holonomy).
 * Cost = unreached (source, lift vertex) pairs at radius D over a focus set F of base sources. When cost(F) = 0 a full
 * check over all 2N base sources runs; up to 32 worst failing sources join F. Temperature falls linearly in wall time.
 * usage: lanneal_c6 ghfile matchfile M tmax seed T0 F0 outfile [D]
 *   ghfile    : "q N", then N lines of q+1 point ids (line k is vertex N+k)
 *   matchfile : "J N", then J rows of N ints; entry p of row k = line index s_k(p) (hop p -- N+s_k(p))
 *   outfile   : liftdiam format ("NB M 1 E", then "u v a 0" per edge), written at the end
 * Prints one RESULT line on stdout: M, J, seed, iterations, focus size, final full-check unreached U, valid flag. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>

static int q, N, J, M, D = 8, NB, E;
static int *eu, *ev, *evol, *adjstart, *adje;
static uint64_t rng_s = 88172645463325252ULL;
static inline uint64_t rnd(void) { rng_s ^= rng_s << 13; rng_s ^= rng_s >> 7; rng_s ^= rng_s << 17; return rng_s; }
static double now(void) { struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts); return ts.tv_sec + 1e-9 * ts.tv_nsec; }

static long long V;
static uint64_t *vis, *fr, *nx;

static long long eval_sources(const int *src, int ns, long long *per) {
  long long tot = 0;
  for (int b0 = 0; b0 < ns; b0 += 64) {
    int nb = ns - b0 < 64 ? ns - b0 : 64;
    uint64_t full = nb == 64 ? ~0ULL : ((1ULL << nb) - 1);
    memset(vis, 0, 8 * (size_t)V); memset(fr, 0, 8 * (size_t)V);
    for (int i = 0; i < nb; i++) { long long w = (long long)src[b0 + i] * M; vis[w] |= 1ULL << i; fr[w] |= 1ULL << i; }
    for (int lev = 0; lev < D; lev++) {
      for (int v = 0; v < NB; v++) {
        uint64_t *nxv = nx + (long long)v * M;
        memset(nxv, 0, 8 * (size_t)M);
        for (int a = adjstart[v]; a < adjstart[v + 1]; a++) {
          int e = adje[a], u, w;
          if (eu[e] == v) { u = ev[e]; w = evol[e]; } else { u = eu[e]; w = (M - evol[e]) % M; }
          const uint64_t *fu = fr + (long long)u * M; int k = M - w;
          for (int g = 0; g < k; g++) nxv[g] |= fu[g + w];
          for (int g = k; g < M; g++) nxv[g] |= fu[g + w - M];
        }
        uint64_t *vv = vis + (long long)v * M;
        for (int g = 0; g < M; g++) { nxv[g] &= ~vv[g]; vv[g] |= nxv[g]; }
      }
      uint64_t *t = fr; fr = nx; nx = t;
    }
    long long cnt[64]; memset(cnt, 0, sizeof cnt);
    for (long long x = 0; x < V; x++) { uint64_t m = full & ~vis[x]; while (m) { int i = __builtin_ctzll(m); cnt[i]++; m &= m - 1; } }
    for (int i = 0; i < nb; i++) { per[b0 + i] = cnt[i]; tot += cnt[i]; }
  }
  return tot;
}

int main(int argc, char **argv) {
  if (argc < 9) { fprintf(stderr, "usage: lanneal_c6 ghfile matchfile M tmax seed T0 F0 outfile [D]\n"); return 1; }
  M = atoi(argv[3]); double tmax = atof(argv[4]); long long seed = atoll(argv[5]);
  double T0 = atof(argv[6]); int F0 = atoi(argv[7]); const char *outfile = argv[8];
  if (argc > 9) D = atoi(argv[9]);
  rng_s ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 20; i++) rnd();

  FILE *f = fopen(argv[1], "r"); if (!f) { perror(argv[1]); return 1; }
  if (fscanf(f, "%d %d", &q, &N) != 2) return 1;
  int *lines = malloc(sizeof(int) * N * (q + 1));
  for (int i = 0; i < N * (q + 1); i++) if (fscanf(f, "%d", &lines[i]) != 1) return 1;
  fclose(f);

  FILE *g = fopen(argv[2], "r"); if (!g) { perror(argv[2]); return 1; }
  int n2; if (fscanf(g, "%d %d", &J, &n2) != 2 || n2 != N) { fprintf(stderr, "bad matchfile header\n"); return 1; }
  int *sm = malloc(sizeof(int) * J * N);
  for (int i = 0; i < J * N; i++) if (fscanf(g, "%d", &sm[i]) != 1) return 1;
  fclose(g);

  NB = 2 * N; E = N * (q + 1) + J * N; V = (long long)NB * M;
  eu = malloc(sizeof(int) * E); ev = malloc(sizeof(int) * E); evol = malloc(sizeof(int) * E);
  int e = 0;
  for (int k = 0; k < N; k++) for (int i = 0; i <= q; i++) { eu[e] = lines[k * (q + 1) + i]; ev[e] = N + k; evol[e] = (int)(rnd() % M); e++; }
  for (int k = 0; k < J; k++) for (int p = 0; p < N; p++) { eu[e] = p; ev[e] = N + sm[k * N + p]; evol[e] = (int)(rnd() % M); e++; }
  int nbad = 0; /* sanity: hops must not repeat a flag, and each hop must be a bijection */
  for (int k = 0; k < J; k++) { char *seen = calloc(N, 1); for (int p = 0; p < N; p++) { if (seen[sm[k * N + p]]) nbad++; seen[sm[k * N + p]] = 1; } free(seen); }
  for (int p = 0; p < N; p++) for (int k = 0; k < J; k++) for (int i = 0; i <= q; i++) if (lines[(sm[k * N + p]) * (q + 1) + i] == p) nbad++;
  if (nbad) { fprintf(stderr, "matchfile not a flag-avoiding bijection set (%d problems)\n", nbad); return 1; }

  adjstart = malloc(sizeof(int) * (NB + 1)); adje = malloc(sizeof(int) * 2 * E);
  int *deg = calloc(NB, sizeof(int));
  for (int i = 0; i < E; i++) { deg[eu[i]]++; deg[ev[i]]++; }
  adjstart[0] = 0; for (int v = 0; v < NB; v++) adjstart[v + 1] = adjstart[v] + deg[v];
  int *fill = calloc(NB, sizeof(int));
  for (int i = 0; i < E; i++) { adje[adjstart[eu[i]] + fill[eu[i]]++] = i; adje[adjstart[ev[i]] + fill[ev[i]]++] = i; }
  free(deg); free(fill);
  vis = malloc(8 * (size_t)V); fr = malloc(8 * (size_t)V); nx = malloc(8 * (size_t)V);

  int *all = malloc(sizeof(int) * NB); for (int v = 0; v < NB; v++) all[v] = v;
  long long *perall = malloc(sizeof(long long) * NB), *perF = malloc(sizeof(long long) * NB);
  int *F = malloc(sizeof(int) * NB); int nF = 0; char *inF = calloc(NB, 1);
  for (int i = 0; i < F0 && nF < NB; i++) { int v = (int)(rnd() % NB); if (!inF[v]) { inF[v] = 1; F[nF++] = v; } }
  long long c = eval_sources(F, nF, perF);
  fprintf(stderr, "init focus cost %lld |F| %d\n", c, nF);

  double t0 = now(); long long it; long long full_tot = -1; int acc = 0;
  for (it = 0;; it++) {
    double el = now() - t0;
    if (el >= tmax) break;
    if (c == 0) {
      full_tot = eval_sources(all, NB, perall);
      fprintf(stderr, "t %.1f full check unreached %lld |F| %d\n", el, full_tot, nF);
      if (full_tot == 0) break;
      for (int r = 0; r < 32; r++) {
        int w = -1; for (int v = 0; v < NB; v++) if (!inF[v] && perall[v] > 0 && (w < 0 || perall[v] > perall[w])) w = v;
        if (w < 0) break; inF[w] = 1; F[nF++] = w;
      }
      c = eval_sources(F, nF, perF);
      continue;
    }
    double T = T0 * (1.0 - el / tmax);
    int ei = (int)(rnd() % E);
    int old = evol[ei]; int nv = (int)(rnd() % M); if (nv == old) continue;
    evol[ei] = nv;
    long long c2 = eval_sources(F, nF, perF);
    if (c2 <= c || (T > 0 && exp((double)(c - c2) / T) > (double)(rnd() >> 11) * (1.0 / 9007199254740992.0))) { c = c2; acc++; }
    else evol[ei] = old;
    if (it % 20000 == 0 && it) fprintf(stderr, "t %.1f it %lld T %.3f focus cost %lld |F| %d acc %d\n", el, it, T, c, nF, acc);
  }
  if (full_tot != 0) full_tot = eval_sources(all, NB, perall);
  int valid = (full_tot == 0);
  FILE *o = fopen(outfile, "w"); if (!o) { perror(outfile); return 1; }
  fprintf(o, "%d %d 1 %d\n", NB, M, E);
  for (int i = 0; i < E; i++) fprintf(o, "%d %d %d 0\n", eu[i], ev[i], evol[i]);
  fclose(o);
  printf("RESULT M %d J %d seed %lld T0 %g tmax %g iters %lld focus %d U %lld valid %d out %s\n",
         M, J, seed, T0, tmax, it, nF, full_tot, valid, outfile);
  return 0;
}
