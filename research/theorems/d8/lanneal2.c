/* lanneal2.c -- annealing of Z_M voltages on H(q) + j hop matchings with a focus set of sources.
 * cost(F) = # (s, lift vertex) pairs at distance > D for sources s in F (base vertices; the group acts, so (s,0)).
 * When cost(F) = 0, a full check over all base sources runs; failing sources (worst first) join F.
 * usage: lanneal2 ghfile j M iters T0 seed holo(0/1) F0 threads [D]
 * Output: lanneal2_q{q}_j{j}_M{M}_h{holo}_s{seed}.txt (liftdiam format) whenever a full check passes, plus stats. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <pthread.h>

static int q, N, J, M, D = 8, HOLO, NT = 1;
static int NB, E; static int *eu, *ev, *evol;
static int *adjstart, *adje;
static uint64_t rng_s = 88172645463325252ULL;
static inline uint64_t rnd(void) { rng_s ^= rng_s << 13; rng_s ^= rng_s >> 7; rng_s ^= rng_s << 17; return rng_s; }

static void build_adj(void) {
  int *deg = calloc(NB, sizeof(int));
  for (int i = 0; i < E; i++) { deg[eu[i]]++; deg[ev[i]]++; }
  adjstart[0] = 0; for (int v = 0; v < NB; v++) adjstart[v + 1] = adjstart[v] + deg[v];
  int *fill = calloc(NB, sizeof(int));
  for (int i = 0; i < E; i++) { adje[adjstart[eu[i]] + fill[eu[i]]++] = i; adje[adjstart[ev[i]] + fill[ev[i]]++] = i; }
  free(deg); free(fill);
}

/* evaluate unreached for a list of sources, multi-threaded over batches */
typedef struct { int *src; int ns; long long *per; int b0, b1; } job_t;
static void *runjob(void *arg) {
  job_t *jb = arg; long long V = (long long)NB * M;
  uint64_t *vis = malloc(8 * V), *fr = malloc(8 * V), *nx = malloc(8 * V);
  for (int b = jb->b0; b < jb->b1; b++) {
    int s0 = b * 64; int nb = jb->ns - s0 < 64 ? jb->ns - s0 : 64; uint64_t full = nb == 64 ? ~0ULL : ((1ULL << nb) - 1);
    memset(vis, 0, 8 * V); memset(fr, 0, 8 * V);
    for (int i = 0; i < nb; i++) { long long w = (long long)jb->src[s0 + i] * M; vis[w] |= 1ULL << i; fr[w] |= 1ULL << i; }
    for (int lev = 0; lev < D; lev++) {
      for (int v = 0; v < NB; v++) {
        uint64_t *nxv = nx + (long long)v * M; memset(nxv, 0, 8 * M);
        for (int a = adjstart[v]; a < adjstart[v + 1]; a++) {
          int e = adje[a]; int u, w;
          if (eu[e] == v) { u = ev[e]; w = evol[e]; } else { u = eu[e]; w = (M - evol[e]) % M; }
          uint64_t *fu = fr + (long long)u * M; int k = M - w;
          for (int g = 0; g < k; g++) nxv[g] |= fu[g + w];
          for (int g = k; g < M; g++) nxv[g] |= fu[g + w - M];
        }
        uint64_t *vv = vis + (long long)v * M; for (int g = 0; g < M; g++) { nxv[g] &= ~vv[g]; vv[g] |= nxv[g]; }
      }
      uint64_t *t = fr; fr = nx; nx = t;
    }
    long long cnt[64]; memset(cnt, 0, sizeof cnt);
    for (long long w = 0; w < V; w++) { uint64_t m = full & ~vis[w]; while (m) { int i = __builtin_ctzll(m); cnt[i]++; m &= m - 1; } }
    for (int i = 0; i < nb; i++) jb->per[s0 + i] = cnt[i];
  }
  free(vis); free(fr); free(nx); return NULL;
}
static long long evaluate(int *src, int ns, long long *per) {
  int nbat = (ns + 63) / 64; int nt = NT < nbat ? NT : nbat; pthread_t th[64]; job_t jb[64];
  for (int t = 0; t < nt; t++) { jb[t].src = src; jb[t].ns = ns; jb[t].per = per; jb[t].b0 = nbat * t / nt; jb[t].b1 = nbat * (t + 1) / nt; pthread_create(&th[t], NULL, runjob, &jb[t]); }
  for (int t = 0; t < nt; t++) pthread_join(th[t], NULL);
  long long s = 0; for (int i = 0; i < ns; i++) s += per[i]; return s;
}

int main(int argc, char **argv) {
  if (argc < 10) { fprintf(stderr, "usage: lanneal2 ghfile j M iters T0 seed holo F0 threads [D]\n"); return 1; }
  FILE *f = fopen(argv[1], "r"); J = atoi(argv[2]); M = atoi(argv[3]); long long iters = atoll(argv[4]);
  double T0 = atof(argv[5]); long long seed = atoll(argv[6]); rng_s ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 20; i++) rnd();
  HOLO = atoi(argv[7]); int F0 = atoi(argv[8]); NT = atoi(argv[9]); if (argc > 10) D = atoi(argv[10]);
  if (fscanf(f, "%d %d", &q, &N) != 2) return 1;
  NB = 2 * N; E = N * (q + 1) + J * N;
  eu = malloc(sizeof(int) * E); ev = malloc(sizeof(int) * E); evol = calloc(E, sizeof(int));
  int e = 0;
  for (int k = 0; k < N; k++) for (int i = 0; i <= q; i++) { int p; if (fscanf(f, "%d", &p) != 1) return 1; eu[e] = p; ev[e] = N + k; evol[e] = HOLO ? (int)(rnd() % M) : 0; e++; }
  int nflags = e; int *hopedge = malloc(sizeof(int) * J * N);
  for (int k = 0; k < J; k++) {
    int *S = malloc(sizeof(int) * N); for (int p = 0; p < N; p++) S[p] = p;
    for (int i = N - 1; i > 0; i--) { int r = rnd() % (i + 1); int t = S[i]; S[i] = S[r]; S[r] = t; }
    for (int p = 0; p < N; p++) { eu[e] = p; ev[e] = N + S[p]; evol[e] = 1 + rnd() % (M - 1); hopedge[k * N + p] = e; e++; }
    free(S);
  }
  adjstart = malloc(sizeof(int) * (NB + 1)); adje = malloc(sizeof(int) * 2 * E); build_adj();
  int *all = malloc(sizeof(int) * NB); for (int v = 0; v < NB; v++) all[v] = v;
  long long *perall = malloc(sizeof(long long) * NB);
  int *F = malloc(sizeof(int) * NB); int nF = 0; char *inF = calloc(NB, 1);
  for (int i = 0; i < F0 && nF < NB; i++) { int v = rnd() % NB; if (!inF[v]) { inF[v] = 1; F[nF++] = v; } }
  long long *perF = malloc(sizeof(long long) * NB);
  long long c = evaluate(F, nF, perF);
  fprintf(stderr, "initial focus cost %lld (|F|=%d)\n", c, nF);
  long long it;
  for (it = 0; it < iters; it++) {
    if (c == 0) {
      long long tot = evaluate(all, NB, perall);
      fprintf(stderr, "it %lld full check: unreached %lld (|F|=%d)\n", it, tot, nF);
      if (tot == 0) break;
      /* add up to 32 worst failing sources */
      for (int r = 0; r < 32; r++) { int w = -1; for (int v = 0; v < NB; v++) if (!inF[v] && perall[v] > 0 && (w < 0 || perall[v] > perall[w])) w = v; if (w < 0) break; inF[w] = 1; F[nF++] = w; }
      c = evaluate(F, nF, perF);
      continue;
    }
    double T = T0 * (1.0 - (double)it / iters);
    int mt = rnd() % 10;
    if (mt < 9) {
      int ei = HOLO ? (int)(rnd() % E) : nflags + (int)(rnd() % (E - nflags));
      int old = evol[ei]; int nv = rnd() % M; if (nv == old) continue;
      evol[ei] = nv; long long c2 = evaluate(F, nF, perF);
      if (c2 <= c || (T > 0 && exp((c - c2) / T) * 4294967296.0 > (double)(rnd() & 0xffffffffULL))) c = c2; else evol[ei] = old;
    } else {
      int k = rnd() % J, p1 = rnd() % N, p2 = rnd() % N; if (p1 == p2) continue;
      int e1 = hopedge[k * N + p1], e2 = hopedge[k * N + p2]; int t = ev[e1]; ev[e1] = ev[e2]; ev[e2] = t; build_adj();
      long long c2 = evaluate(F, nF, perF);
      if (c2 <= c || (T > 0 && exp((c - c2) / T) * 4294967296.0 > (double)(rnd() & 0xffffffffULL))) c = c2;
      else { t = ev[e1]; ev[e1] = ev[e2]; ev[e2] = t; build_adj(); }
    }
    if (it % 500 == 0) fprintf(stderr, "it %lld T %.2f focus cost %lld |F| %d\n", it, T, c, nF);
  }
  long long tot = evaluate(all, NB, perall);
  printf("q %d j %d M %d holo %d seed %lld iters %lld final_full_unreached %lld |F| %d\n", q, J, M, HOLO, seed, it, tot, nF);
  char fn[256]; snprintf(fn, sizeof fn, "lanneal2_q%d_j%d_M%d_h%d_s%lld.txt", q, J, M, HOLO, seed);
  FILE *o = fopen(fn, "w"); fprintf(o, "%d %d 1 %d\n", NB, M, E);
  for (int i = 0; i < E; i++) fprintf(o, "%d %d %d 0\n", eu[i], ev[i], evol[i]);
  fclose(o);
  return 0;
}
