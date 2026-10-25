/* orbils.c: iterated local search (Andrade-Resende-Werneck style: (1,2)-swaps, forced-insertion perturbation,
   undo log, ARW acceptance) for a maximum independent set of an orbit conflict graph (all vertices have equal weight).
   usage: orbils GRAPH.bin INIT.txt SECONDS SEED OUT.txt [RESTART_ITERS]
   GRAPH.bin: int32 n, m, osz; then n*osz int32 point ids (orbit v = orbpts[v*osz..]); then m int32 pairs (a,b).
   Writes the best solution as point ids (one per line) to OUT.txt whenever it improves. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <limits.h>
#include <time.h>

static int n, m, osz;
static int *orbpts, *adjs, *adj;
static char *inS, *inQ;
static int *tight, *sxor;
static long long *age;
static int *sol, solN, *solPos;
static int *fre, freN, *frePos;
static int *Q, qN;
static int *logv; static char *logt; static long logN, logCap;
static int logging;
static long long iters;
static int *Lbuf, *remv, *mark; static int stampv;
static int *bestsol, bestN;
static const char *outfile;

static uint64_t rs = 0x9E3779B97F4A7C15ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline int rndint(int k) { return (int)((rnd() >> 11) % (uint64_t)k); }
static inline double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) { struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts); return ts.tv_sec + 1e-9 * ts.tv_nsec; }

static inline void push(int v) { if (!inQ[v]) { inQ[v] = 1; Q[qN++] = v; } }
static inline void fre_add(int v) { frePos[v] = freN; fre[freN++] = v; }
static inline void fre_del(int v) { int p = frePos[v]; int last = fre[--freN]; fre[p] = last; frePos[last] = p; frePos[v] = -1; }
static inline void sol_add(int v) { solPos[v] = solN; sol[solN++] = v; }
static inline void sol_del(int v) { int p = solPos[v]; int last = sol[--solN]; sol[p] = last; solPos[last] = p; solPos[v] = -1; }

static void logpush(int v, char t) {
  if (logN == logCap) {
    logCap = logCap ? 2 * logCap : 1 << 16;
    logv = realloc(logv, sizeof(int) * logCap);
    logt = realloc(logt, logCap);
  }
  logv[logN] = v; logt[logN] = t; logN++;
}

/* insert v (must have no solution neighbour) */
static void ins(int v) {
  if (logging) logpush(v, 1);
  inS[v] = 1; sol_add(v); age[v] = iters;
  if (frePos[v] >= 0) fre_del(v);
  for (int e = adjs[v]; e < adjs[v + 1]; e++) {
    int u = adj[e];
    tight[u]++; sxor[u] ^= v;
    if (tight[u] == 1 && frePos[u] >= 0) fre_del(u);
  }
}

/* delete v from the solution */
static void del(int v) {
  if (logging) logpush(v, 0);
  inS[v] = 0; sol_del(v); age[v] = iters;
  for (int e = adjs[v]; e < adjs[v + 1]; e++) {
    int u = adj[e];
    tight[u]--; sxor[u] ^= v;
    if (tight[u] == 0 && !inS[u]) fre_add(u);
  }
  fre_add(v); /* tight[v] == 0 because the solution is independent */
}

static void fill_free(void) {
  while (freN > 0) { int v = fre[rndint(freN)]; ins(v); push(v); }
}

/* (1,2)-swap around solution vertex x: remove x, insert two non-adjacent 1-tight neighbours of x */
static int try2(int x) {
  int L = 0;
  for (int e = adjs[x]; e < adjs[x + 1]; e++) { int u = adj[e]; if (!inS[u] && tight[u] == 1) Lbuf[L++] = u; }
  if (L < 2) return 0;
  for (int i = L - 1; i > 0; i--) { int j = rndint(i + 1); int t = Lbuf[i]; Lbuf[i] = Lbuf[j]; Lbuf[j] = t; }
  for (int a = 0; a < L; a++) {
    int u = Lbuf[a];
    if (stampv == INT_MAX) { memset(mark, 0, sizeof(int) * n); stampv = 0; }
    int st = ++stampv;
    for (int e = adjs[u]; e < adjs[u + 1]; e++) mark[adj[e]] = st;
    for (int b = a + 1; b < L; b++) {
      int w = Lbuf[b];
      if (mark[w] != st) {
        del(x); ins(u); ins(w);
        push(u); push(w);
        for (int e = adjs[x]; e < adjs[x + 1]; e++) { int y = adj[e]; if (!inS[y] && tight[y] == 1) push(sxor[y]); }
        return 1;
      }
    }
  }
  return 0;
}

static void local_search(void) {
  fill_free();
  while (qN > 0) {
    int x = Q[--qN]; inQ[x] = 0;
    if (!inS[x]) continue;
    if (try2(x)) fill_free();
  }
}

/* force-insert v (not in S): remove its solution neighbours */
static void perturb(int v) {
  int c = 0;
  for (int e = adjs[v]; e < adjs[v + 1]; e++) { int u = adj[e]; if (inS[u]) remv[c++] = u; }
  for (int i = 0; i < c; i++) del(remv[i]);
  ins(v); push(v);
  for (int i = 0; i < c; i++) {
    int x = remv[i];
    for (int e = adjs[x]; e < adjs[x + 1]; e++) { int y = adj[e]; if (!inS[y] && tight[y] == 1) push(sxor[y]); }
  }
}

/* pick a non-solution vertex: best of 4 random samples by (tightness, age) */
static int pick(void) {
  int bv = -1, bt = INT_MAX; long long ba = 0;
  for (int t = 0; t < 4; t++) {
    int v; do { v = rndint(n); } while (inS[v]);
    if (bv < 0 || tight[v] < bt || (tight[v] == bt && age[v] < ba)) { bv = v; bt = tight[v]; ba = age[v]; }
  }
  return bv;
}

static void write_best(void) {
  char tmp[1024]; snprintf(tmp, sizeof tmp, "%s.tmp", outfile);
  FILE *f = fopen(tmp, "w"); if (!f) return;
  for (int i = 0; i < bestN; i++) { int v = bestsol[i]; for (int k = 0; k < osz; k++) fprintf(f, "%d\n", orbpts[(long)v * osz + k]); }
  fclose(f); rename(tmp, outfile);
}

static void restore_best(void) {
  int saved = logging; logging = 0;
  while (solN > 0) del(sol[solN - 1]);
  for (int i = 0; i < bestN; i++) ins(bestsol[i]);
  fill_free();
  logging = saved;
}

int main(int argc, char **argv) {
  if (argc < 6) { fprintf(stderr, "usage: orbils GRAPH.bin INIT.txt SECONDS SEED OUT.txt [RESTART_ITERS]\n"); return 1; }
  const char *gf = argv[1], *initf = argv[2];
  double T = atof(argv[3]);
  uint64_t seed = strtoull(argv[4], 0, 10);
  outfile = argv[5];
  long long restart_iters = argc > 6 ? atoll(argv[6]) : 200000;
  rs ^= (seed + 1) * 0x2545F4914F6CDD1DULL; for (int i = 0; i < 20; i++) rnd();

  FILE *f = fopen(gf, "rb"); if (!f) { perror(gf); return 1; }
  int hdr[3]; if (fread(hdr, 4, 3, f) != 3) return 1;
  n = hdr[0]; m = hdr[1]; osz = hdr[2];
  orbpts = malloc(sizeof(int) * (size_t)n * osz);
  if (fread(orbpts, 4, (size_t)n * osz, f) != (size_t)n * osz) return 1;
  int *E = malloc(sizeof(int) * 2 * (size_t)m);
  if (fread(E, 4, 2 * (size_t)m, f) != 2 * (size_t)m) return 1;
  fclose(f);
  adjs = calloc(n + 1, sizeof(int));
  for (long e = 0; e < m; e++) { adjs[E[2 * e] + 1]++; adjs[E[2 * e + 1] + 1]++; }
  for (int i = 0; i < n; i++) adjs[i + 1] += adjs[i];
  adj = malloc(sizeof(int) * 2 * (size_t)m);
  int *fp = malloc(sizeof(int) * n); memcpy(fp, adjs, sizeof(int) * n);
  for (long e = 0; e < m; e++) { int a = E[2 * e], b = E[2 * e + 1]; adj[fp[a]++] = b; adj[fp[b]++] = a; }
  free(fp); free(E);

  inS = calloc(n, 1); inQ = calloc(n, 1);
  tight = calloc(n, sizeof(int)); sxor = calloc(n, sizeof(int)); age = calloc(n, sizeof(long long));
  sol = malloc(sizeof(int) * n); solPos = malloc(sizeof(int) * n);
  fre = malloc(sizeof(int) * n); frePos = malloc(sizeof(int) * n);
  Q = malloc(sizeof(int) * n);
  Lbuf = malloc(sizeof(int) * n); remv = malloc(sizeof(int) * n); mark = calloc(n, sizeof(int));
  bestsol = malloc(sizeof(int) * n);
  for (int v = 0; v < n; v++) { solPos[v] = -1; frePos[v] = -1; }
  for (int v = 0; v < n; v++) fre_add(v);

  long ninit = 0, nskip = 0;
  f = fopen(initf, "r"); if (!f) { perror(initf); return 1; }
  int v;
  while (fscanf(f, "%d", &v) == 1) {
    if (v < 0 || v >= n || inS[v]) continue;
    if (tight[v] > 0) { nskip++; continue; }
    ins(v); ninit++;
  }
  fclose(f);
  for (int i = 0; i < solN; i++) push(sol[i]);
  local_search();
  bestN = solN; memcpy(bestsol, sol, sizeof(int) * solN);
  fprintf(stderr, "n=%d m=%d osz=%d init=%ld skipped=%ld start=%d\n", n, m, osz, ninit, nskip, solN);
  write_best();

  double t0 = now(), tprint = t0;
  int cur = solN;
  long long lastImp = iters, nAcc = 0, nWorse = 0;
  while (1) {
    iters++;
    if ((iters & 127) == 0) {
      double t = now();
      if (t - t0 > T) break;
      if (t - tprint > 20) { tprint = t; fprintf(stderr, "t=%.0f it=%lld cur=%d best=%d acc=%lld worse=%lld\n", t - t0, iters, cur, bestN, nAcc, nWorse); }
    }
    if (cur < bestN && iters - lastImp > restart_iters) { restore_best(); cur = solN; lastImp = iters; }
    logN = 0; logging = 1;
    int k = 1;
    if (rnd01() < 1.0 / (2.0 * solN)) { k = 2; while (rnd01() < 0.5 && k < 6) k++; }
    for (int i = 0; i < k; i++) { int w = pick(); perturb(w); }
    local_search();
    logging = 0;
    int nw = solN, acc;
    if (nw >= cur) acc = 1;
    else {
      int d = cur - nw, ds = bestN - nw; if (ds < 1) ds = 1;
      acc = rnd01() < 1.0 / (1.0 + (double)d * ds);
      if (acc) nWorse++;
    }
    if (acc) {
      cur = nw; nAcc++;
      if (cur > bestN) {
        bestN = cur; memcpy(bestsol, sol, sizeof(int) * solN); lastImp = iters;
        write_best();
        fprintf(stderr, "IMPROVED t=%.1f it=%lld best=%d (points %d)\n", now() - t0, iters, bestN, bestN * osz);
      }
    } else {
      for (long i = logN - 1; i >= 0; i--) { if (logt[i]) del(logv[i]); else ins(logv[i]); }
    }
  }
  fprintf(stderr, "FINAL best=%d orbits points=%d iters=%lld\n", bestN, bestN * osz, iters);
  printf("%d\n", bestN * osz);
  return 0;
}
