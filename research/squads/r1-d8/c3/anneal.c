/* anneal.c -- simulated annealing on the labels of a Z_M1 x Z_M2 voltage lift (liftdiam file format), card c3.
 *
 * Cost = unreached (source,target) pairs within D steps, summed over a sample of base sources: every STEP-th
 * base vertex (the same sample as liftdiam's SRC_STEP). Whenever the sample cost reaches 0, a full check over
 * all base vertices runs; its failing sources join the sample and the search goes on.
 * Moves: give one mutable edge a new random Z_M2 label (Z_M1 part untouched).
 *   mode 0: mutable = hop darts (a != 0); mode 1: mutable = all darts (flags too).
 *   With probability PT the edge is drawn from the mutable edges within H-distance 2 of the target or of the
 *   source of a random unreached pair of the current accepted state; otherwise uniform.
 * BFS semantics are those of liftdiam.c (bitset, 64 sources per batch, pull step).
 *
 * usage: anneal base.txt D seconds seed T0 T1 STEP mode PT out.txt
 * Writes the best state (or the success state) to out.txt in liftdiam format.
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>

static int NB, M1, M2, M, E, D;
static long long V;
static int *eu, *ev, *ea, *eb;
static int *adjstart, *adjv, *adja, *adjb;
static uint64_t *vis, *fr, *nx;
static int *srcs, nsrc, *inS;
static long long *unr_src;
static int *mut, nmut;
static int *incs, *incl;   /* CSR: mutable darts at each base vertex */
static int *fs, *fa;       /* CSR: flag graph (darts with a == 0) */
static int *stamp, curstamp = 0, *bq;

#define CAP 512
static int exs_new[CAP], exs_cur[CAP], nex_new = 0, nex_cur = 0;
static long long exw_new[CAP], exw_cur[CAP], nseen = 0;

static unsigned long long rs = 88172645463325252ULL;
static inline unsigned long long rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline int rndint(int n) { return (int)(rnd() % (unsigned long long)n); }
static inline double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }

static void build_adj(void) {
  int *deg = calloc(NB, sizeof(int)), *fill = calloc(NB, sizeof(int));
  for (int i = 0; i < E; i++) { deg[eu[i]]++; deg[ev[i]]++; }
  adjstart[0] = 0;
  for (int v = 0; v < NB; v++) adjstart[v + 1] = adjstart[v] + deg[v];
  for (int i = 0; i < E; i++) {
    int u = eu[i], v = ev[i], p;
    p = adjstart[u] + fill[u]++; adjv[p] = v; adja[p] = ea[i]; adjb[p] = eb[i];
    p = adjstart[v] + fill[v]++; adjv[p] = u; adja[p] = (M1 - ea[i]) % M1; adjb[p] = (M2 - eb[i]) % M2;
  }
  free(deg); free(fill);
}

/* unreached (source,target) pairs of one batch of <= 64 sources (sample indices s0..s0+nb-1) */
static long long batch_unr(int s0, int nb, long long *per) {
  uint64_t full = (nb == 64) ? ~0ULL : ((1ULL << nb) - 1);
  memset(vis, 0, sizeof(uint64_t) * V);
  memset(fr, 0, sizeof(uint64_t) * V);
  for (int i = 0; i < nb; i++) { long long w = (long long)srcs[s0 + i] * M; fr[w] |= 1ULL << i; vis[w] |= 1ULL << i; }
  long long need = (long long)nb * V, got = nb;
  for (int level = 0; level < D && got < need; level++) {
    long long newbits = 0;
    for (int v = 0; v < NB; v++) {
      uint64_t *nxv = nx + (long long)v * M;
      memset(nxv, 0, sizeof(uint64_t) * M);
      for (int e = adjstart[v]; e < adjstart[v + 1]; e++) {
        int u = adjv[e], a = adja[e], bb = adjb[e];
        const uint64_t *fru = fr + (long long)u * M;
        int kk = M2 - bb;
        for (int g1 = 0; g1 < M1; g1++) {
          int h1 = g1 + a; if (h1 >= M1) h1 -= M1;
          uint64_t *dst = nxv + g1 * M2; const uint64_t *src = fru + h1 * M2;
          for (int g2 = 0; g2 < kk; g2++) dst[g2] |= src[g2 + bb];
          for (int g2 = kk; g2 < M2; g2++) dst[g2] |= src[g2 + bb - M2];
        }
      }
      uint64_t *visv = vis + (long long)v * M;
      for (int g = 0; g < M; g++) { uint64_t m = nxv[g] & ~visv[g]; nxv[g] = m; visv[g] |= m; newbits += __builtin_popcountll(m); }
    }
    uint64_t *t = fr; fr = nx; nx = t;
    got += newbits;
    if (newbits == 0) break;
  }
  long long u = 0;
  if (per) for (int i = 0; i < nb; i++) per[i] = 0;
  for (long long w = 0; w < V; w++) {
    uint64_t m = (~vis[w]) & full;
    if (!m) continue;
    u += __builtin_popcountll(m);
    while (m) {
      int i = __builtin_ctzll(m); m &= m - 1;
      if (per) per[i]++;
      nseen++;   /* reservoir sample of unreached pairs (source base vertex, lift target) */
      if (nex_new < CAP) { exs_new[nex_new] = srcs[s0 + i]; exw_new[nex_new] = w; nex_new++; }
      else { long long j = (long long)(rnd() % (unsigned long long)nseen); if (j < CAP) { exs_new[j] = srcs[s0 + i]; exw_new[j] = w; } }
    }
  }
  return u;
}

static long long evaluate(void) {
  build_adj();
  nseen = 0; nex_new = 0;
  long long tot = 0;
  for (int s0 = 0; s0 < nsrc; s0 += 64) {
    int nb = nsrc - s0 < 64 ? nsrc - s0 : 64;
    tot += batch_unr(s0, nb, unr_src + s0);
  }
  return tot;
}

/* mutable darts incident to the H-ball of radius R around center (flag graph) */
static int gather(int center, int R, int *cand, int cmax) {
  int nc = 0, head = 0, qt = 0;
  curstamp++;
  bq[qt++] = center; stamp[center] = curstamp;
  for (int r = 0; r <= R; r++) {
    int end = qt;
    for (int i = head; i < end; i++) {
      int z = bq[i];
      for (int j = incs[z]; j < incs[z + 1]; j++) if (nc < cmax) cand[nc++] = incl[j];
    }
    if (r == R) break;
    for (int i = head; i < end; i++) {
      int z = bq[i];
      for (int j = fs[z]; j < fs[z + 1]; j++) { int y2 = fa[j]; if (stamp[y2] != curstamp) { stamp[y2] = curstamp; bq[qt++] = y2; } }
    }
    head = end;
    if (head == qt) break;
  }
  return nc;
}

static void write_state(const char *path) {
  FILE *o = fopen(path, "w");
  if (!o) { perror("write"); exit(1); }
  fprintf(o, "%d %d %d %d\n", NB, M1, M2, E);
  for (int i = 0; i < E; i++) fprintf(o, "%d %d %d %d\n", eu[i], ev[i], ea[i], eb[i]);
  fclose(o);
}

int main(int argc, char **argv) {
  if (argc < 11) { fprintf(stderr, "usage: anneal base.txt D seconds seed T0 T1 STEP mode PT out.txt\n"); return 1; }
  D = atoi(argv[2]);
  double secs = atof(argv[3]);
  unsigned long long seed = strtoull(argv[4], NULL, 10);
  rs ^= seed * 0x9E3779B97F4A7C15ULL; if (!rs) rs = 1;
  for (int i = 0; i < 20; i++) rnd();
  double T0 = atof(argv[5]), T1 = atof(argv[6]);
  int STEP = atoi(argv[7]), mode = atoi(argv[8]);
  double PT = atof(argv[9]);
  const char *outp = argv[10];

  FILE *f = fopen(argv[1], "r");
  if (!f || fscanf(f, "%d %d %d %d", &NB, &M1, &M2, &E) != 4) { fprintf(stderr, "bad base file\n"); return 1; }
  M = M1 * M2; V = (long long)NB * M;
  eu = malloc(sizeof(int) * E); ev = malloc(sizeof(int) * E); ea = malloc(sizeof(int) * E); eb = malloc(sizeof(int) * E);
  for (int i = 0; i < E; i++) {
    if (fscanf(f, "%d %d %d %d", &eu[i], &ev[i], &ea[i], &eb[i]) != 4) { fprintf(stderr, "bad edge %d\n", i); return 1; }
    ea[i] = ((ea[i] % M1) + M1) % M1; eb[i] = ((eb[i] % M2) + M2) % M2;
  }
  fclose(f);

  /* mutable darts and their incidence lists; flag graph for the H-balls */
  mut = malloc(sizeof(int) * E); nmut = 0;
  for (int i = 0; i < E; i++) if (mode == 1 || ea[i] != 0) mut[nmut++] = i;
  int *cnt = calloc(NB, sizeof(int));
  incs = calloc(NB + 1, sizeof(int)); incl = malloc(sizeof(int) * (2 * nmut + 1));
  for (int j = 0; j < nmut; j++) { int e = mut[j]; cnt[eu[e]]++; cnt[ev[e]]++; }
  for (int v = 0; v < NB; v++) incs[v + 1] = incs[v] + cnt[v];
  memset(cnt, 0, sizeof(int) * NB);
  for (int j = 0; j < nmut; j++) { int e = mut[j]; incl[incs[eu[e]] + cnt[eu[e]]++] = e; incl[incs[ev[e]] + cnt[ev[e]]++] = e; }
  memset(cnt, 0, sizeof(int) * NB);
  int nflag = 0;
  for (int i = 0; i < E; i++) if (ea[i] == 0) { cnt[eu[i]]++; cnt[ev[i]]++; nflag++; }
  fs = calloc(NB + 1, sizeof(int)); fa = malloc(sizeof(int) * (2 * nflag + 1));
  for (int v = 0; v < NB; v++) fs[v + 1] = fs[v] + cnt[v];
  memset(cnt, 0, sizeof(int) * NB);
  for (int i = 0; i < E; i++) if (ea[i] == 0) {
    int u = eu[i], v = ev[i];
    fa[fs[u] + cnt[u]++] = v; fa[fs[v] + cnt[v]++] = u;
  }
  free(cnt);

  adjstart = malloc(sizeof(int) * (NB + 1));
  adjv = malloc(sizeof(int) * 2 * E); adja = malloc(sizeof(int) * 2 * E); adjb = malloc(sizeof(int) * 2 * E);
  vis = malloc(sizeof(uint64_t) * V); fr = malloc(sizeof(uint64_t) * V); nx = malloc(sizeof(uint64_t) * V);
  if (!vis || !fr || !nx) { fprintf(stderr, "oom\n"); return 1; }
  srcs = malloc(sizeof(int) * NB); inS = calloc(NB, sizeof(int)); unr_src = calloc(NB, sizeof(long long));
  stamp = calloc(NB, sizeof(int)); bq = malloc(sizeof(int) * NB);
  nsrc = 0;
  for (int v = 0; v < NB; v += STEP) { srcs[nsrc++] = v; inS[v] = 1; }

  long long cur = evaluate();
  memcpy(exs_cur, exs_new, sizeof(int) * nex_new); memcpy(exw_cur, exw_new, sizeof(long long) * nex_new); nex_cur = nex_new;
  long long best = cur;
  int *beste = malloc(sizeof(int) * (nmut + 1));
  for (int j = 0; j < nmut; j++) beste[j] = eb[mut[j]];
  printf("init: NB %d M %d mutable %d sample %d (step %d) cost %lld\n", NB, M, nmut, nsrc, STEP, cur);
  fflush(stdout);

  double t0 = now();
  long long iters = 0, acc = 0;
  int nfull = 0, success = 0;
  while (now() - t0 < secs) {
    if (cur == 0) {
      /* sample is clean: full check over all base vertices */
      int saved = nsrc;
      nsrc = 0; for (int v = 0; v < NB; v++) srcs[nsrc++] = v;
      long long full = evaluate();
      nfull++;
      printf("full check %d (sample was %d): unreached %lld at %.1fs\n", nfull, saved, full, now() - t0);
      fflush(stdout);
      if (full == 0) { success = 1; break; }
      nsrc = 0;
      for (int v = 0; v < NB; v++) if (inS[v] || unr_src[v] > 0) { inS[v] = 1; srcs[nsrc++] = v; }
      cur = evaluate();
      memcpy(exs_cur, exs_new, sizeof(int) * nex_new); memcpy(exw_cur, exw_new, sizeof(long long) * nex_new); nex_cur = nex_new;
      best = cur;
      for (int j = 0; j < nmut; j++) beste[j] = eb[mut[j]];
      printf("  sample extended to %d sources, cost %lld\n", nsrc, cur);
      fflush(stdout);
      continue;
    }
    double el = now() - t0;
    double T = T0 * pow(T1 / T0, el / secs);
    int e;
    if (nex_cur > 0 && rnd01() < PT) {
      int k = rndint(nex_cur);
      int s = exs_cur[k], y = (int)(exw_cur[k] / M);
      int center = (rnd() & 1) ? y : s;
      static int cand[4096];
      int nc = gather(center, 2, cand, 4096);
      e = nc > 0 ? cand[rndint(nc)] : mut[rndint(nmut)];
    } else {
      e = mut[rndint(nmut)];
    }
    int oldb = eb[e];
    int newb = (oldb + 1 + rndint(M2 - 1)) % M2;
    eb[e] = newb;
    long long c = evaluate();
    iters++;
    long long dl = c - cur;
    if (dl <= 0 || rnd01() < exp(-(double)dl / T)) {
      cur = c; acc++;
      memcpy(exs_cur, exs_new, sizeof(int) * nex_new); memcpy(exw_cur, exw_new, sizeof(long long) * nex_new); nex_cur = nex_new;
      if (cur < best) {
        best = cur;
        for (int j = 0; j < nmut; j++) beste[j] = eb[mut[j]];
        printf("  it %lld t %.1fs T %.3f best %lld\n", iters, now() - t0, T, best);
        fflush(stdout);
      }
    } else {
      eb[e] = oldb;
    }
    if (iters % 500 == 0) {
      printf("  it %lld t %.1fs T %.3f cur %lld best %lld acc %.3f\n", iters, now() - t0, T, cur, best, (double)acc / iters);
      fflush(stdout);
    }
  }
  if (success) {
    write_state(outp);
    printf("SUCCESS: full unreached 0, iters %lld, time %.1fs, output %s\n", iters, now() - t0, outp);
  } else {
    for (int j = 0; j < nmut; j++) eb[mut[j]] = beste[j];
    write_state(outp);
    printf("END: best sample cost %lld, iters %lld, accepted %lld, full checks %d, time %.1fs, output %s\n",
           best, iters, acc, nfull, now() - t0, outp);
  }
  return 0;
}
