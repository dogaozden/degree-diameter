/* c05: Z_N voltage lift of a 4-regular bipartite base multigraph (K+K vertices, 4K edges, one colour per edge,
   proper 4-edge-colouring), fibre F4^4, chart as in research/theorems/graphs/build_d16D5_n33792.py.
   Letter 0 (colour 0) gets translation set {lam*b0} u {e}  (degree 17) when D == 17, else degree 16.
   Lift: A-vertex ((i,g),x) ~ B-vertex ((j,g+v),A_c x + w), w in W_c.
   usage: lift17 INFILE OUTSTATE N D seconds seed T0 Tend NS [OUTEDGES]
     INFILE: line 1 K; then 4K lines "i j v c" (or "i j" for random init); optional line "E c0 c1 c2 c3" (vector e).
   seconds = 0: only evaluate the input state (full fibre sampling).  Cost = sum over sources of #vertices at
   distance > 5 (sources: one per base vertex x all fibre points when NS = 256; NS random fibre points otherwise). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <time.h>
#include <stdint.h>
#include <limits.h>

#define MAXK 8
#define MAXE 32
#define S 17

static uint64_t rs = 88172645463325252ULL;
static inline uint64_t xr(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline int rnd(int m) { return (int)(xr() % (uint64_t)m); }
static double urand(void) { return (double)(xr() >> 11) * (1.0 / 9007199254740992.0); }

static const int MUL[4][4] = {{0,0,0,0},{0,1,2,3},{0,2,3,1},{0,3,1,2}};
/* chart of the (16,5) builder */
static const int CHA[4][4][4] = {
  {{1,0,0,0},{0,1,0,0},{0,0,1,0},{0,0,0,1}},
  {{0,1,3,0},{1,0,2,3},{3,2,1,3},{1,2,3,1}},
  {{0,1,3,2},{3,0,2,3},{0,3,1,2},{0,1,0,3}},
  {{1,0,3,3},{1,0,3,0},{0,0,1,1},{2,3,1,2}}};
static const int CHB[4][4] = {{1,2,0,2},{0,1,1,2},{1,0,0,2},{0,1,3,2}};

static double wall(void){ struct timespec ts; clock_gettime(CLOCK_MONOTONIC,&ts); return ts.tv_sec+1e-9*ts.tv_nsec; }
static int K, NE, N, D;
static int EI[MAXE], EJ[MAXE], EV[MAXE], EC[MAXE];
static int CH[4][4][4], BC[4][4];
static int MATT[4][256], WV[4][4];
static int EVEC;
static int n, nA;
static int *adj, *dg;
static unsigned int *stamp;
static unsigned int curstamp = 0;
static int *qa;

static int vid4(const int *v) { return v[0] | (v[1] << 2) | (v[2] << 4) | (v[3] << 6); }
static void unvid(int x, int *v) { v[0] = x & 3; v[1] = (x >> 2) & 3; v[2] = (x >> 4) & 3; v[3] = (x >> 6) & 3; }

static void setup_chart(void) {
  for (int c = 0; c < 4; c++) {
    for (int x = 0; x < 256; x++) {
      int xv[4], yv[4]; unvid(x, xv);
      for (int r = 0; r < 4; r++) { int s = 0; for (int q = 0; q < 4; q++) s ^= MUL[CH[c][r][q]][xv[q]]; yv[r] = s; }
      MATT[c][x] = vid4(yv);
    }
    for (int l = 0; l < 4; l++) { int w[4]; for (int k = 0; k < 4; k++) w[k] = MUL[l][BC[c][k]]; WV[c][l] = vid4(w); }
  }
}

static int build(void) {
  nA = K * N * 256; n = 2 * nA;
  memset(dg, 0, sizeof(int) * n);
  for (int e = 0; e < NE; e++) {
    int i = EI[e], j = EJ[e], v = EV[e], c = EC[e];
    int w[5], nw = 4;
    for (int l = 0; l < 4; l++) w[l] = WV[c][l];
    if (c == 0 && D == 17) { w[4] = EVEC; nw = 5; }
    for (int g = 0; g < N; g++) {
      int g2 = (g + v) % N;
      for (int x = 0; x < 256; x++) {
        int a = (i * N + g) * 256 + x, y0 = MATT[c][x];
        for (int t = 0; t < nw; t++) {
          int b = nA + (j * N + g2) * 256 + (y0 ^ w[t]);
          if (dg[a] >= S || dg[b] >= S) return -1;
          adj[(size_t)a * S + dg[a]++] = b;
          adj[(size_t)b * S + dg[b]++] = a;
        }
      }
    }
  }
  return 0;
}

/* sum over sources of #vertices not within distance 5 */
static long cost_sample(const int *xs, int nx) {
  static int srcbuf[2 * MAXK * 256];
  int ns = 0;
  for (int i = 0; i < K; i++) for (int t = 0; t < nx; t++) srcbuf[ns++] = (i * N) * 256 + xs[t];
  for (int j = 0; j < K; j++) for (int t = 0; t < nx; t++) srcbuf[ns++] = nA + (j * N) * 256 + xs[t];
  long tot = 0;
  for (int t = 0; t < ns; t++) {
    int s = srcbuf[t];
    if (curstamp == UINT_MAX - 1) { memset(stamp, 0, sizeof(unsigned int) * n); curstamp = 0; }
    curstamp++; stamp[s] = curstamp; qa[0] = s;
    int lo = 0, hi = 1, tail = 1;
    for (int d = 1; d <= 5; d++) {
      for (int idx = lo; idx < hi; idx++) {
        int u = qa[idx], du = dg[u];
        for (int q = 0; q < du; q++) {
          int w = adj[(size_t)u * S + q];
          if (stamp[w] != curstamp) { stamp[w] = curstamp; qa[tail++] = w; }
        }
      }
      lo = hi; hi = tail;
      if (lo == hi) break;
    }
    tot += n - tail;
  }
  return tot;
}

static int usedA[MAXK][4], usedB[MAXK][4];
static int colour_rec(int e) {
  if (e == NE) return 1;
  int i = EI[e], j = EJ[e], perm[4] = {0,1,2,3};
  for (int a = 3; a > 0; a--) { int b = rnd(a + 1); int tmp = perm[a]; perm[a] = perm[b]; perm[b] = tmp; }
  for (int t = 0; t < 4; t++) {
    int c = perm[t];
    if (!usedA[i][c] && !usedB[j][c]) {
      usedA[i][c] = usedB[j][c] = 1; EC[e] = c;
      if (colour_rec(e + 1)) return 1;
      usedA[i][c] = usedB[j][c] = 0;
    }
  }
  return 0;
}

static int in_span0(int x) { for (int l = 0; l < 4; l++) if (WV[0][l] == x) return 1; return 0; }

static void write_state(const char *fn, const int *EVs, const int *ECs, int evec) {
  FILE *f = fopen(fn, "w"); if (!f) return;
  fprintf(f, "%d\n", K);
  for (int e = 0; e < NE; e++) fprintf(f, "%d %d %d %d\n", EI[e], EJ[e], EVs[e], ECs[e]);
  int v[4]; unvid(evec, v);
  fprintf(f, "E %d %d %d %d\n", v[0], v[1], v[2], v[3]);
  fclose(f);
}

static int cmp_pair(const void *a, const void *b) {
  const long long *x = a, *y = b; return (*x > *y) - (*x < *y);
}

static void write_edges(const char *fn) {
  size_t cap = (size_t)n * S / 2 + 16; long long *pr = malloc(sizeof(long long) * cap); size_t m = 0;
  for (int u = 0; u < n; u++) for (int q = 0; q < dg[u]; q++) { int w = adj[(size_t)u * S + q]; if (u < w) pr[m++] = (long long)u * n + w; }
  qsort(pr, m, sizeof(long long), cmp_pair);
  FILE *f = fopen(fn, "w"); fprintf(f, "%d\n", n);
  size_t cnt = 0;
  for (size_t t = 0; t < m; t++) { if (t > 0 && pr[t] == pr[t - 1]) continue; fprintf(f, "%lld %lld\n", pr[t] / n, pr[t] % n); cnt++; }
  fclose(f); free(pr);
  fprintf(stderr, "wrote %s : n=%d unique edges=%zu (pairs %zu)\n", fn, n, cnt, m);
}

int main(int argc, char **argv) {
  if (argc < 10) { fprintf(stderr, "usage: lift17 INFILE OUTSTATE N D seconds seed T0 Tend NS [OUTEDGES]\n"); return 1; }
  const char *in = argv[1], *outst = argv[2];
  N = atoi(argv[3]); D = atoi(argv[4]);
  double limit = atof(argv[5]); uint64_t seed = strtoull(argv[6], 0, 10);
  double T0 = atof(argv[7]), Tend = atof(argv[8]); int NS = atoi(argv[9]);
  const char *outedges = argc > 10 ? argv[10] : NULL;
  rs ^= seed * 0x9E3779B97F4A7C15ULL; for (int k = 0; k < 10; k++) xr();
  memcpy(CH, CHA, sizeof(CH));
  for (int c = 0; c < 4; c++) for (int k = 0; k < 4; k++) BC[c][k] = CHB[c][k];
  setup_chart();

  FILE *f = fopen(in, "r"); if (!f) { fprintf(stderr, "no input\n"); return 1; }
  char line[256]; int have_v = 1, have_e = 0; int evec_in[4] = {0,0,0,0};
  if (!fgets(line, sizeof line, f)) return 1;
  K = atoi(line); NE = 4 * K;
  for (int e = 0; e < NE; e++) {
    if (!fgets(line, sizeof line, f)) { fprintf(stderr, "short file\n"); return 1; }
    int a, b, v = -1, c = -1; int cnt = sscanf(line, "%d %d %d %d", &a, &b, &v, &c);
    EI[e] = a; EJ[e] = b; if (cnt < 4) have_v = 0; else { EV[e] = v; EC[e] = c; }
  }
  while (fgets(line, sizeof line, f)) if (line[0] == 'E') { sscanf(line + 1, "%d %d %d %d", &evec_in[0], &evec_in[1], &evec_in[2], &evec_in[3]); have_e = 1; }
  fclose(f);

  /* per-vertex degree sanity: each base vertex has 4 edges */
  int dA[MAXK] = {0}, dB[MAXK] = {0};
  for (int e = 0; e < NE; e++) { dA[EI[e]]++; dB[EJ[e]]++; }
  for (int i = 0; i < K; i++) if (dA[i] != 4 || dB[i] != 4) { fprintf(stderr, "base not 4-regular\n"); return 1; }

  if (!have_v) {
    for (int i = 0; i < K; i++) for (int c = 0; c < 4; c++) { usedA[i][c] = usedB[i][c] = 0; }
    if (!colour_rec(0)) { fprintf(stderr, "no colouring\n"); return 1; }
    for (int e = 0; e < NE; e++) EV[e] = rnd(N);
  }
  if (have_e) EVEC = vid4(evec_in);
  else { do { EVEC = 1 + rnd(255); } while (in_span0(EVEC)); }
  if (in_span0(EVEC)) { fprintf(stderr, "e in span of b0\n"); return 1; }

  dg = calloc(0, 1); nA = K * N * 256; n = 2 * nA;
  adj = malloc(sizeof(int) * (size_t)n * S); dg = malloc(sizeof(int) * n);
  stamp = calloc(n, sizeof(unsigned int)); qa = malloc(sizeof(int) * n);
  if (!adj || !dg || !stamp || !qa) { fprintf(stderr, "oom\n"); return 1; }

  /* fibre sample */
  int perm256[256]; for (int x = 0; x < 256; x++) perm256[x] = x;
  for (int x = 255; x > 0; x--) { int b = rnd(x + 1); int t = perm256[x]; perm256[x] = perm256[b]; perm256[b] = t; }
  int SXn = NS; if (SXn > 256) SXn = 256; if (SXn < 1) SXn = 1;
  static int SX[256]; for (int t = 0; t < SXn; t++) SX[t] = perm256[t];

  if (build() != 0) { fprintf(stderr, "degree overflow\n"); return 1; }
  long cur = cost_sample(SX, SXn);
  long c0 = cur;
  static int bestEV[MAXE], bestEC[MAXE]; int bestVec = EVEC;
  memcpy(bestEV, EV, sizeof(int) * NE); memcpy(bestEC, EC, sizeof(int) * NE);
  long best = cur;
  fprintf(stderr, "init sample cost %ld (K=%d N=%d n=%d D=%d NS=%d)\n", cur, K, N, n, D, SXn);

  double start = wall(); long iters = 0, acc = 0;
  if (limit > 0 && best > 0) {
    while (1) {
      double el = wall() - start;
      if (el >= limit || best == 0) break;
      double T = T0 * pow(Tend / T0, el / limit);
      int e = -1, oldv = 0, oldvec = EVEC;
      if (D == 17 && urand() < 0.03) { int nv; do { nv = 1 + rnd(255); } while (in_span0(nv)); EVEC = nv; }
      else { e = rnd(NE); oldv = EV[e]; EV[e] = (oldv + 1 + rnd(N - 1)) % N; }
      build();
      long nc = cost_sample(SX, SXn);
      iters++;
      if (nc <= cur || urand() < exp(-(double)(nc - cur) / T)) {
        cur = nc; acc++;
        if (cur < best) { best = cur; bestVec = EVEC; memcpy(bestEV, EV, sizeof(int) * NE); memcpy(bestEC, EC, sizeof(int) * NE); }
      } else {
        if (e >= 0) EV[e] = oldv; else EVEC = oldvec;
      }
    }
  }
  fprintf(stderr, "iters %ld accepted %ld best sample cost %ld (init %ld)\n", iters, acc, best, c0);

  /* restore best, full check over all fibre points */
  memcpy(EV, bestEV, sizeof(int) * NE); memcpy(EC, bestEC, sizeof(int) * NE); EVEC = bestVec;
  int allx[256]; for (int x = 0; x < 256; x++) allx[x] = x;
  build();
  long full = cost_sample(allx, 256);
  printf("BEST_SAMPLE %ld FULL_COST %ld n=%d N=%d D=%d\n", best, full, n, N, D);
  write_state(outst, EV, EC, EVEC);
  if (full == 0 && outedges) write_edges(outedges);
  return 0;
}
