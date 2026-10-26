/* w2: two-sided translation bipartite graphs.
 * Vertices A = G (0..N-1), B = G (N..2N-1). Edge a ~ N+s_i*a*t_i for i=0..3, with s_0=t_0=identity.
 * Each (s_i,t_i) pair gives a perfect matching; the 4 matchings must be disjoint (simple 4-regular graph).
 * t_i all equal to identity gives the Haar graph H(G,{s_i}) (the family of all round-1 near misses).
 * Cost = number of unordered vertex pairs at distance > 8 (bitset BFS for all sources).
 * usage: ts TABLE.bin SECONDS SEED T0 T1 INIT(haar|rand) OUT.edges
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <math.h>
#include <stdio.h>

static int N, n, W;
static uint16_t *MT; /* N*N table */
static int inv_[1 << 13];
#define MUL(x, y) ((int)MT[(size_t)(x) * N + (y)])

static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline int rndi(int m) { return (int)(rnd() % (uint64_t)m); }
static double rndu(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int S[4], Tt[4];
static int *F[4], *G[4]; /* f_i(a)=s_i a t_i on A; g_i(b) inverse */
static int *adj;          /* n*4 */
static uint64_t *bufA, *bufB;

static void build_maps(void) {
  for (int i = 0; i < 4; i++) {
    for (int a = 0; a < N; a++) {
      int f = MUL(MUL(S[i], a), Tt[i]);
      F[i][a] = f;
    }
    for (int a = 0; a < N; a++) G[i][F[i][a]] = a;
  }
  for (int a = 0; a < N; a++)
    for (int i = 0; i < 4; i++) adj[a * 4 + i] = N + F[i][a];
  for (int b = 0; b < N; b++)
    for (int i = 0; i < 4; i++) adj[(N + b) * 4 + i] = G[i][b];
}

static int disjoint_ok(void) {
  for (int i = 0; i < 4; i++)
    for (int j = i + 1; j < 4; j++)
      for (int a = 0; a < N; a++)
        if (MUL(MUL(S[i], a), Tt[i]) == MUL(MUL(S[j], a), Tt[j])) return 0;
  return 1;
}

/* returns number of unordered far pairs */
static long cost_full(void) {
  build_maps();
  uint64_t *cur = bufA, *nxt = bufB;
  memset(cur, 0, sizeof(uint64_t) * (size_t)n * W);
  for (int v = 0; v < n; v++) cur[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
  for (int step = 0; step < 8; step++) {
    for (int v = 0; v < n; v++) {
      uint64_t *o = nxt + (size_t)v * W;
      const uint64_t *c = cur + (size_t)v * W;
      memcpy(o, c, sizeof(uint64_t) * W);
      for (int k = 0; k < 4; k++) {
        const uint64_t *u = cur + (size_t)adj[v * 4 + k] * W;
        for (int w = 0; w < W; w++) o[w] |= u[w];
      }
    }
    uint64_t *t = cur; cur = nxt; nxt = t;
  }
  long reached = 0;
  for (int v = 0; v < n; v++) {
    const uint64_t *c = cur + (size_t)v * W;
    for (int w = 0; w < W; w++) reached += __builtin_popcountll(c[w]);
  }
  /* cur and nxt swapped; keep buffers as allocated */
  long far_ord = (long)n * n - reached;
  return far_ord / 2;
}

static void write_edges(const char *path) {
  FILE *f = fopen(path, "w");
  if (!f) return;
  fprintf(f, "%d\n", n);
  build_maps();
  for (int a = 0; a < N; a++)
    for (int i = 0; i < 4; i++) fprintf(f, "%d %d\n", a, N + F[i][a]);
  fclose(f);
}

int main(int argc, char **argv) {
  if (argc < 8) { fprintf(stderr, "usage: ts TABLE.bin SECONDS SEED T0 T1 INIT OUT.edges\n"); return 1; }
  FILE *fp = fopen(argv[1], "rb");
  if (!fp) { perror("table"); return 1; }
  int32_t N32; fread(&N32, 4, 1, fp); N = N32;
  MT = malloc((size_t)N * N * 2);
  fread(MT, 2, (size_t)N * N, fp); fclose(fp);
  double secs = atof(argv[2]);
  rs ^= (uint64_t)atol(argv[3]) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 10; i++) rnd();
  double T0 = atof(argv[4]), T1 = atof(argv[5]);
  int haar = strcmp(argv[6], "haar") == 0;
  const char *out = argv[7];
  n = 2 * N; W = (n + 63) / 64;
  for (int i = 0; i < 4; i++) { F[i] = malloc(sizeof(int) * N); G[i] = malloc(sizeof(int) * N); }
  adj = malloc(sizeof(int) * n * 4);
  bufA = malloc(sizeof(uint64_t) * (size_t)n * W);
  bufB = malloc(sizeof(uint64_t) * (size_t)n * W);
  /* init */
  for (int tries = 0;; tries++) {
    S[0] = Tt[0] = 0;
    for (int i = 1; i < 4; i++) {
      S[i] = 1 + rndi(N - 1);
      Tt[i] = haar ? 0 : rndi(N);
    }
    if (disjoint_ok()) break;
    if (tries > 100000) { fprintf(stderr, "no init\n"); return 1; }
  }
  if (getenv("INITS") && getenv("INITT")) {
    sscanf(getenv("INITS"), "%d %d %d %d", &S[0], &S[1], &S[2], &S[3]);
    sscanf(getenv("INITT"), "%d %d %d %d", &Tt[0], &Tt[1], &Tt[2], &Tt[3]);
    if (!disjoint_ok()) { fprintf(stderr, "init not disjoint\n"); return 1; }
  }
  long cur = cost_full();
  long best = cur; int bS[4], bT[4];
  memcpy(bS, S, sizeof S); memcpy(bT, Tt, sizeof Tt);
  struct timespec t0, t1; clock_gettime(CLOCK_MONOTONIC, &t0);
  long it = 0, acc = 0;
  double el = 0;
  while (1) {
    if ((it & 15) == 0) {
      clock_gettime(CLOCK_MONOTONIC, &t1);
      el = (t1.tv_sec - t0.tv_sec) + 1e-9 * (t1.tv_nsec - t0.tv_nsec);
      if (el >= secs || best == 0) break;
    }
    double frac = el / secs;
    double T = T0 * pow(T1 / T0, frac);
    int i = 1 + rndi(3);
    int side = haar ? 0 : rndi(2); /* haar: only move s_i */
    int oldv = side ? Tt[i] : S[i];
    int newv = rndi(N);
    if (newv == oldv) continue;
    if (side) Tt[i] = newv; else S[i] = newv;
    if (!disjoint_ok()) { if (side) Tt[i] = oldv; else S[i] = oldv; continue; }
    long c = cost_full();
    it++;
    if (c <= cur || rndu() < exp(-(double)(c - cur) / T)) {
      cur = c; acc++;
      if (c < best) {
        best = c; memcpy(bS, S, sizeof S); memcpy(bT, Tt, sizeof Tt);
      }
    } else {
      if (side) Tt[i] = oldv; else S[i] = oldv;
    }
  }
  memcpy(S, bS, sizeof S); memcpy(Tt, bT, sizeof Tt);
  write_edges(out);
  printf("RESULT ts N=%d n=%d seconds=%.1f evals=%ld acc=%ld best_far_unordered=%ld miss=%.3f\n",
         N, n, el, it, acc, best, 2.0 * best / n);
  printf("S");
  for (int i = 0; i < 4; i++) printf(" %d", S[i]);
  printf("\nT");
  for (int i = 0; i < 4; i++) printf(" %d", Tt[i]);
  printf("\n");
  return 0;
}
