/* anneal.c: simulated annealing for a near-duality s: points -> lines of H(q).
 * usage: anneal GH OUT SEED ITERS T0 T1 ALPHA [FORBID]
 *   GH:     "q N" then N lines of q+1 point ids (line k is incidence vertex N+k).
 *   OUT:    N lines, line s(u) for each point u (0..N-1).
 *   FORBID: optional file of N ints; require s(u) != FORBID[u] for all u (used for hop 2 vs hop 1).
 * Objective over unordered collinear point pairs {u,x} (distance 2 in the incidence graph):
 *   +1 if s(u), s(x) are concurrent (distance 2), -ALPHA if opposite (distance 6), 0 if distance 4.
 * Hard constraints: s is a bijection; s(u) is not incident to u (no flag doubles as a hop).
 * Swap moves s(u) <-> s(w); only pairs touching u or w change, so a delta costs 2q(q+1) lookups.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>

static uint64_t rs[2];
static uint64_t rotl64(uint64_t x, int k) { return (x << k) | (x >> (64 - k)); }
static uint64_t nxt(void) {
  uint64_t s0 = rs[0], s1 = rs[1], r = s0 + s1;
  s1 ^= s0; rs[0] = rotl64(s0, 24) ^ s1 ^ (s1 << 16); rs[1] = rotl64(s1, 37);
  return r;
}
static double urand(void) { return (nxt() >> 11) * (1.0 / 9007199254740992.0); }
static int irand(int n) { return (int)(urand() * n); }
static void seed_rng(uint64_t seed) {
  uint64_t z = seed;
  for (int i = 0; i < 2; i++) {
    z += 0x9E3779B97F4A7C15ULL; uint64_t x = z;
    x = (x ^ (x >> 30)) * 0xBF58476D1CE4E5B9ULL; x = (x ^ (x >> 27)) * 0x94D049BB133111EBULL;
    rs[i] = x ^ (x >> 31);
  }
}

static int q, N, K, Kc;
static int *LP, *TH, *COL;      /* LP[k*K+i] points on line k; TH[p*K+i] lines through p; COL[u*Kc+i] collinear pts */
static uint8_t *INC, *R;        /* INC[p*N+k] incidence; R[a*N+b]: 0 dist4/same, 1 concurrent, 2 opposite */
static int *S, *BEST, *FORB;
static int valtab[3];

static inline int bad(int u, int a) { return INC[(size_t)u * N + a] || (FORB && FORB[u] == a); }

static void die(const char *m) { fprintf(stderr, "%s\n", m); exit(1); }

static void stats(const int *s, long *C, long *O, long *E) {
  long c = 0, o = 0, e = 0;
  for (int u = 0; u < N; u++)
    for (int i = 0; i < Kc; i++) {
      int x = COL[u * Kc + i];
      if (x > u) { e++; int r = R[(size_t)s[u] * N + s[x]]; if (r == 1) c++; else if (r == 2) o++; }
    }
  *C = c; *O = o; *E = e;
}

int main(int argc, char **argv) {
  if (argc < 8) die("usage: anneal GH OUT SEED ITERS T0 T1 ALPHA [FORBID]");
  FILE *fp = fopen(argv[1], "r");
  if (!fp) die("open GH");
  if (fscanf(fp, "%d %d", &q, &N) != 2) die("bad GH header");
  K = q + 1; Kc = q * (q + 1);
  LP = malloc(sizeof(int) * N * K);
  for (int k = 0; k < N; k++) for (int i = 0; i < K; i++) if (fscanf(fp, "%d", &LP[k * K + i]) != 1) die("bad GH line");
  fclose(fp);
  TH = malloc(sizeof(int) * N * K);
  int *cnt = calloc(N, sizeof(int));
  for (int k = 0; k < N; k++) for (int i = 0; i < K; i++) { int p = LP[k * K + i]; if (cnt[p] >= K) die("point degree"); TH[p * K + cnt[p]++] = k; }
  for (int p = 0; p < N; p++) if (cnt[p] != K) die("point degree != q+1");
  INC = calloc((size_t)N * N, 1);
  for (int p = 0; p < N; p++) for (int i = 0; i < K; i++) INC[(size_t)p * N + TH[p * K + i]] = 1;
  /* collinear point lists: points sharing a line with u */
  COL = malloc(sizeof(int) * N * Kc);
  for (int u = 0; u < N; u++) {
    int c = 0;
    for (int i = 0; i < K; i++) { int k = TH[u * K + i];
      for (int j = 0; j < K; j++) { int x = LP[k * K + j]; if (x != u) { if (c >= Kc) die("too many collinear"); COL[u * Kc + c++] = x; } } }
    if (c != Kc) die("collinear count != q(q+1)");
  }
  /* line concurrency graph: lines sharing a point; BFS gives incidence distance 2*dist */
  int *LN = malloc(sizeof(int) * N * Kc);
  for (int a = 0; a < N; a++) {
    int c = 0;
    for (int i = 0; i < K; i++) { int p = LP[a * K + i];
      for (int j = 0; j < K; j++) { int b = TH[p * K + j]; if (b != a) { if (c >= Kc) die("too many concurrent"); LN[a * Kc + c++] = b; } } }
    if (c != Kc) die("concurrent count != q(q+1)");
  }
  R = malloc((size_t)N * N);
  int *dist = malloc(sizeof(int) * N), *qu = malloc(sizeof(int) * N);
  int maxd = 0;
  for (int a = 0; a < N; a++) {
    for (int b = 0; b < N; b++) dist[b] = -1;
    int h = 0, t = 0; qu[t++] = a; dist[a] = 0;
    while (h < t) { int x = qu[h++]; for (int i = 0; i < Kc; i++) { int y = LN[x * Kc + i]; if (dist[y] < 0) { dist[y] = dist[x] + 1; qu[t++] = y; } } }
    for (int b = 0; b < N; b++) {
      int d = dist[b]; if (d < 0) die("line graph disconnected");
      if (d > maxd) maxd = d;
      R[(size_t)a * N + b] = (d == 1) ? 1 : (d == 3) ? 2 : 0;
    }
  }
  if (maxd != 3) die("line-graph diameter != 3");
  long seed = atol(argv[3]); long iters = atol(argv[4]);
  double T0 = atof(argv[5]), T1 = atof(argv[6]); int alpha = atoi(argv[7]);
  valtab[0] = 0; valtab[1] = 1; valtab[2] = -alpha;
  FORB = NULL;
  if (argc > 8) {
    FORB = malloc(sizeof(int) * N);
    FILE *ff = fopen(argv[8], "r"); if (!ff) die("open FORBID");
    for (int u = 0; u < N; u++) if (fscanf(ff, "%d", &FORB[u]) != 1) die("bad FORBID");
    fclose(ff);
  }
  seed_rng((uint64_t)seed * 0x2545F4914F6CDD1DULL + 12345);
  S = malloc(sizeof(int) * N); BEST = malloc(sizeof(int) * N);
  for (int u = 0; u < N; u++) S[u] = u;
  for (int u = N - 1; u > 0; u--) { int j = irand(u + 1); int t = S[u]; S[u] = S[j]; S[j] = t; }
  /* repair random start into the feasible set */
  for (;;) {
    int nb = 0;
    for (int u = 0; u < N; u++) if (bad(u, S[u])) {
      nb++;
      for (int tries = 0; tries < 10000000; tries++) {
        int w = irand(N); if (w == u) continue;
        if (!bad(u, S[w]) && !bad(w, S[u])) { int t = S[u]; S[u] = S[w]; S[w] = t; break; }
      }
    }
    if (nb == 0) break;
  }
  long C, O, E;
  stats(S, &C, &O, &E);
  long f = C - (long)alpha * O;
  long bestf = f; memcpy(BEST, S, sizeof(int) * N);
  fprintf(stderr, "init E %ld C %ld O %ld f %ld\n", E, C, O, f);
  double lr = log(T1 / T0);
  double T = T0;
  long acc = 0;
  for (long it = 0; it < iters; it++) {
    if ((it & 4095) == 0) {
      T = T0 * exp(lr * (double)it / (double)iters);
      if (f > bestf) { bestf = f; memcpy(BEST, S, sizeof(int) * N); }
    }
    int u = irand(N), w = irand(N - 1); if (w >= u) w++;
    int a = S[u], b = S[w];
    if (bad(u, b) || bad(w, a)) continue;
    /* delta over collinear pairs touching u or w */
    int d = 0;
    const int *cu = COL + (size_t)u * Kc, *cw = COL + (size_t)w * Kc;
    for (int i = 0; i < Kc; i++) { int x = cu[i]; if (x == w) continue; int sx = S[x];
      d += valtab[R[(size_t)b * N + sx]] - valtab[R[(size_t)a * N + sx]]; }
    for (int i = 0; i < Kc; i++) { int x = cw[i]; if (x == u) continue; int sx = S[x];
      d += valtab[R[(size_t)a * N + sx]] - valtab[R[(size_t)b * N + sx]]; }
    if (d >= 0 || urand() < exp(d / T)) {
      S[u] = b; S[w] = a; f += d; acc++;
    }
  }
  if (f > bestf) { bestf = f; memcpy(BEST, S, sizeof(int) * N); }
  /* verify best from scratch */
  for (int u = 0; u < N; u++) if (bad(u, BEST[u])) die("best violates constraints");
  { char *seen = calloc(N, 1); for (int u = 0; u < N; u++) { if (seen[BEST[u]]) die("not a bijection"); seen[BEST[u]] = 1; } free(seen); }
  stats(BEST, &C, &O, &E);
  printf("q %d N %d E %ld C %ld O %ld conc_frac %.5f opp_frac %.5f f %ld acc %ld iters %ld alpha %d\n",
         q, N, E, C, O, (double)C / E, (double)O / E, C - (long)alpha * O, acc, iters, alpha);
  printf("random_baseline conc_frac %.5f opp_frac %.5f\n", (double)Kc / (N - 1), (double)(q * q * q * q * q) / (N - 1));
  FILE *fo = fopen(argv[2], "w");
  if (!fo) die("open OUT");
  for (int u = 0; u < N; u++) fprintf(fo, "%d\n", BEST[u]);
  fclose(fo);
  return 0;
}
