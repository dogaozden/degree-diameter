/* gwanneal.c -- simulated annealing for the "sheet model" lift of H(q):
 *   lift vertices (x, g), g in Z_M; H(q) edges keep g; hop k (k=1..j) joins point p to line s_k(p),
 *   (p,g) ~ (s_k(p), g + t_k(p)).
 * Cost = number of (point x, line y, g) with g NOT in the GUARANTEED set G(x,y): voltages of walks of length <= 7
 * that exist in every generalized hexagon (they only use d(point,line) <= 5, d(line,line) <= 6, d(point,point) <= 6):
 *   0; t_k(x); -l_k(b) (b on x); l_k(y); -t_k(a) (a on y); t_k(x)+l_m(y);
 *   (j=2) t_k(x)-l_m(s_k x), l_k(y)-t_m(s_k^{-1} y) for k != m.        (l_k(L) := t_k(s_k^{-1}(L)))
 * Cost 0 => every point->line (and by reversal line->point) pair is covered within 7 steps.
 * Same-colour pairs are checked separately at the end with their own guaranteed sets (length <= 8).
 *
 * usage: gwanneal ghfile j M iters T0 seed [mode]   mode 0: s_k random bijections (default)
 *                                                   mode 1: s_k disjoint 1-factors (parallel hops)
 * prints best cost and writes labels to stdout file "gw_best.txt" (format: N j M, then per point: s_1 t_1 [s_2 t_2])
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>

static int q, N, J, M; static int *LP; /* LP[k*(q+1)+i] = point i of line k */
static int *TH; /* TH[p*(q+1)+i] = line i through p */
static int *S[2], *SI[2], *T[2]; /* S[k][p] = line, SI[k][L] = point, T[k][p] = label */
static uint64_t FULL;
static uint64_t *X, *Y;
static uint64_t rng_s = 88172645463325252ULL;
static inline uint64_t rnd(void) { rng_s ^= rng_s << 13; rng_s ^= rng_s >> 7; rng_s ^= rng_s << 17; return rng_s; }
static inline int md(int a) { a %= M; return a < 0 ? a + M : a; }
static inline int lab(int k, int L) { return T[k][SI[k][L]]; }

static uint64_t compX(int x) {
  uint64_t m = 0;
  for (int k = 0; k < J; k++) {
    m |= 1ULL << T[k][x];
    for (int i = 0; i <= q; i++) m |= 1ULL << md(-lab(k, TH[x * (q + 1) + i]));
  }
  if (J == 2) for (int k = 0; k < 2; k++) { int o = 1 - k; m |= 1ULL << md(T[k][x] - lab(o, S[k][x])); }
  return m;
}
static uint64_t compY(int y) {
  uint64_t m = 0;
  for (int k = 0; k < J; k++) {
    m |= 1ULL << lab(k, y);
    for (int i = 0; i <= q; i++) m |= 1ULL << md(-T[k][LP[y * (q + 1) + i]]);
  }
  if (J == 2) for (int k = 0; k < 2; k++) { int o = 1 - k; m |= 1ULL << md(lab(k, y) - T[o][SI[k][y]]); }
  return m;
}
static inline int paircost(int x, int y) {
  uint64_t c = X[x] | Y[y] | 1ULL;
  for (int k = 0; k < J; k++) for (int m2 = 0; m2 < J; m2++) c |= 1ULL << md(T[k][x] + lab(m2, y));
  return __builtin_popcountll(FULL & ~c);
}
static long long rowcost(int x) { long long s = 0; for (int y = 0; y < N; y++) s += paircost(x, y); return s; }
static long long colcost(int y) { long long s = 0; for (int x = 0; x < N; x++) s += paircost(x, y); return s; }

/* affected rows/cols when T[k][p] changes or S[k] changes at p */
static int rows[64], nrows, cols[64], ncols;
static void addrow(int x) { for (int i = 0; i < nrows; i++) if (rows[i] == x) return; rows[nrows++] = x; }
static void addcol(int y) { for (int i = 0; i < ncols; i++) if (cols[i] == y) return; cols[ncols++] = y; }
static void affected_label(int k, int p) {
  int L = S[k][p];
  addrow(p); for (int i = 0; i <= q; i++) addrow(LP[L * (q + 1) + i]);
  addcol(L); for (int i = 0; i <= q; i++) addcol(TH[p * (q + 1) + i]);
  if (J == 2) { int o = 1 - k; addrow(SI[o][L]); addcol(S[o][p]); }
}
static long long blockcost(void) { /* cost of union of affected rows and cols */
  long long s = 0;
  for (int i = 0; i < nrows; i++) s += rowcost(rows[i]);
  for (int i = 0; i < ncols; i++) s += colcost(cols[i]);
  for (int i = 0; i < nrows; i++) for (int jj = 0; jj < ncols; jj++) s -= paircost(rows[i], cols[jj]);
  return s;
}
static void recompute_sets(void) { for (int i = 0; i < nrows; i++) X[rows[i]] = compX(rows[i]); for (int i = 0; i < ncols; i++) Y[cols[i]] = compY(cols[i]); }

static void perfect_matching(int *match, int *forbid) { /* random 1-factor point->line avoiding forbid[p] */
  int *mL = malloc(sizeof(int) * N), *mP = malloc(sizeof(int) * N), *par = malloc(sizeof(int) * N), *qu = malloc(sizeof(int) * N), *seen = malloc(sizeof(int) * N);
  for (int i = 0; i < N; i++) mL[i] = mP[i] = -1;
  int *ord = malloc(sizeof(int) * N); for (int i = 0; i < N; i++) ord[i] = i;
  for (int i = N - 1; i > 0; i--) { int r = rnd() % (i + 1); int t = ord[i]; ord[i] = ord[r]; ord[r] = t; }
  for (int oi = 0; oi < N; oi++) {
    int s = ord[oi]; /* BFS augmenting path from point s */
    for (int i = 0; i < N; i++) seen[i] = 0;
    int h = 0, t = 0; qu[t++] = s; int endL = -1;
    while (h < t && endL < 0) {
      int p = qu[h++]; int off = rnd() % (q + 1);
      for (int ii = 0; ii <= q; ii++) { int L = TH[p * (q + 1) + (ii + off) % (q + 1)]; if (forbid && forbid[p] == L) continue; if (seen[L]) continue; seen[L] = 1; par[L] = p;
        if (mL[L] < 0) { endL = L; break; } qu[t++] = mL[L]; }
    }
    if (endL < 0) { fprintf(stderr, "matching failed\n"); exit(1); }
    int L = endL; while (1) { int p = par[L]; int prevL = mP[p]; mP[p] = L; mL[L] = p; if (p == s) break; L = prevL; }
  }
  for (int p = 0; p < N; p++) match[p] = mP[p];
  free(mL); free(mP); free(par); free(qu); free(seen); free(ord);
}

int main(int argc, char **argv) {
  if (argc < 7) { fprintf(stderr, "usage: gwanneal ghfile j M iters T0 seed [mode]\n"); return 1; }
  FILE *f = fopen(argv[1], "r"); J = atoi(argv[2]); M = atoi(argv[3]); long long iters = atoll(argv[4]); double T0 = atof(argv[5]);
  rng_s ^= (uint64_t)atoll(argv[6]) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 10; i++) rnd();
  int mode = argc > 7 ? atoi(argv[7]) : 0;
  if (fscanf(f, "%d %d", &q, &N) != 2) return 1;
  LP = malloc(sizeof(int) * N * (q + 1)); TH = malloc(sizeof(int) * N * (q + 1)); int *cnt = calloc(N, sizeof(int));
  for (int k = 0; k < N; k++) for (int i = 0; i <= q; i++) { int p; if (fscanf(f, "%d", &p) != 1) return 1; LP[k * (q + 1) + i] = p; TH[p * (q + 1) + cnt[p]++] = k; }
  FULL = (M == 64) ? ~0ULL : ((1ULL << M) - 1);
  for (int k = 0; k < J; k++) { S[k] = malloc(sizeof(int) * N); SI[k] = malloc(sizeof(int) * N); T[k] = malloc(sizeof(int) * N); }
  for (int k = 0; k < J; k++) {
    if (mode == 1) perfect_matching(S[k], k ? S[0] : NULL);
    else { for (int p = 0; p < N; p++) S[k][p] = p; for (int i = N - 1; i > 0; i--) { int r = rnd() % (i + 1); int t = S[k][i]; S[k][i] = S[k][r]; S[k][r] = t; } }
    for (int p = 0; p < N; p++) SI[k][S[k][p]] = p;
    for (int p = 0; p < N; p++) T[k][p] = 1 + rnd() % (M - 1);
  }
  X = malloc(sizeof(uint64_t) * N); Y = malloc(sizeof(uint64_t) * N);
  for (int x = 0; x < N; x++) X[x] = compX(x);
  for (int y = 0; y < N; y++) Y[y] = compY(y);
  long long cost = 0; for (int x = 0; x < N; x++) cost += rowcost(x);
  long long best = cost; fprintf(stderr, "initial cost %lld\n", cost);
  int **BT = malloc(sizeof(int *) * 2), **BS = malloc(sizeof(int *) * 2);
  for (int k = 0; k < J; k++) { BT[k] = malloc(sizeof(int) * N); BS[k] = malloc(sizeof(int) * N); memcpy(BT[k], T[k], sizeof(int) * N); memcpy(BS[k], S[k], sizeof(int) * N); }
  for (long long it = 0; it < iters && cost > 0; it++) {
    double Tt = T0 * (1.0 - (double)it / iters);
    int k = rnd() % J; int p = rnd() % N;
    nrows = ncols = 0;
    int movetype = (mode == 0 && (rnd() % 4 == 0)) ? 1 : 0;
    int p2 = -1, old = T[k][p];
    if (movetype == 0) {
      affected_label(k, p);
      long long before = blockcost();
      int nv = 1 + rnd() % (M - 1); if (nv == old) continue;
      T[k][p] = nv; recompute_sets();
      long long after = blockcost(); long long d = after - before;
      if (d <= 0 || (Tt > 0 && exp(-d / Tt) * 4294967296.0 > (double)(rnd() & 0xffffffffULL))) { cost += d; }
      else { T[k][p] = old; recompute_sets(); }
    } else { /* swap s_k images of p and p2 */
      p2 = rnd() % N; if (p2 == p) continue;
      affected_label(k, p); affected_label(k, p2);
      int L1 = S[k][p], L2 = S[k][p2];
      long long before = blockcost();
      S[k][p] = L2; S[k][p2] = L1; SI[k][L2] = p; SI[k][L1] = p2;
      /* affected sets also include those for new positions */
      affected_label(k, p); affected_label(k, p2);
      recompute_sets();
      /* recompute before with same row/col set: approximate by recomputing full delta over union */
      long long after = blockcost();
      S[k][p] = L1; S[k][p2] = L2; SI[k][L1] = p; SI[k][L2] = p2; recompute_sets();
      long long before2 = blockcost();
      long long d = after - before2; (void)before;
      if (d <= 0 || (Tt > 0 && exp(-d / Tt) * 4294967296.0 > (double)(rnd() & 0xffffffffULL))) {
        S[k][p] = L2; S[k][p2] = L1; SI[k][L2] = p; SI[k][L1] = p2; recompute_sets(); cost += d; }
    }
    if (cost < best) { best = cost; for (int kk = 0; kk < J; kk++) { memcpy(BT[kk], T[kk], sizeof(int) * N); memcpy(BS[kk], S[kk], sizeof(int) * N); } }
    if ((it & 0xffff) == 0) fprintf(stderr, "it %lld T %.3f cost %lld best %lld\n", it, Tt, cost, best);
  }
  /* verify best from scratch */
  for (int kk = 0; kk < J; kk++) { memcpy(T[kk], BT[kk], sizeof(int) * N); memcpy(S[kk], BS[kk], sizeof(int) * N); for (int p = 0; p < N; p++) SI[kk][S[kk][p]] = p; }
  for (int x = 0; x < N; x++) X[x] = compX(x);
  for (int y = 0; y < N; y++) Y[y] = compY(y);
  long long c2 = 0; for (int x = 0; x < N; x++) c2 += rowcost(x);
  printf("q %d j %d M %d best_cost %lld (rechecked %lld)\n", q, J, M, best, c2);
  char fn[256]; snprintf(fn, sizeof fn, "gw_best_q%d_j%d_M%d.txt", q, J, M);
  FILE *o = fopen(fn, "w"); fprintf(o, "%d %d %d\n", N, J, M);
  for (int p = 0; p < N; p++) { for (int kk = 0; kk < J; kk++) fprintf(o, "%d %d ", S[kk][p], T[kk][p]); fprintf(o, "\n"); }
  fclose(o);
  return 0;
}
