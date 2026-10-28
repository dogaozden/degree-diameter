/* Card e03 (polylev r2): greedy family of pairwise disjoint totally singular lines of Q(6,q), q prime.
 * Quadric: Q(x) = x0x4 + x1x5 + x2x6 - x3^2, polar b(x,y) = x0y4+x4y0+x1y5+x5y1+x2y6+x6y2-2x3y3.
 * Points come from research/theorems/polylev/hex/hex_q<q>.bin (hexagon H(q); the points are all points of Q(6,q)).
 * For an uncovered point p:
 *   (a) the 14 hexagon lines through p (line = <p,x> for x collinear with p in H(q)) are tried first;
 *   (b) then T random non-backtracking walks p -> L1 -> x1 -> L2 -> x2 (x2 is at distance 4 from p, hence b(p,x2)=0),
 *       the line <p,x2> = {p, x2, p + l*x2 (l = 1..q-1)} (normalised) is taken if all its points are uncovered.
 * Coverage is a bitmap over all projective points of PG(6,q) (ranks). Output: header int32 q, int32 count, then
 * count * (q+1) * 7 bytes (normalised coordinates, each line's q+1 points consecutively).
 * Usage: greedy HEX OUT SEED0 NPASSES T WALL_SECONDS
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>

static int q;
static int64_t N, NL, NPG;
static int32_t *lines;   /* NL*(q+1) point ids */
static int32_t *pl;      /* N*(q+1) line ids through each point */
static uint8_t *co;      /* N*8 coordinates (7 used) */
static int32_t *rk;      /* N projective ranks */
static uint64_t *cov;    /* bitmap over projective ranks */
static int64_t off[7];
static int inv[64];

static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline int rndn(int n) { return (int)((rnd64() >> 11) % (uint64_t)n); }

static double now(void) {
  struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts);
  return ts.tv_sec + 1e-9 * ts.tv_nsec;
}

static inline int64_t rank_vec(const int *w) { /* w normalised */
  int k = 0; while (w[k] == 0) k++;
  int64_t acc = 0;
  for (int j = k + 1; j < 7; j++) acc = acc * q + w[j];
  return off[k] + acc;
}
static inline void normalize(int *w) {
  int k = 0; while (w[k] == 0) k++;
  int c = inv[w[k]];
  if (c != 1) for (int j = k; j < 7; j++) w[j] = (w[j] * c) % q;
}
static inline int covered(int64_t r) { return (cov[r >> 6] >> (r & 63)) & 1; }
static inline void setcov(int64_t r) { cov[r >> 6] |= (1ULL << (r & 63)); }

/* 1 iff the q-1 points P + l*X (l = 1..q-1) are all uncovered */
static int line_free_extra(const int *P, const int *X) {
  int y[7];
  memcpy(y, P, sizeof y);
  for (int l = 1; l < q; l++) {
    for (int j = 0; j < 7; j++) { int v = y[j] + X[j]; y[j] = v >= q ? v - q : v; }
    int w[7]; memcpy(w, y, sizeof w); normalize(w);
    if (covered(rank_vec(w))) return 0;
  }
  return 1;
}

static void take_constructed(const int *P, const int *X, uint8_t *dst) {
  int y[7];
  memcpy(y, P, sizeof y);
  setcov(rank_vec(P)); for (int j = 0; j < 7; j++) dst[j] = (uint8_t)P[j];
  setcov(rank_vec(X)); for (int j = 0; j < 7; j++) dst[7 + j] = (uint8_t)X[j];
  for (int l = 1; l < q; l++) {
    for (int j = 0; j < 7; j++) { int v = y[j] + X[j]; y[j] = v >= q ? v - q : v; }
    int w[7]; memcpy(w, y, sizeof w); normalize(w);
    setcov(rank_vec(w));
    for (int j = 0; j < 7; j++) dst[(l + 1) * 7 + j] = (uint8_t)w[j];
  }
}

static inline int32_t sample_x2(int32_t pi) {
  int Q1 = q + 1;
  int32_t L1 = pl[(int64_t)pi * Q1 + rndn(Q1)];
  int32_t x1;
  do { x1 = lines[(int64_t)L1 * Q1 + rndn(Q1)]; } while (x1 == pi);
  int32_t L2;
  do { L2 = pl[(int64_t)x1 * Q1 + rndn(Q1)]; } while (L2 == L1);
  int32_t x2;
  do { x2 = lines[(int64_t)L2 * Q1 + rndn(Q1)]; } while (x2 == x1);
  return x2;
}

static int64_t greedy(uint64_t seed, int T, double deadline, uint8_t *outbuf, int64_t cap, int *aborted) {
  int Q1 = q + 1;
  rs = seed * 0x9E3779B97F4A7C15ULL + 0x2545F4914F6CDD1DULL; if (!rs) rs = 1;
  for (int i = 0; i < 10; i++) rnd64();
  memset(cov, 0, (size_t)((NPG + 63) / 64) * 8);
  int32_t *perm = malloc((size_t)N * 4);
  for (int64_t i = 0; i < N; i++) perm[i] = (int32_t)i;
  for (int64_t i = N - 1; i > 0; i--) { int64_t j = (int64_t)(rnd64() % (uint64_t)(i + 1)); int32_t t = perm[i]; perm[i] = perm[j]; perm[j] = t; }
  int64_t nl = 0, fails = 0, tried = 0;
  *aborted = 0;
  for (int64_t idx = 0; idx < N; idx++) {
    int32_t pi = perm[idx];
    if (covered(rk[pi])) continue;
    if ((idx & 1023) == 0 && now() > deadline) { *aborted = 1; break; }
    tried++;
    int done = 0;
    /* (a) hexagon lines through p */
    for (int t = 0; t < Q1 && !done; t++) {
      int32_t L1 = pl[(int64_t)pi * Q1 + t];
      int ok = 1;
      for (int s = 0; s < Q1; s++) if (covered(rk[lines[(int64_t)L1 * Q1 + s]])) { ok = 0; break; }
      if (!ok) continue;
      if (nl >= cap) { *aborted = 2; break; }
      uint8_t *dst = outbuf + nl * Q1 * 7;
      for (int s = 0; s < Q1; s++) {
        int32_t pt = lines[(int64_t)L1 * Q1 + s];
        setcov(rk[pt]);
        memcpy(dst + s * 7, co + (int64_t)pt * 8, 7);
      }
      nl++; done = 1;
    }
    /* (b) random walks p -> L1 -> x1 -> L2 -> x2 */
    int P[7];
    for (int j = 0; j < 7; j++) P[j] = co[(int64_t)pi * 8 + j];
    for (int t = 0; t < T && !done; t++) {
      int32_t x2 = sample_x2(pi);
      if (covered(rk[x2])) continue;
      int X[7];
      for (int j = 0; j < 7; j++) X[j] = co[(int64_t)x2 * 8 + j];
      if (!line_free_extra(P, X)) continue;
      if (nl >= cap) { *aborted = 2; break; }
      take_constructed(P, X, outbuf + nl * Q1 * 7);
      nl++; done = 1;
    }
    if (*aborted == 2) break;
    if (!done) fails++;
  }
  (void)fails; (void)tried;
  free(perm);
  return nl;
}

static int write_out(const char *path, const uint8_t *buf, int64_t count) {
  char tmp[4096]; snprintf(tmp, sizeof tmp, "%s.tmp", path);
  FILE *f = fopen(tmp, "wb"); if (!f) return -1;
  int32_t hdr[2] = { q, (int32_t)count };
  fwrite(hdr, 4, 2, f);
  fwrite(buf, 1, (size_t)count * (q + 1) * 7, f);
  fclose(f);
  return rename(tmp, path);
}

int main(int argc, char **argv) {
  if (argc < 7) { fprintf(stderr, "usage: greedy HEX OUT SEED0 NPASSES T WALL_SECONDS\n"); return 1; }
  const char *hexp = argv[1], *outp = argv[2];
  uint64_t seed0 = strtoull(argv[3], 0, 10);
  int npass = atoi(argv[4]), T = atoi(argv[5]);
  double wall = atof(argv[6]);
  double t0 = now(), deadline = t0 + wall;

  FILE *f = fopen(hexp, "rb"); if (!f) { perror("hex"); return 1; }
  int32_t hdr[3];
  if (fread(hdr, 4, 3, f) != 3) return 1;
  q = hdr[0]; N = hdr[1]; NL = hdr[2];
  lines = malloc((size_t)NL * (q + 1) * 4);
  if (fread(lines, 4, (size_t)NL * (q + 1), f) != (size_t)NL * (q + 1)) { fprintf(stderr, "short read lines\n"); return 1; }
  uint8_t *cc = malloc((size_t)N * 7);
  if (fread(cc, 1, (size_t)N * 7, f) != (size_t)N * 7) { fprintf(stderr, "short read coords\n"); return 1; }
  fclose(f);
  int Q1 = q + 1;
  co = calloc((size_t)N * 8, 1);
  for (int64_t i = 0; i < N; i++) memcpy(co + i * 8, cc + i * 7, 7);
  free(cc);

  /* field inverses (q prime) */
  for (int a = 1; a < q; a++) for (int b = 1; b < q; b++) if ((a * b) % q == 1) inv[a] = b;

  /* ranks */
  { int64_t pw[7]; pw[0] = 1; for (int i = 1; i < 7; i++) pw[i] = pw[i - 1] * q; /* pw[i] = q^i */
    /* block for pivot k has q^(6-k) points */
    off[0] = 0;
    for (int k = 1; k < 7; k++) off[k] = off[k - 1] + pw[7 - k];
    NPG = off[6] + pw[0];
  }
  rk = malloc((size_t)N * 4);
  uint8_t *seen = calloc((size_t)NPG / 8 + 8, 1);
  int64_t bad = 0;
  for (int64_t i = 0; i < N; i++) {
    int w[7]; for (int j = 0; j < 7; j++) w[j] = co[i * 8 + j];
    int k = 0; while (k < 7 && w[k] == 0) k++;
    if (k == 7 || w[k] != 1) { bad++; }
    int64_t r = rank_vec(w);
    rk[i] = (int32_t)r;
    if (seen[r >> 3] >> (r & 7) & 1) bad++;
    seen[r >> 3] |= (uint8_t)(1 << (r & 7));
    int Qv = (w[0] * w[4] + w[1] * w[5] + w[2] * w[6] - w[3] * w[3]) % q;
    if (((Qv % q) + q) % q != 0) bad++;
  }
  free(seen);
  if (bad) { fprintf(stderr, "point table check failed: %lld\n", (long long)bad); return 1; }

  /* lines through each point */
  int32_t *cnt = calloc((size_t)N, 4);
  pl = malloc((size_t)N * Q1 * 4);
  for (int64_t li = 0; li < NL; li++)
    for (int s = 0; s < Q1; s++) {
      int32_t pt = lines[li * Q1 + s];
      if (cnt[pt] >= Q1) { fprintf(stderr, "point on too many lines\n"); return 1; }
      pl[(int64_t)pt * Q1 + cnt[pt]++] = (int32_t)li;
    }
  for (int64_t i = 0; i < N; i++) if (cnt[i] != Q1) { fprintf(stderr, "point %lld has %d lines\n", (long long)i, cnt[i]); return 1; }
  free(cnt);
  cov = malloc((size_t)((NPG + 63) / 64) * 8);
  int64_t cap = N / Q1 + 16;
  uint8_t *outbuf = malloc((size_t)cap * Q1 * 7);
  uint8_t *best = malloc((size_t)cap * Q1 * 7);
  fprintf(stderr, "loaded q=%d N=%lld L=%lld NPG=%lld load %.1fs\n", q, (long long)N, (long long)NL, (long long)NPG, now() - t0);

  int64_t bestn = -1;
  for (int pass = 0; pass < npass && now() < deadline; pass++) {
    uint64_t seed = seed0 + pass;
    double ts = now(); int ab = 0;
    int64_t n = greedy(seed, T, deadline, outbuf, cap, &ab);
    fprintf(stderr, "pass %d seed %llu T %d lines %lld (bound %lld, %.2f%%) time %.1fs%s\n", pass, (unsigned long long)seed, T,
            (long long)n, (long long)(N / Q1), 100.0 * n / (double)(N / Q1), now() - ts, ab ? " [stopped early]" : "");
    if (n > bestn) {
      bestn = n; memcpy(best, outbuf, (size_t)n * Q1 * 7);
      if (write_out(outp, best, n)) { fprintf(stderr, "write failed\n"); return 1; }
      fprintf(stderr, "  saved best %lld to %s\n", (long long)n, outp);
    }
  }
  printf("best %lld\n", (long long)bestn);
  return 0;
}
