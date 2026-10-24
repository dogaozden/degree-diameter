/* anneal_perm.c: anneal a bijection s: points -> lines of H(q) minimising anti-homomorphism violations
 *   cost(s) = #{ {p,x} : 0 < dP(p,x) <= 4 and dL(s p, s x) in {2,4} }   (close points must go to opposite lines, dL = 6)
 * usage: anneal_perm dist.bin N iters T0 T1 seed out.txt
 * dist.bin: raw uint8, N*N bytes point-point distances then N*N bytes line-line distances (line index 0..N-1).
 * out.txt: line index of each point (one per line). Prints the best cost and the number of hops that are incidences.
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>

static uint64_t rs;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline double urand(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

int main(int argc, char **argv) {
  if (argc < 8) { fprintf(stderr, "usage: anneal_perm dist.bin N iters T0 T1 seed out.txt\n"); return 1; }
  int N = atoi(argv[2]); long long iters = atoll(argv[3]);
  double T0 = atof(argv[4]), T1 = atof(argv[5]);
  rs = 88172645463325252ULL ^ ((uint64_t)atoll(argv[6]) * 0x9E3779B97F4A7C15ULL);
  if (!rs) rs = 1;
  for (int i = 0; i < 20; i++) rnd();
  FILE *f = fopen(argv[1], "rb");
  if (!f) { perror("dist"); return 1; }
  uint8_t *DP = malloc((size_t)N * N), *DL = malloc((size_t)N * N);
  if (fread(DP, 1, (size_t)N * N, f) != (size_t)N * N || fread(DL, 1, (size_t)N * N, f) != (size_t)N * N) { fprintf(stderr, "short read\n"); return 1; }
  fclose(f);
  uint8_t *AP = malloc((size_t)N * N), *AL = malloc((size_t)N * N);
  for (long i = 0; i < (long)N * N; i++) { AP[i] = (DP[i] == 2 || DP[i] == 4); AL[i] = (DL[i] == 2 || DL[i] == 4); }
  int *perm = malloc(sizeof(int) * N), *best = malloc(sizeof(int) * N);
  for (int i = 0; i < N; i++) perm[i] = i;
  for (int i = N - 1; i > 0; i--) { int j = rnd() % (i + 1); int t = perm[i]; perm[i] = perm[j]; perm[j] = t; }
  long long cost = 0;
  for (int p = 0; p < N; p++) for (int x = p + 1; x < N; x++) cost += AP[(long)p * N + x] * AL[(long)perm[p] * N + perm[x]];
  long long bestc = cost; memcpy(best, perm, sizeof(int) * N);
  long long acc = 0;
  for (long long it = 0; it < iters; it++) {
    double T = T0 * pow(T1 / T0, (double)it / (double)iters);
    int p1 = rnd() % N, p2 = rnd() % N;
    if (p1 == p2) continue;
    int a = perm[p1], b = perm[p2];
    const uint8_t *ap1 = AP + (long)p1 * N, *ap2 = AP + (long)p2 * N;
    const uint8_t *alA = AL + (long)a * N, *alB = AL + (long)b * N;
    long long d = 0;
    for (int x = 0; x < N; x++) {
      if (x == p1 || x == p2) continue;
      int dx = (int)ap1[x] - (int)ap2[x];
      if (dx == 0) continue;
      int px = perm[x];
      d += dx * ((int)alB[px] - (int)alA[px]);
    }
    if (d <= 0 || urand() < exp(-(double)d / T)) {
      perm[p1] = b; perm[p2] = a; cost += d; acc++;
      if (cost < bestc) { bestc = cost; memcpy(best, perm, sizeof(int) * N); }
    }
  }
  /* independent recount of the best permutation */
  long long chk = 0;
  for (int p = 0; p < N; p++) for (int x = p + 1; x < N; x++) chk += AP[(long)p * N + x] * AL[(long)best[p] * N + best[x]];
  FILE *g = fopen(argv[7], "w");
  for (int i = 0; i < N; i++) fprintf(g, "%d\n", best[i]);
  fclose(g);
  printf("N %d iters %lld acc %lld best_cost %lld recount %lld\n", N, iters, acc, bestc, chk);
  return 0;
}
