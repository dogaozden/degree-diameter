/* c16: 2+2 voltage lifts over SL(2,p) (base = K_{2,2} with k voltages per pair), versus the Haar case (m = 1).
 * Graph: vertices (A_i,g), (B_j,h), g,h in SL(2,p), 2m|G| vertices. Edge (A_i,g)-(B_j,g*v) for v in V_ij.
 * Left multiplication by SL(2,p) is an automorphism, so diameter <= D iff BFS from (A_i,I) and (B_j,I) reaches all.
 * cost = number of (source, vertex) pairs at distance > D, summed over the 2m sources.
 * usage: lift2 m k p D SECONDS SEED OUT
 *   m = 1: Haar graph H(SL(2,p), S), |S| = k (degree k).   m = 2: 2+2 lift, degree 2k.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef struct { int a, b, c, d; } Mx;
static int P, M, K, D;
static long PP4, NG;
static uint64_t rs;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline Mx dec(long code) {
  Mx x; x.d = (int)(code % P); code /= P; x.c = (int)(code % P); code /= P; x.b = (int)(code % P); x.a = (int)(code / P);
  return x;
}
static inline long enc(Mx x) { return (((long)x.a * P + x.b) * P + x.c) * P + x.d; }
static inline Mx mul(Mx x, Mx y) {
  Mx r;
  r.a = (x.a * y.a + x.b * y.c) % P; r.b = (x.a * y.b + x.b * y.d) % P;
  r.c = (x.c * y.a + x.d * y.c) % P; r.d = (x.c * y.b + x.d * y.d) % P;
  return r;
}
static inline Mx inv(Mx x) { Mx r; r.a = x.d; r.b = (P - x.b) % P; r.c = (P - x.c) % P; r.d = x.a; return r; }

static Mx vol[2][2][64], vinv[2][2][64];
static uint32_t *stamp, cur = 0;
static uint32_t *qa, *qb;

static Mx randsl(void) {
  for (;;) {
    Mx x; x.a = rnd() % P; x.b = rnd() % P; x.c = rnd() % P; x.d = rnd() % P;
    if (((long)x.a * x.d - (long)x.b * x.c) % P == 1 || ((long)x.a * x.d - (long)x.b * x.c) % P == 1 - P)
      return x;
  }
}
static int tdet(Mx x) { long t = ((long)x.a * x.d - (long)x.b * x.c) % P; if (t < 0) t += P; return t == 1; }

static long eval(void) {
  long cost = 0;
  long N = 2L * M * NG;
  for (int t0 = 0; t0 < 2 * M; t0++) {
    Mx I = {1, 0, 0, 1};
    long code0 = (long)t0 * PP4 + enc(I);
    cur++;
    long nq = 0, reached = 1;
    uint32_t *fr = qa, *nx = qb;
    long nf = 1; fr[0] = (uint32_t)code0; stamp[code0] = cur;
    for (int depth = 1; depth <= D && nf > 0; depth++) {
      long nn = 0;
      for (long q = 0; q < nf; q++) {
        long code = fr[q];
        int t = (int)(code / PP4);
        Mx g = dec(code % PP4);
        if (t < M) {
          for (int j = 0; j < M; j++)
            for (int kk = 0; kk < K; kk++) {
              Mx y = mul(g, vol[t][j][kk]);
              long id = (long)(M + j) * PP4 + enc(y);
              if (stamp[id] != cur) { stamp[id] = cur; nx[nn++] = (uint32_t)id; }
            }
        } else {
          int j = t - M;
          for (int i = 0; i < M; i++)
            for (int kk = 0; kk < K; kk++) {
              Mx y = mul(g, vinv[i][j][kk]);
              long id = (long)i * PP4 + enc(y);
              if (stamp[id] != cur) { stamp[id] = cur; nx[nn++] = (uint32_t)id; }
            }
        }
      }
      reached += nn;
      uint32_t *tmp = fr; fr = nx; nx = tmp; nf = nn;
    }
    (void)nq;
    cost += N - reached;
  }
  return cost;
}

int main(int argc, char **argv) {
  if (argc < 8) { fprintf(stderr, "usage: lift2 m k p D SECONDS SEED OUT\n"); return 1; }
  M = atoi(argv[1]); K = atoi(argv[2]); P = atoi(argv[3]); D = atoi(argv[4]);
  double secs = atof(argv[5]); rs = strtoull(argv[6], 0, 10) * 2654435761ULL + 88172645463325252ULL;
  const char *out = argv[7];
  PP4 = (long)P * P * P * P; NG = (long)P * (P * P - 1);
  stamp = calloc(2L * M * PP4, sizeof(uint32_t));
  qa = malloc(sizeof(uint32_t) * 2L * M * PP4); qb = malloc(sizeof(uint32_t) * 2L * M * PP4);
  if (!stamp || !qa || !qb) { fprintf(stderr, "alloc\n"); return 1; }
  for (int i = 0; i < M; i++) for (int j = 0; j < M; j++) for (int kk = 0; kk < K; kk++) {
    vol[i][j][kk] = randsl();
  }
  for (int i = 0; i < M; i++) for (int j = 0; j < M; j++) for (int kk = 0; kk < K; kk++) vinv[i][j][kk] = inv(vol[i][j][kk]);
  long cost = eval(), best = cost, evals = 1;
  clock_t t0 = clock();
  double T = 0;
  fprintf(stderr, "init cost=%ld N=%ld\n", cost, 2L * M * NG);
  while (cost > 0) {
    double el = (double)(clock() - t0) / CLOCKS_PER_SEC;
    if (el > secs) break;
    int i = rnd() % M, j = rnd() % M, kk = rnd() % K;
    Mx old = vol[i][j][kk], oldi = vinv[i][j][kk];
    Mx y; int ok;
    do {
      y = randsl(); ok = 1;
      for (int q = 0; q < K; q++) if (q != kk && memcmp(&vol[i][j][q], &y, sizeof(Mx)) == 0) ok = 0;
    } while (!ok);
    vol[i][j][kk] = y; vinv[i][j][kk] = inv(y);
    long c2 = eval(); evals++;
    if (c2 <= cost || (rnd() % 1000) < 3) { cost = c2; }
    else { vol[i][j][kk] = old; vinv[i][j][kk] = oldi; }
    if (cost < best) { best = cost; fprintf(stderr, "t=%.0f evals=%ld cost=%ld best=%ld\n", el, evals, cost, best); }
  }
  double el = (double)(clock() - t0) / CLOCKS_PER_SEC;
  printf("m=%d k=%d p=%d D=%d N=%ld best=%ld final=%ld evals=%ld time=%.1f\n", M, K, P, D, 2L * M * NG, best, cost, evals, el);
  if (cost == 0) {
    FILE *f = fopen(out, "w");
    fprintf(f, "# m=%d k=%d p=%d D=%d; vertices (A_i,g) id i*G+idx, (B_j,g) id (m+j)*G+idx; SL(2,p) elems as a b c d\n", M, K, P, D);
    for (int i = 0; i < M; i++) for (int j = 0; j < M; j++) for (int kk = 0; kk < K; kk++)
      fprintf(f, "V %d %d %d %d %d %d %d\n", i, j, vol[i][j][kk].a, vol[i][j][kk].b, vol[i][j][kk].c, vol[i][j][kk].d, kk);
    fclose(f);
    printf("FOUND cost 0 written to %s\n", out);
  }
  return 0;
}
