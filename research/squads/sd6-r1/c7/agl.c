/* c7 wildcard: Haar graphs H(G,S), G = AGL(1,q) = {x -> u x + v : u in F_q^*, v in F_q}, |S| = 7, N = q(q-1).
 * Condition (even D=6): S S^-1 S S^-1 S = G. uncovered = N - |{s1 s2^-1 s3 s4^-1 s5}|.
 * Element encoding: idx = (u-1)*q + v. Product (u1,v1)(u2,v2) = (u1 u2, u1 v2 + v1).
 * Modes:
 *   0 random: uniform random 7-sets, report the distribution (baseline)
 *   1 poly:   for random multiplier sets {u_i}, exhaustive v_i = a0 + a1 u_i + a2 u_i^2 (structured family)
 *   2 sa:     simulated annealing over general S (both u and v free), restarts until time is up
 * usage: agl q mode seconds seed nsets
 * Prints BEST uncovered and the S as "u:v" pairs (group elements), then "END".
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <math.h>

static int q, N, K = 7;
static int *stamp;
static int stampv = 0;
static int invu[4096];
static unsigned short *MT = NULL; static int *IV = NULL;
static unsigned long long rs = 88172645463325252ULL;

static inline unsigned long long xr(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline int rnd(int n) { return (int)(xr() % (unsigned long long)n); }
static inline int enc(int u, int v) { return (u - 1) * q + v; }
static inline int eu(int e) { return e / q + 1; }
static inline int ev(int e) { return e % q; }
static inline int gmul_raw(int a, int b) {
  int u1 = eu(a), v1 = ev(a), u2 = eu(b), v2 = ev(b);
  return enc(u1 * u2 % q, (u1 * v2 + v1) % q);
}
static int MM[128][128], MV[128][128], ADD[128][128];
static inline int gmul(int a, int b) {
  int u1 = eu(a), v1 = ev(a), u2 = eu(b), v2 = ev(b);
  int ru = MM[u1][u2];
  int rv = ADD[MV[u1][v2]][v1];
  return (ru - 1) * q + rv;
}
static inline int ginv(int a) { return IV[a]; }

/* uncovered count of S S^-1 S S^-1 S in G */
static int uncovered(const int *S) {
  int I[7], cnt = 0;
  for (int i = 0; i < K; i++) I[i] = ginv(S[i]);
  stampv++;
  for (int a = 0; a < K; a++)
    for (int b = 0; b < K; b++) {
      int p2 = gmul(S[a], I[b]);
      for (int c = 0; c < K; c++) {
        int p3 = gmul(p2, S[c]);
        for (int d = 0; d < K; d++) {
          int p4 = gmul(p3, I[d]);
          for (int e = 0; e < K; e++) {
            int p5 = gmul(p4, S[e]);
            if (stamp[p5] != stampv) { stamp[p5] = stampv; cnt++; }
          }
        }
      }
    }
  return N - cnt;
}

static int distinct(const int *S) {
  for (int i = 0; i < K; i++) for (int j = i + 1; j < K; j++) if (S[i] == S[j]) return 0;
  return 1;
}

static void printS(const char *tag, const int *S, int unc) {
  printf("%s uncovered=%d S=", tag, unc);
  for (int i = 0; i < K; i++) printf("%s%d:%d", i ? " " : "", eu(S[i]), ev(S[i]));
  printf("\n");
}

static int primeq(int x) { if (x < 2) return 0; for (int d = 2; d * d <= x; d++) if (x % d == 0) return 0; return 1; }

int main(int argc, char **argv) {
  if (argc < 5) { fprintf(stderr, "usage: agl q mode seconds seed [nsets]\n"); return 1; }
  q = atoi(argv[1]);
  int mode = atoi(argv[2]);
  double secs = atof(argv[3]);
  rs ^= (unsigned long long)atoll(argv[4]) * 0x9E3779B97F4A7C15ULL;
  int nsets = argc > 5 ? atoi(argv[5]) : 10;
  if (!primeq(q)) { fprintf(stderr, "q must be prime\n"); return 1; }
  N = q * (q - 1);
  stamp = calloc(N, sizeof(int));
  for (int u = 1; u < q; u++) for (int w = 1; w < q; w++) if (u * w % q == 1) invu[u] = w;
  for (int a = 0; a < q; a++) for (int b = 0; b < q; b++) { ADD[a][b] = (a + b) % q; }
  for (int a = 1; a < q; a++) for (int b = 1; b < q; b++) MM[a][b] = a * b % q;
  for (int a = 1; a < q; a++) for (int b = 0; b < q; b++) MV[a][b] = a * b % q;
  IV = malloc(N * sizeof(int));
  for (int a = 0; a < N; a++) { IV[a] = 0; }
  for (int a = 0; a < N; a++) { int u = eu(a), v = ev(a), ui = invu[u]; IV[a] = enc(ui, (q - (ui * v) % q) % q); }
  for (int a = 0; a < N; a++) for (int b = 0; b < N; b++) if (gmul_raw(a, b) != gmul(a, b)) { fprintf(stderr, "table mismatch\n"); return 1; }
  time_t t0 = time(NULL);
  int best = 1 << 30, bestS[7];
  long long evals = 0;

  if (mode == 0) {
    /* uniform random S: distribution of uncovered counts */
    int hist_min = 1 << 30, sum = 0, runs = 0;
    while (difftime(time(NULL), t0) < secs) {
      int S[7];
      for (int i = 0; i < K; i++) {
        int e;
        do { e = rnd(N); } while (0);
        S[i] = e;
      }
      if (!distinct(S)) continue;
      int u = uncovered(S);
      evals++; runs++; sum += u;
      if (u < hist_min) hist_min = u;
      if (u < best) { best = u; memcpy(bestS, S, sizeof S); }
    }
    printf("random: runs=%d mean=%.1f min=%d\n", runs, runs ? (double)sum / runs : 0.0, hist_min);
  } else if (mode == 1) {
    /* structured: v_i = a0 + a1 u_i + a2 u_i^2 over F_q, multipliers u_i from a random distinct set */
    for (int set = 0; set < nsets && difftime(time(NULL), t0) < secs; set++) {
      int us[7], used[4096];
      memset(used, 0, sizeof used);
      for (int i = 0; i < K;) { int u = 1 + rnd(q - 1); if (!used[u]) { used[u] = 1; us[i++] = u; } }
      int setbest = 1 << 30, sb[7];
      for (int a0 = 0; a0 < q; a0++)
        for (int a1 = 0; a1 < q; a1++)
          for (int a2 = 0; a2 < q; a2++) {
            int S[7];
            for (int i = 0; i < K; i++) {
              int u = us[i];
              int v = (a0 + a1 * u + a2 * u * u) % q;
              S[i] = enc(u, v);
            }
            int un = uncovered(S);
            evals++;
            if (un < setbest) { setbest = un; memcpy(sb, S, sizeof S); }
          }
      printf("set %d multipliers", set);
      for (int i = 0; i < K; i++) printf(" %d", us[i]);
      printf(" -> best quadratic-family uncovered=%d\n", setbest);
      if (setbest < best) { best = setbest; memcpy(bestS, sb, sizeof sb); }
      if (best == 0) break;
    }
  } else {
    /* simulated annealing over general S (u and v free) with restarts */
    while (difftime(time(NULL), t0) < secs && best > 0) {
      int S[7];
      for (int i = 0; i < K; ) {
        int e = rnd(N); int ok = 1;
        for (int j = 0; j < i; j++) if (S[j] == e) ok = 0;
        if (ok) S[i++] = e;
      }
      int cur = uncovered(S);
      double T0 = 6.0, T1 = 0.3;
      long long steps = 40000;
      for (long long st = 0; st < steps && difftime(time(NULL), t0) < secs; st++) {
        double T = T0 * pow(T1 / T0, (double)st / steps);
        int i = rnd(K), old = S[i];
        int e = rnd(N), ok = 1;
        for (int j = 0; j < K; j++) if (S[j] == e) ok = 0;
        if (!ok) continue;
        S[i] = e;
        int nu = uncovered(S);
        evals++;
        if (nu <= cur || exp(-(nu - cur) / T) > (double)(xr() % 1000000) / 1e6) {
          cur = nu;
          if (cur < best) { best = cur; memcpy(bestS, S, sizeof S); }
          if (best == 0) break;
        } else S[i] = old;
      }
    }
  }
  printf("q=%d N=%d mode=%d evals=%lld secs=%.0f\n", q, N, mode, evals, difftime(time(NULL), t0));
  printS("BEST", bestS, best);
  printf("END\n");
  return 0;
}
