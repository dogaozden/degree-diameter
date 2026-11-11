/* a09: Haar-graph evaluator for meta groups Z_m x|_r Z_k, elements (a,j) index a*k+j, product (a,j)(b,l)=(a+r^j b, j+l).
 * usage: hb STATEFILE            -> prints cost (#B-elements not within D-1=11 of (e,A)) and uncovered list
 *        hb STATEFILE -gen "a j"  (optional extra replacement: env REPL="idx a j" replaces generator idx) */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
typedef long long ll;
static ll M, K, R_[128];
static int D = 12; static int DROP = -1;
static int nS; static ll SA[16], SJ[16];      /* generators (a,j) */
static inline ll mulg(ll c, ll i, ll g) {     /* s*g, s=(c,i), g index */
  ll a = g / K, j = g % K;
  return ((c + R_[i] * a) % M) * K + ((i + j) % K);
}
static inline ll invg(ll c, ll i) {           /* index of s^{-1} */
  ll jj = (K - i) % K; ll b = (M - (R_[jj] * c) % M) % M; return b * K + jj;
}
int main(int argc, char **argv) {
  FILE *f = fopen(argv[1], "r"); if (!f) return 2;
  char line[512]; ll m, k, r; int d, DD, n, NN; ll N;
  if (!fgets(line, sizeof line, f)) return 3;
  char spec[128]; int cost0;
  /* header: "6 12 meta 74719 63 37726 n 1 N 4707297 cost 1" */
  sscanf(line, "%d %d meta %lld %lld %lld", &d, &DD, &M, &K, &r);
  D = DD;
  R_[0] = 1 % M; for (int j = 1; j < K; j++) R_[j] = R_[j-1] * r % M;
  nS = 0;
  while (fgets(line, sizeof line, f)) {
    ll a, j; if (sscanf(line, "%*d meta(a=%lld,j=%lld)", &a, &j) == 2) { SA[nS] = a; SJ[nS] = j; nS++; }
  }
  fclose(f);
  /* optional replacement: REPL="idx a j" */
  if (getenv("REPL")) { int idx; ll a, j; sscanf(getenv("REPL"), "%d %lld %lld", &idx, &a, &j); SA[idx] = a; SJ[idx] = j; }
  if (getenv("DROP")) DROP = atoi(getenv("DROP"));
  N = M * K;
  ll *Cc = malloc(sizeof(ll) * nS), *Ci = malloc(sizeof(ll) * nS);
  for (int s = 0; s < nS; s++) { Cc[s] = SA[s]; Ci[s] = SJ[s]; }
  ll V = 2 * N;
  unsigned char *dist = malloc(V); memset(dist, 255, V);
  uint32_t *q = malloc(sizeof(uint32_t) * V);
  ll h = 0, t = 0; dist[0] = 0; q[t++] = 0;
  while (h < t) {
    uint32_t v = q[h++]; ll g = v >> 1; int side = v & 1; unsigned char dv = dist[v];
    if (dv >= D - 1) continue;
    if (side == 0) {           /* (g,A) -> (s g, B) */
      for (int s = 0; s < nS; s++) { if (s == DROP) continue; ll w = 2 * mulg(Cc[s], Ci[s], g) + 1; if (dist[w] == 255) { dist[w] = dv + 1; q[t++] = (uint32_t)w; } }
    } else {                   /* (g,B) -> (s^-1 g, A) */
      for (int s = 0; s < nS; s++) { if (s == DROP) continue; ll ig = invg(Cc[s], Ci[s]); ll ic = ig / K, ii = ig % K;
        ll w = 2 * mulg(ic, ii, g); if (dist[w] == 255) { dist[w] = dv + 1; q[t++] = (uint32_t)w; } }
    }
  }
  ll cost = 0, maxd = 0;
  for (ll g = 0; g < N; g++) { unsigned char x = dist[2 * g + 1]; if (x == 255 || x > D - 1) { cost++; if (cost <= 40) printf("UNC g=%lld (a=%lld,j=%lld)\n", g, g / K, g % K); } }
  printf("N=%lld nS=%d cost=%lld\n", N, nS, cost);
  return 0;
}
