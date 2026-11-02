/* f04: Frobenius group G = Z_P x|_r Z_K, element (a,j) = a*K+j, (a,j)(b,l) = (a + r^j b, j+l).
 * Haar graph: A-vertex g ~ B-vertex s g for s in S (|S| = ND, S[0] = e).
 * cost = #A not within 8 of (e,A) + #B not within 8 of (e,B) (haar_gen3 odd-D cost).
 * modes: anat STATE            -> uncovered elements and classification
 *        scan STATE POS LO HI OUT -> swap S[POS] by x in [LO,HI), report x with cost < base, and cost stats. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#define ND 6
static int P, K, R_[64], r_, N;
static int S[ND];
static int *Lt, *Lit, *q; static uint8_t *dist;
static inline int gmul(int x, int y) {
  int a = x / K, j = x - a * K, b = y / K, l = y - b * K;
  int c = (a + (R_[j] * b) % P) % P;
  int jj = j + l; if (jj >= K) jj -= K;
  return c * K + jj;
}
static inline int ginv(int x) {
  int a = x / K, j = x - a * K; int jj = (K - j) % K;
  int b = (P - (R_[jj] * a) % P) % P;
  return b * K + jj;
}
static void bfs(int src, int maxd) {
  memset(dist, 255, 2 * N);
  int h = 0, t = 0; q[t++] = src; dist[src] = 0;
  while (h < t) {
    int v = q[h++]; int dv = dist[v]; if (dv >= maxd) continue;
    if (v < N) {
      for (int i = 0; i < ND; i++) { int w = N + Lt[i * N + v]; if (dist[w] == 255) { dist[w] = dv + 1; q[t++] = w; } }
    } else {
      int h0 = v - N;
      for (int i = 0; i < ND; i++) { int w = Lit[i * N + h0]; if (dist[w] == 255) { dist[w] = dv + 1; q[t++] = w; } }
    }
  }
}
static void row_fast(int x, int *out) {
  int ax = x / K, jx = x - ax * K;
  int t = ax;
  for (int b = 0; b < P; b++) {
    int base = b * K; int jl = jx;
    for (int l = 0; l < K; l++) { out[base + l] = t * K + jl; jl++; if (jl == K) jl = 0; }
    t += R_[jx]; if (t >= P) t -= P;
  }
}
static void build_rows(int pos, int x) {
  row_fast(x, Lt + pos * N); row_fast(ginv(x), Lit + pos * N);
}
static int read_state(const char *fn) {
  FILE *f = fopen(fn, "r"); if (!f) { perror(fn); exit(1); }
  char line[512]; if (!fgets(line, sizeof line, f)) exit(1);
  int d, D; char spec[32]; int n, nn; long long NN; int cost;
  char nm[32];
  /* "6 9 meta 2551 25 2401 n 1 N 63775 cost 6" */
  char tok[20][32]; int ntok = 0; char *s = strtok(line, " \n");
  while (s && ntok < 20) { strcpy(tok[ntok++], s); s = strtok(NULL, " \n"); }
  P = atoi(tok[3]); K = atoi(tok[4]); r_ = atoi(tok[5]);
  N = P * K; R_[0] = 1 % P; for (int j = 1; j < K; j++) R_[j] = (int)((long long)R_[j - 1] * r_ % P);
  for (int i = 0; i < ND; i++) {
    int idx; char desc[64], z[16];
    if (fscanf(f, "%d %63s %15s", &idx, desc, z) != 3) { fprintf(stderr, "bad state\n"); exit(1); }
    S[i] = idx;
  }
  fclose(f);
  return 0;
}
static void setup_tables(void) {
  Lt = malloc(sizeof(int) * ND * N); Lit = malloc(sizeof(int) * ND * N);
  for (int i = 0; i < ND; i++) { int xi = ginv(S[i]);
    for (int g = 0; g < N; g++) { Lt[i * N + g] = gmul(S[i], g); Lit[i * N + g] = gmul(xi, g); } }
  q = malloc(sizeof(int) * 2 * N); dist = malloc(2 * N);
}
static int cost_of(int *ca, int *cb) {
  bfs(0, 8); int c1 = 0; for (int g = 0; g < N; g++) if (dist[g] > 8) c1++;
  *ca = c1; if (c1 >= 6) return c1;
  bfs(N, 8); int c2 = 0; for (int h = N; h < 2 * N; h++) if (dist[h] > 8) c2++;
  *cb = c2; return c1 + c2;
}
static int full_ok(void) {   /* ecc(e,A) <= 9 and ecc(e,B) <= 9 */
  bfs(0, 9); for (int v = 0; v < 2 * N; v++) if (dist[v] == 255) return 0;
  bfs(N, 9); for (int v = 0; v < 2 * N; v++) if (dist[v] == 255) return 0;
  return 1;
}
int main(int argc, char **argv) {
  if (argc < 3) { fprintf(stderr, "usage: anat STATE | scan STATE POS LO HI OUT\n"); return 1; }
  read_state(argv[2]); setup_tables();
  if (!strcmp(argv[1], "anat")) {
    int ca, cb; int c = cost_of(&ca, &cb);
    printf("P=%d K=%d r=%d N=%d S:", P, K, r_, N); for (int i = 0; i < ND; i++) printf(" %d(a=%d,j=%d)", S[i], S[i] / K, S[i] % K); printf("\n");
    /* uncovered sets, full BFS to depth 8 (plus exact dists for report) */
    bfs(0, 8); int uA[4096], nA = 0; for (int g = 0; g < N; g++) if (dist[g] > 8) uA[nA++] = g;
    bfs(N, 8); int uB[4096], nB = 0; for (int h = N; h < 2 * N; h++) if (dist[h] > 8) uB[nB++] = h - N;
    printf("cost=%d (A %d, B %d)\n", c, ca, cb);
    /* exact eccentricities with unbounded depth */
    bfs(0, 1000); int eA = 0; for (int v = 0; v < 2 * N; v++) if (dist[v] != 255 && dist[v] > eA) eA = dist[v];
    int unA = 0; for (int v = 0; v < 2 * N; v++) if (dist[v] == 255) unA++;
    printf("ecc(e,A)=%d unreached=%d\n", eA, unA);
    bfs(N, 1000); int eB = 0; for (int v = 0; v < 2 * N; v++) if (dist[v] != 255 && dist[v] > eB) eB = dist[v];
    printf("ecc(e,B)=%d\n", eB);
    printf("uncovered A (dist>8 from (e,A)), n=%d:\n", nA);
    for (int i = 0; i < nA; i++) { int g = uA[i]; int ig = ginv(g); int inS = 0; for (int s = 0; s < ND; s++) if (S[s] == g) inS = 1;
      printf("  g=%d (a=%d,j=%d) inv=%d(a=%d,j=%d) %s\n", g, g / K, g % K, ig, ig / K, ig % K, g == 0 ? "identity" : (g % K == 0 ? "kernel-Zp" : "")); }
    printf("uncovered B (dist>8 from (e,B)), n=%d:\n", nB);
    for (int i = 0; i < nB; i++) { int g = uB[i]; int ig = ginv(g);
      printf("  g=%d (a=%d,j=%d) inv=%d(a=%d,j=%d) %s\n", g, g / K, g % K, ig, ig / K, ig % K, g == 0 ? "identity" : (g % K == 0 ? "kernel-Zp" : "")); }
    return 0;
  }
  if (!strcmp(argv[1], "scan")) {
    int pos = atoi(argv[3]), lo = atoi(argv[4]), hi = atoi(argv[5]);
    FILE *out = fopen(argv[6], "a");
    { int xt = 12345; int *tmp = malloc(sizeof(int)*N); row_fast(xt, tmp); int mm = 0; for (int g = 0; g < N; g++) if (tmp[g] != gmul(xt, g)) mm++;
      row_fast(ginv(xt), tmp); for (int g = 0; g < N; g++) if (tmp[g] != gmul(ginv(xt), g)) mm++; fprintf(stderr, "row_fast mismatches=%d\n", mm); free(tmp); }
    int base_S[ND]; memcpy(base_S, S, sizeof S);
    int hist[64] = {0}; int best = 1 << 30, nbest = 0; long long evals = 0, full = 0;
    for (int kk = lo; kk < hi; kk++) {
      int x = (int)(((long long)kk * 7919) % N);
      int dup = 0; for (int i = 0; i < ND; i++) if (i != pos && base_S[i] == x) dup = 1;
      if (dup) continue;
      S[pos] = x; build_rows(pos, x);
      int ca = 0, cb = 0; int c = cost_of(&ca, &cb); evals++;
      int hc = ca < 63 ? ca : 63; hist[hc]++;
      if (c < 6) {
        full++;
        int ok = (c == 0) ? full_ok() : 0; if (c == 0 && !ok) {}
        fprintf(out, "pos=%d x=%d cost=%d A=%d B=%d valid_full=%d\n", pos, x, c, ca, cb, ok);
        if (c < best) best = c; nbest++;
        if (c == 0 && ok) { fprintf(out, "FOUND_COST0 pos=%d x=%d\n", pos, x); }
      }
      if (evals % 500 == 0) fflush(out);
    }
    fprintf(out, "SCAN pos=%d range=[%d,%d) evals=%lld cost<6 count=%lld best=%d\n", pos, lo, hi, evals, full, best == (1 << 30) ? -1 : best);
    fprintf(out, "HIST_A"); for (int i = 0; i < 40; i++) fprintf(out, " %d", hist[i]); fprintf(out, "\n");
    fclose(out);
    printf("pos=%d range=[%d,%d) evals=%lld cost<6=%lld best=%d\n", pos, lo, hi, evals, full, best == (1 << 30) ? -1 : best);
    return 0;
  }
  return 1;
}
