/* Fit a route chart (A_a, b_a, A_b, b_b over F_4^4) to a given Haar controller H(G,S), |S| = 4.
   cost = (# label-reduced 4-words with singular M_w)  [makes every controller pair at distance 4 fine]
        + (# missed (x,y) pairs, x,y in F_4^4, over all same-side controller targets d at distance 0 or 2 from the two
           base vertices (e,A), (e,B)), computed exactly from all label walks of length 0, 2, 4.
   usage: chartfit TABLE s1 s2 s3 s4 seed iters [chartfile]  (chartfile: start point, 40 digits) */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
typedef unsigned char u8;
static u8 MUL[4][4] = {{0,0,0,0},{0,1,2,3},{0,2,3,1},{0,3,1,2}}, INV[4] = {0,1,3,2};
typedef struct { u8 m[4][4]; } Mat;
static int n, T[256][256], inv_[256], s[4];
static int mvid(const Mat *A, int x) { int y = 0; for (int i = 0; i < 4; i++) { u8 v = 0; for (int j = 0; j < 4; j++) v ^= MUL[A->m[i][j]][(x >> (2*j)) & 3]; y |= v << (2*i); } return y; }
static Mat mmul(const Mat *A, const Mat *B) { Mat C; for (int i = 0; i < 4; i++) for (int j = 0; j < 4; j++) { u8 v = 0; for (int k = 0; k < 4; k++) v ^= MUL[A->m[i][k]][B->m[k][j]]; C.m[i][j] = v; } return C; }
static int minv(const Mat *A, Mat *R) { u8 a[4][8]; for (int i = 0; i < 4; i++) for (int j = 0; j < 8; j++) a[i][j] = j < 4 ? A->m[i][j] : (j - 4 == i);
  for (int c = 0; c < 4; c++) { int p = -1; for (int i = c; i < 4; i++) if (a[i][c]) { p = i; break; } if (p < 0) return 0;
    if (p != c) for (int j = 0; j < 8; j++) { u8 t = a[p][j]; a[p][j] = a[c][j]; a[c][j] = t; }
    u8 iv = INV[a[c][c]]; for (int j = 0; j < 8; j++) a[c][j] = MUL[iv][a[c][j]];
    for (int i = 0; i < 4; i++) if (i != c && a[i][c]) { u8 f = a[i][c]; for (int j = 0; j < 8; j++) a[i][j] ^= MUL[f][a[c][j]]; } }
  for (int i = 0; i < 4; i++) for (int j = 0; j < 4; j++) R->m[i][j] = a[i][j+4]; return 1; }
static Mat Am[4]; static int Bv[4];   /* labels 0=a 1=A 2=b 3=B ; inverse label = t^1 */
static Mat Aa, Ab; static int ba, bb;
static int setup(void) { Am[0] = Aa; Am[2] = Ab; if (!minv(&Aa, &Am[1]) || !minv(&Ab, &Am[3])) return 0;
  Bv[0] = ba; Bv[2] = bb; Bv[1] = mvid(&Am[1], ba); Bv[3] = mvid(&Am[3], bb); return ba && bb; }
/* controller: vertex = side*n + g ; step(label, v) */
static int step(int t, int v) { int side = v / n, g = v % n;
  if (side == 0) { int k = t == 0 ? 0 : t == 1 ? 1 : t == 2 ? 2 : 3; return n + T[s[k]][g]; }
  else { int k = t == 0 ? 1 : t == 1 ? 0 : t == 2 ? 3 : 2; return T[inv_[s[k]]][g]; } }
static int span_mask(int *cols, int k, unsigned long long *mask) { /* F_4-span of k vectors as 256-bit mask; returns size */
  memset(mask, 0, 32); mask[0] = 1; int sz = 1; int elems[256]; elems[0] = 0;
  for (int c = 0; c < k; c++) { int v = cols[c]; if (mask[v >> 6] >> (v & 63) & 1) continue;
    int cur = sz; for (int i = 0; i < cur; i++) for (int l = 1; l < 4; l++) { int sv = 0; for (int j = 0; j < 4; j++) sv |= MUL[l][(v >> (2*j)) & 3] << (2*j);
      int e = elems[i] ^ sv; if (!(mask[e >> 6] >> (e & 63) & 1)) { mask[e >> 6] |= 1ULL << (e & 63); elems[sz++] = e; } } }
  return sz; }
static int singular_words(void) { int bad = 0;
  for (int t1 = 0; t1 < 4; t1++) for (int t2 = 0; t2 < 4; t2++) { if (t2 == (t1 ^ 1)) continue;
    for (int t3 = 0; t3 < 4; t3++) { if (t3 == (t2 ^ 1)) continue; for (int t4 = 0; t4 < 4; t4++) { if (t4 == (t3 ^ 1)) continue;
      int cols[4] = { mvid(&Am[t4], mvid(&Am[t3], mvid(&Am[t2], Bv[t1]))), mvid(&Am[t4], mvid(&Am[t3], Bv[t2])), mvid(&Am[t4], Bv[t3]), Bv[t4] };
      unsigned long long mk[4]; if (span_mask(cols, 4, mk) < 256) bad++; } } }
  return bad; }
/* walks of length 0,2,4 from base b; for each target at distance 0 or 2, union of affine images */
static int dist2targets[2][256], ntg[2];
static int missed(void) { int total = 0;
  for (int sd = 0; sd < 2; sd++) { int base = sd * n;
    for (int it = 0; it < ntg[sd]; it++) { int d = dist2targets[sd][it];
      /* collect walks base -> d */
      static Mat Aw[400]; static unsigned long long Sw[400][4]; int nw = 0;
      if (d == base) { Mat I; memset(&I, 0, sizeof I); for (int i = 0; i < 4; i++) I.m[i][i] = 1; Aw[nw] = I; memset(Sw[nw], 0, 32); Sw[nw][0] = 1; nw++; }
      for (int t1 = 0; t1 < 4; t1++) { int v1 = step(t1, base);
        for (int t2 = 0; t2 < 4; t2++) { int v2 = step(t2, v1);
          if (v2 == d) { int cols[2] = { mvid(&Am[t2], Bv[t1]), Bv[t2] }; Aw[nw] = mmul(&Am[t2], &Am[t1]); span_mask(cols, 2, Sw[nw]); nw++; }
          for (int t3 = 0; t3 < 4; t3++) { int v3 = step(t3, v2);
            for (int t4 = 0; t4 < 4; t4++) { int v4 = step(t4, v3); if (v4 != d) continue;
              int cols[4] = { mvid(&Am[t4], mvid(&Am[t3], mvid(&Am[t2], Bv[t1]))), mvid(&Am[t4], mvid(&Am[t3], Bv[t2])), mvid(&Am[t4], Bv[t3]), Bv[t4] };
              Mat M = mmul(&Am[t2], &Am[t1]); M = mmul(&Am[t3], &M); Aw[nw] = mmul(&Am[t4], &M); span_mask(cols, 4, Sw[nw]); nw++; } } } }
      /* full-rank walk -> covered for all x */
      int full = 0; for (int w = 0; w < nw; w++) if (Sw[w][0] == ~0ULL && Sw[w][1] == ~0ULL && Sw[w][2] == ~0ULL && Sw[w][3] == ~0ULL) { full = 1; break; }
      if (full) continue;
      for (int x = 0; x < 256; x++) { unsigned long long cov[4] = {0,0,0,0};
        for (int w = 0; w < nw; w++) { int b0 = mvid(&Aw[w], x);
          for (int e = 0; e < 256; e++) if (Sw[w][e >> 6] >> (e & 63) & 1) { int y = b0 ^ e; cov[y >> 6] |= 1ULL << (y & 63); } }
        total += 256 - (__builtin_popcountll(cov[0]) + __builtin_popcountll(cov[1]) + __builtin_popcountll(cov[2]) + __builtin_popcountll(cov[3])); } } }
  return total; }
static unsigned long long rs = 88172645463325252ULL;
static unsigned long long rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
int main(int argc, char **argv) {
  FILE *f = fopen(argv[1], "r"); n = 0; char line[8192];
  while (fgets(line, sizeof line, f)) { if (strlen(line) < 2) continue; char *p = line; int j = 0; while (*p) { while (*p == ' ') p++; if (*p == '\n' || !*p) break; T[n][j++] = strtol(p, &p, 10); } n++; }
  int e = -1; for (int i = 0; i < n && e < 0; i++) { int ok = 1; for (int j = 0; j < n; j++) if (T[i][j] != j) { ok = 0; break; } if (ok) e = i; }
  for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) if (T[i][j] == e) inv_[i] = j;
  for (int k = 0; k < 4; k++) s[k] = atoi(argv[2 + k]);
  rs ^= (unsigned long long)atoll(argv[6]) * 0x9E3779B97F4A7C15ULL; long iters = atol(argv[7]);
  /* targets at distance 0 or 2 (same side) from the base vertices; base vertex g = e */
  for (int sd = 0; sd < 2; sd++) { int base = sd * n + e; ntg[sd] = 0;
    for (int g = 0; g < n; g++) dist2targets[sd][ntg[sd]++] = sd * n + g; }
  /* the base vertex index used inside missed(): sd*n (assumes e == 0) */
  if (e != 0) { fprintf(stderr, "identity is not element 0\n"); return 1; }
  if (argc > 8) { FILE *cf = fopen(argv[8], "r"); int d[40], k = 0, ch; while (k < 40 && (ch = fgetc(cf)) != EOF) if (ch >= '0' && ch <= '3') d[k++] = ch - '0';
    for (int i = 0; i < 4; i++) for (int j = 0; j < 4; j++) { Aa.m[i][j] = d[4*i+j]; Ab.m[i][j] = d[20+4*i+j]; }
    ba = 0; bb = 0; for (int i = 0; i < 4; i++) { ba |= d[16+i] << (2*i); bb |= d[36+i] << (2*i); } }
  else do { for (int i = 0; i < 4; i++) for (int j = 0; j < 4; j++) { Aa.m[i][j] = rnd() & 3; Ab.m[i][j] = rnd() & 3; } ba = rnd() & 255; bb = rnd() & 255; } while (!setup());
  if (!setup()) { fprintf(stderr, "bad start chart\n"); return 1; }
  int c = missed(); double Tm = 20000.0; int best = c;
  printf("start cost %d (singular %d, missed %d)\n", c, singular_words(), missed()); fflush(stdout);
  for (long it = 0; it < iters && c > 0; it++) {
    Mat sa = Aa, sb = Ab; int sba = ba, sbb = bb; int w = rnd() % 4;
    if (w == 0) Aa.m[rnd() & 3][rnd() & 3] = rnd() & 3; else if (w == 1) Ab.m[rnd() & 3][rnd() & 3] = rnd() & 3;
    else if (w == 2) ba ^= (rnd() & 3) << (2 * (rnd() & 3)); else bb ^= (rnd() & 3) << (2 * (rnd() & 3));
    if (!setup()) { Aa = sa; Ab = sb; ba = sba; bb = sbb; setup(); continue; }
    int c2 = missed();
    if (c2 <= c || (double)(rnd() % 1000000) / 1e6 < exp((c - c2) / Tm)) { c = c2; if (c < best) { best = c; printf("it %ld cost %d\n", it, c); fflush(stdout); } }
    else { Aa = sa; Ab = sb; ba = sba; bb = sbb; setup(); }
    Tm *= 0.9995; if (Tm < 300) Tm = 300;
  }
  printf("final cost %d\n", c);
  if (c == 0 || argc > 0) { printf("CHART "); for (int i = 0; i < 4; i++) { for (int j = 0; j < 4; j++) printf("%d", Aa.m[i][j]); printf(" "); }
    for (int i = 0; i < 4; i++) printf("%d", (ba >> (2*i)) & 3); printf(" ");
    for (int i = 0; i < 4; i++) { for (int j = 0; j < 4; j++) printf("%d", Ab.m[i][j]); printf(" "); }
    for (int i = 0; i < 4; i++) printf("%d", (bb >> (2*i)) & 3); printf("\n"); }
  return 0; }
