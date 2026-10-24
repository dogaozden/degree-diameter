/* Route-chart fitter over F_q^4, q in {2,3,4}, for an arbitrary labeled controller given as two permutations
   sigma_a, sigma_b of [0, n) (side A = [0, nA), side B = [nA, n)) plus optional extra involution labels (not used).
   Labels: 0 = a, 1 = a^-1, 2 = b, 3 = b^-1. Chart: A_a, A_b in GL_4(F_q), b_a, b_b in F_q^4.
   cost = exact number of missed (x, y) pairs over all ordered same-side controller pairs (c, d), using all label
   walks of length 0, 2, 4 from c to d (union of affine sets A_w x + Im M_w). Random restarts + annealing.
   usage: fitq q CTRL seed iters restarts [chart]   CTRL file: "n nA" then sigma_a (n entries) then sigma_b (n entries)
   Output chart: "CHART q" then A_a (16), b_a (4), A_b (16), b_b (4) digits. F_4 codes: 0,1,w,w^2 = 0,1,2,3. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
static int q, Q4;                   /* q^4 */
static int ADD[256][256], SC[4][256];   /* vector add, scalar mult (scalar codes 0..q-1) */
static int fadd[4][4], fmul[4][4], finv[4];
static int n, nA, sa[8192], sb[8192], sai[8192], sbi[8192], stride = 1;
typedef struct { int m[4][4]; } Mat;
static int vid(const int *v) { int x = 0, p = 1; for (int i = 0; i < 4; i++) { x += v[i] * p; p *= q; } return x; }
static void vdec(int x, int *v) { for (int i = 0; i < 4; i++) { v[i] = x % q; x /= q; } }
static int mv(const Mat *A, int x) { int v[4], w[4]; vdec(x, v); for (int i = 0; i < 4; i++) { int s = 0; for (int j = 0; j < 4; j++) s = fadd[s][fmul[A->m[i][j]][v[j]]]; w[i] = s; } return vid(w); }
static Mat mm(const Mat *A, const Mat *B) { Mat C; for (int i = 0; i < 4; i++) for (int j = 0; j < 4; j++) { int s = 0; for (int k = 0; k < 4; k++) s = fadd[s][fmul[A->m[i][k]][B->m[k][j]]]; C.m[i][j] = s; } return C; }
static int minv(const Mat *A, Mat *R) { int a[4][8]; for (int i = 0; i < 4; i++) for (int j = 0; j < 8; j++) a[i][j] = j < 4 ? A->m[i][j] : (j - 4 == i);
  for (int c = 0; c < 4; c++) { int p = -1; for (int i = c; i < 4; i++) if (a[i][c]) { p = i; break; } if (p < 0) return 0;
    for (int j = 0; j < 8; j++) { int t = a[p][j]; a[p][j] = a[c][j]; a[c][j] = t; }
    int iv = finv[a[c][c]]; for (int j = 0; j < 8; j++) a[c][j] = fmul[iv][a[c][j]];
    for (int i = 0; i < 4; i++) if (i != c && a[i][c]) { int f = a[i][c], nf = 0; for (int z = 0; z < q; z++) if (fadd[f][z] == 0) nf = z;  /* nf = -f */
      for (int j = 0; j < 8; j++) a[i][j] = fadd[a[i][j]][fmul[nf][a[c][j]]]; } }
  for (int i = 0; i < 4; i++) for (int j = 0; j < 4; j++) R->m[i][j] = a[i][j + 4]; return 1; }
static Mat Am[4]; static int Bv[4]; static Mat Aa, Ab; static int ba, bb;
static int setup(void) { Am[0] = Aa; Am[2] = Ab; if (!minv(&Aa, &Am[1]) || !minv(&Ab, &Am[3])) return 0; Bv[0] = ba; Bv[2] = bb; Bv[1] = mv(&Am[1], ba); Bv[3] = mv(&Am[3], bb); return ba && bb; }
static int step(int t, int v) { switch (t) { case 0: return sa[v]; case 1: return sai[v]; case 2: return sb[v]; default: return sbi[v]; } }
/* span of k vectors as a bitmask over Q4 points (Q4 <= 256) */
typedef struct { unsigned long long w[4]; } Mask;
static int span_mask(const int *cols, int k, Mask *M) { int el[256], sz = 1; memset(M, 0, sizeof *M); M->w[0] = 1; el[0] = 0;
  for (int c = 0; c < k; c++) { int v = cols[c]; if (M->w[v >> 6] >> (v & 63) & 1) continue; int cur = sz;
    for (int i = 0; i < cur; i++) for (int l = 1; l < q; l++) { int e = ADD[el[i]][SC[l][v]]; if (!(M->w[e >> 6] >> (e & 63) & 1)) { M->w[e >> 6] |= 1ULL << (e & 63); el[sz++] = e; } } }
  return sz; }
/* precomputed per label sequence of length 2 and 4: A_w and Im M_w */
static Mat A2[16], A4s[256]; static Mask S2[16], S4[256]; static int full4[256];
static void precompute(void) {
  for (int t1 = 0; t1 < 4; t1++) for (int t2 = 0; t2 < 4; t2++) { int cols[2] = { mv(&Am[t2], Bv[t1]), Bv[t2] }; A2[t1*4+t2] = mm(&Am[t2], &Am[t1]); span_mask(cols, 2, &S2[t1*4+t2]); }
  for (int t1 = 0; t1 < 4; t1++) for (int t2 = 0; t2 < 4; t2++) for (int t3 = 0; t3 < 4; t3++) for (int t4 = 0; t4 < 4; t4++) { int w = t1*64+t2*16+t3*4+t4;
    int cols[4] = { mv(&Am[t4], mv(&Am[t3], mv(&Am[t2], Bv[t1]))), mv(&Am[t4], mv(&Am[t3], Bv[t2])), mv(&Am[t4], Bv[t3]), Bv[t4] };
    Mat M = mm(&Am[t2], &Am[t1]); M = mm(&Am[t3], &M); A4s[w] = mm(&Am[t4], &M); full4[w] = span_mask(cols, 4, &S4[w]) == Q4; } }
static int *wl_start, *wl_seq, nwl;   /* per (source, target) walk lists: computed once from the controller */
static int *pair_c, *pair_d, npairs;
static void build_walk_lists(void) {
  /* for each source c and same-side target d: list of sequences (code: 0 = empty walk, 1000+s2 = length-2, 2000+s4) */
  int cap = 1 << 20; wl_seq = malloc(cap * sizeof(int)); int cap2 = n * n; wl_start = malloc((cap2 + 1) * sizeof(int)); pair_c = malloc(cap2 * sizeof(int)); pair_d = malloc(cap2 * sizeof(int));
  static int bucket[8192][64]; static int bcnt[8192];
  npairs = 0; nwl = 0;
  for (int c = 0; c < n; c++) {
    if (c % stride) continue;
    int side = c < nA; memset(bcnt, 0, sizeof(int) * n);
    #define ADDW(d, code) do { if (bcnt[d] < 64) bucket[d][bcnt[d]++] = (code); } while (0)
    ADDW(c, 0);
    for (int t1 = 0; t1 < 4; t1++) { int x1 = step(t1, c); for (int t2 = 0; t2 < 4; t2++) { int x2 = step(t2, x1); ADDW(x2, 1000 + t1*4 + t2);
      for (int t3 = 0; t3 < 4; t3++) { int x3 = step(t3, x2); for (int t4 = 0; t4 < 4; t4++) { int x4 = step(t4, x3); ADDW(x4, 2000 + t1*64 + t2*16 + t3*4 + t4); } } } }
    for (int d = 0; d < n; d++) { if ((d < nA) != side) continue;
      pair_c[npairs] = c; pair_d[npairs] = d; wl_start[npairs] = nwl;
      for (int i = 0; i < bcnt[d]; i++) { if (nwl >= cap) { cap *= 2; wl_seq = realloc(wl_seq, cap * sizeof(int)); } wl_seq[nwl++] = bucket[d][i]; }
      npairs++; } }
  wl_start[npairs] = nwl; }
static long missed(long cap) { long total = 0; Mat I; memset(&I, 0, sizeof I); for (int i = 0; i < 4; i++) I.m[i][i] = 1; Mask Z; memset(&Z, 0, sizeof Z); Z.w[0] = 1;
  for (int p = 0; p < npairs && total <= cap; p++) {
    int full = 0, nw = wl_start[p + 1] - wl_start[p];
    if (nw == 0) { total += (long)Q4 * Q4; continue; }
    for (int i = wl_start[p]; i < wl_start[p + 1]; i++) { int code = wl_seq[i]; if (code >= 2000 && full4[code - 2000]) { full = 1; break; } }
    if (full) continue;
    for (int x = 0; x < Q4; x++) { Mask cov; memset(&cov, 0, sizeof cov);
      for (int i = wl_start[p]; i < wl_start[p + 1]; i++) { int code = wl_seq[i]; const Mat *A; const Mask *S;
        if (code == 0) { A = &I; S = &Z; } else if (code < 2000) { A = &A2[code - 1000]; S = &S2[code - 1000]; } else { A = &A4s[code - 2000]; S = &S4[code - 2000]; }
        int b0 = mv(A, x);
        for (int e = 0; e < Q4; e++) if (S->w[e >> 6] >> (e & 63) & 1) { int y = ADD[b0][e]; cov.w[y >> 6] |= 1ULL << (y & 63); } }
      int c = 0; for (int i = 0; i < 4; i++) c += __builtin_popcountll(cov.w[i]); total += Q4 - c; } }
  return total; }
static unsigned long long rs = 88172645463325252ULL;
static unsigned long long rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static void randchart(void) { do { for (int i = 0; i < 4; i++) for (int j = 0; j < 4; j++) { Aa.m[i][j] = rnd() % q; Ab.m[i][j] = rnd() % q; } ba = rnd() % Q4; bb = rnd() % Q4; } while (!setup()); }
int main(int argc, char **argv) {
  q = atoi(argv[1]); Q4 = q * q * q * q;
  if (q == 4) { int A4[4][4] = {{0,1,2,3},{1,0,3,2},{2,3,0,1},{3,2,1,0}}, M4[4][4] = {{0,0,0,0},{0,1,2,3},{0,2,3,1},{0,3,1,2}}; memcpy(fadd, A4, sizeof A4); memcpy(fmul, M4, sizeof M4); finv[1] = 1; finv[2] = 3; finv[3] = 2; }
  else { for (int a = 0; a < q; a++) for (int b = 0; b < q; b++) { fadd[a][b] = (a + b) % q; fmul[a][b] = (a * b) % q; } for (int a = 1; a < q; a++) for (int b = 1; b < q; b++) if (fmul[a][b] == 1) finv[a] = b; }
  for (int x = 0; x < Q4; x++) { int v[4], w[4]; vdec(x, v); for (int y = 0; y < Q4; y++) { vdec(y, w); int z[4]; for (int i = 0; i < 4; i++) z[i] = fadd[v[i]][w[i]]; ADD[x][y] = vid(z); }
    for (int s = 0; s < q; s++) { int z[4]; for (int i = 0; i < 4; i++) z[i] = fmul[s][v[i]]; SC[s][x] = vid(z); } }
  FILE *cf = fopen(argv[2], "r"); if (fscanf(cf, "%d %d", &n, &nA) != 2) return 1;
  for (int i = 0; i < n; i++) if (fscanf(cf, "%d", &sa[i]) != 1) return 1; for (int i = 0; i < n; i++) if (fscanf(cf, "%d", &sb[i]) != 1) return 1;
  for (int i = 0; i < n; i++) { sai[sa[i]] = i; sbi[sb[i]] = i; }
  rs ^= (unsigned long long)atoll(argv[3]) * 0x9E3779B97F4A7C15ULL; long iters = atol(argv[4]); int restarts = atoi(argv[5]);
  if (getenv("STRIDE")) stride = atoi(getenv("STRIDE"));
  build_walk_lists();
  if (argc > 6) { FILE *ch = fopen(argv[6], "r"); int d[40], k = 0, cc; while (k < 40 && (cc = fgetc(ch)) != EOF) if (cc >= '0' && cc <= '3') d[k++] = cc - '0';
    for (int i = 0; i < 4; i++) for (int j = 0; j < 4; j++) { Aa.m[i][j] = d[4*i+j]; Ab.m[i][j] = d[20+4*i+j]; } int va[4], vb[4]; for (int i = 0; i < 4; i++) { va[i] = d[16+i]; vb[i] = d[36+i]; } ba = vid(va); bb = vid(vb); if (!setup()) return 1; }
  else randchart();
  precompute(); long c = missed(1L << 60), best = c; Mat bAa = Aa, bAb = Ab; int bba = ba, bbb = bb;
  printf("pairs %d, start cost %ld\n", npairs, c); fflush(stdout);
  for (int r = 0; r < restarts && best > 0; r++) {
    if (r > 0) { randchart(); precompute(); c = missed(1L << 60); }
    double T = 0.05 * (c + 100); long stall = 0;
    for (long it = 0; it < iters && c > 0 && stall < iters / 4; it++) {
      Mat sA = Aa, sB = Ab; int s1 = ba, s2 = bb; int w = rnd() % 4, v[4];
      if (w == 0) Aa.m[rnd() & 3][rnd() & 3] = rnd() % q; else if (w == 1) Ab.m[rnd() & 3][rnd() & 3] = rnd() % q;
      else if (w == 2) { vdec(ba, v); v[rnd() & 3] = rnd() % q; ba = vid(v); } else { vdec(bb, v); v[rnd() & 3] = rnd() % q; bb = vid(v); }
      if (!setup()) { Aa = sA; Ab = sB; ba = s1; bb = s2; setup(); continue; }
      precompute(); long c2 = missed(c + (long)(5 * T) + 1);
      if (c2 < c) stall = 0; else stall++;
      if (c2 <= c || (double)(rnd() % 1000000) / 1e6 < exp((double)(c - c2) / T)) c = c2; else { Aa = sA; Ab = sB; ba = s1; bb = s2; setup(); precompute(); }
      T *= 0.999; if (T < 1.0) T = 1.0; }
    if (c < best) { best = c; bAa = Aa; bAb = Ab; bba = ba; bbb = bb; printf("restart %d cost %ld\n", r, c); fflush(stdout); } }
  Aa = bAa; Ab = bAb; ba = bba; bb = bbb; setup();
  printf("final cost %ld\nCHART %d ", best, q); int v[4];
  for (int i = 0; i < 4; i++) { for (int j = 0; j < 4; j++) printf("%d", Aa.m[i][j]); printf(" "); } vdec(ba, v); for (int i = 0; i < 4; i++) printf("%d", v[i]); printf(" ");
  for (int i = 0; i < 4; i++) { for (int j = 0; j < 4; j++) printf("%d", Ab.m[i][j]); printf(" "); } vdec(bb, v); for (int i = 0; i < 4; i++) printf("%d", v[i]); printf("\n");
  return 0; }
