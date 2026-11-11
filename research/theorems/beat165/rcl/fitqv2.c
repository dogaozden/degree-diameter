/* Route-chart fitter with a chart per base vertex, for permutation-voltage controllers over F_4^4 (q = 4).
   Controller: base vertices v in [0,2k) (v < k side A), group table (m), sigma_t(v,g) = (pi_t(v), phi_t[v] g).
   Parameters: for each base vertex v and t in {a, b}: A_{v,t} in GL_4(F_4), b_{v,t}; the reverse label at
   w = pi_t(v) is A_{w,t^-1} = A_{v,t}^-1, b_{w,t^-1} = A_{v,t}^-1 b_{v,t}.
   Lift edges: (v,g,x) ~ (sigma_t(v,g), A_{v,t} x + lam b_{v,t}). Group-invariant, so sources = (v, e), one per base vertex.
   cost = exact missed (x,y) pairs over all same-side targets. usage: fitqv TABLE PVCTRL seed iters restarts [uniformchart] */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#define Q4 256
static int MUL[4][4] = {{0,0,0,0},{0,1,2,3},{0,2,3,1},{0,3,1,2}}, INV[4] = {0,1,3,2};
typedef struct { int m[4][4]; } Mat;
static int mv(const Mat *A, int x) { int y = 0; for (int i = 0; i < 4; i++) { int s = 0; for (int j = 0; j < 4; j++) s ^= MUL[A->m[i][j]][(x >> (2*j)) & 3]; y |= s << (2*i); } return y; }
static Mat mm(const Mat *A, const Mat *B) { Mat C; for (int i = 0; i < 4; i++) for (int j = 0; j < 4; j++) { int s = 0; for (int k = 0; k < 4; k++) s ^= MUL[A->m[i][k]][B->m[k][j]]; C.m[i][j] = s; } return C; }
static int minv(const Mat *A, Mat *R) { int a[4][8]; for (int i = 0; i < 4; i++) for (int j = 0; j < 8; j++) a[i][j] = j < 4 ? A->m[i][j] : (j - 4 == i);
  for (int c = 0; c < 4; c++) { int p = -1; for (int i = c; i < 4; i++) if (a[i][c]) { p = i; break; } if (p < 0) return 0;
    for (int j = 0; j < 8; j++) { int t = a[p][j]; a[p][j] = a[c][j]; a[c][j] = t; } int iv = INV[a[c][c]]; for (int j = 0; j < 8; j++) a[c][j] = MUL[iv][a[c][j]];
    for (int i = 0; i < 4; i++) if (i != c && a[i][c]) { int f = a[i][c]; for (int j = 0; j < 8; j++) a[i][j] ^= MUL[f][a[c][j]]; } }
  for (int i = 0; i < 4; i++) for (int j = 0; j < 4; j++) R->m[i][j] = a[i][j+4]; return 1; }
typedef struct { unsigned long long w[4]; } Mask;
static int span_mask(const int *cols, int k, Mask *M) { int el[256], sz = 1; memset(M, 0, sizeof *M); M->w[0] = 1; el[0] = 0;
  for (int c = 0; c < k; c++) { int v = cols[c]; if (M->w[v >> 6] >> (v & 63) & 1) continue; int cur = sz;
    for (int i = 0; i < cur; i++) for (int l = 1; l < 4; l++) { int sv = 0; for (int j = 0; j < 4; j++) sv |= MUL[l][(v >> (2*j)) & 3] << (2*j); int e = el[i] ^ sv;
      if (!(M->w[e >> 6] >> (e & 63) & 1)) { M->w[e >> 6] |= 1ULL << (e & 63); el[sz++] = e; } } }
  return sz; }
static int m, T[256][256], inv_[256], e, k, nb, pa[16], pb[16], fa[16], fb[16], pai[16], pbi[16];
static Mat PA[16][2]; static int PB[16][2];          /* free parameters: [v][0] = a-edge from v, [v][1] = b-edge */
static Mat LA[16][4]; static int LB[16][4];          /* effective per-vertex label maps */
static int setup(void) {
  for (int v = 0; v < nb; v++) { LA[v][0] = PA[v][0]; LB[v][0] = PB[v][0]; LA[v][2] = PA[v][1]; LB[v][2] = PB[v][1]; if (!PB[v][0] || !PB[v][1]) return 0; }
  for (int v = 0; v < nb; v++) { int u = pai[v]; if (!minv(&PA[u][0], &LA[v][1])) return 0; LB[v][1] = mv(&LA[v][1], PB[u][0]);
                                 u = pbi[v]; if (!minv(&PA[u][1], &LA[v][3])) return 0; LB[v][3] = mv(&LA[v][3], PB[u][1]); }
  return 1; }
static int bstep(int t, int v) { switch (t) { case 0: return pa[v]; case 1: return pai[v]; case 2: return pb[v]; default: return pbi[v]; } }
static int cstep(int t, int x) { int v = x / m, g = x % m;
  switch (t) { case 0: return pa[v] * m + T[fa[v]][g]; case 1: { int w = pai[v]; return w * m + T[inv_[fa[w]]][g]; }
               case 2: return pb[v] * m + T[fb[v]][g]; default: { int w = pbi[v]; return w * m + T[inv_[fb[w]]][g]; } } }
/* per (v0, sequence) data */
static Mat W2A[16][16], W4A[16][256]; static Mask W2S[16][16], W4S[16][256]; static int W4F[16][256];
static void precompute(void) {
  for (int v0 = 0; v0 < nb; v0++) {
    for (int t1 = 0; t1 < 4; t1++) { int v1 = bstep(t1, v0); for (int t2 = 0; t2 < 4; t2++) { int s = t1*4+t2;
      int cols[2] = { mv(&LA[v1][t2], LB[v0][t1]), LB[v1][t2] }; W2A[v0][s] = mm(&LA[v1][t2], &LA[v0][t1]); span_mask(cols, 2, &W2S[v0][s]); } }
    for (int t1 = 0; t1 < 4; t1++) { int v1 = bstep(t1, v0); for (int t2 = 0; t2 < 4; t2++) { int v2 = bstep(t2, v1);
      for (int t3 = 0; t3 < 4; t3++) { int v3 = bstep(t3, v2); for (int t4 = 0; t4 < 4; t4++) { int w = t1*64+t2*16+t3*4+t4;
        const Mat *M1 = &LA[v0][t1], *M2 = &LA[v1][t2], *M3 = &LA[v2][t3], *M4 = &LA[v3][t4];
        int cols[4] = { mv(M4, mv(M3, mv(M2, LB[v0][t1]))), mv(M4, mv(M3, LB[v1][t2])), mv(M4, LB[v2][t3]), LB[v3][t4] };
        Mat P = mm(M2, M1); P = mm(M3, &P); W4A[v0][w] = mm(M4, &P); W4F[v0][w] = span_mask(cols, 4, &W4S[v0][w]) == Q4; } } } } } }
static int npairs, *pv0, *pstart, *pseq, nseq;
static void build_lists(void) {
  int N = nb * m; int cap = 1 << 20; pseq = malloc(cap * 4); pv0 = malloc(nb * N * 4); pstart = malloc((nb * N + 1) * 4);
  static int bucket[8192][48], bcnt[8192]; npairs = 0; nseq = 0;
  for (int v0 = 0; v0 < nb; v0++) { int c = v0 * m + e; memset(bcnt, 0, sizeof(int) * N);
    #define ADDW(d, code) do { if (bcnt[d] < 48) bucket[d][bcnt[d]++] = (code); } while (0)
    ADDW(c, 0);
    for (int t1 = 0; t1 < 4; t1++) { int x1 = cstep(t1, c); for (int t2 = 0; t2 < 4; t2++) { int x2 = cstep(t2, x1); ADDW(x2, 1000 + t1*4+t2);
      for (int t3 = 0; t3 < 4; t3++) { int x3 = cstep(t3, x2); for (int t4 = 0; t4 < 4; t4++) ADDW(cstep(t4, x3), 2000 + t1*64+t2*16+t3*4+t4); } } }
    int side = v0 < k;
    for (int d = 0; d < N; d++) { if ((d / m < k) != side) continue; pv0[npairs] = v0; pstart[npairs] = nseq;
      for (int i = 0; i < bcnt[d]; i++) { if (nseq >= cap) { cap *= 2; pseq = realloc(pseq, cap * 4); } pseq[nseq++] = bucket[d][i]; }
      npairs++; } }
  pstart[npairs] = nseq; }
static int lastmiss = -1, nmissp = 0;
static long missed(long cap) { long total = 0; lastmiss = -1; nmissp = 0; Mat I; memset(&I, 0, sizeof I); for (int i = 0; i < 4; i++) I.m[i][i] = 1; Mask Z; memset(&Z, 0, sizeof Z); Z.w[0] = 1;
  for (int p = 0; p < npairs && total <= cap; p++) { int v0 = pv0[p], full = 0;
    if (pstart[p + 1] == pstart[p]) { total += Q4 * Q4; continue; }
    for (int i = pstart[p]; i < pstart[p + 1]; i++) { int c = pseq[i]; if (c >= 2000 && W4F[v0][c - 2000]) { full = 1; break; } }
    if (full) continue;
    for (int x = 0; x < Q4; x++) { Mask cov; memset(&cov, 0, sizeof cov);
      for (int i = pstart[p]; i < pstart[p + 1]; i++) { int c = pseq[i]; const Mat *A; const Mask *S;
        if (c == 0) { A = &I; S = &Z; } else if (c < 2000) { A = &W2A[v0][c - 1000]; S = &W2S[v0][c - 1000]; } else { A = &W4A[v0][c - 2000]; S = &W4S[v0][c - 2000]; }
        int b0 = mv(A, x); for (int w = 0; w < 4; w++) { unsigned long long bits = S->w[w]; while (bits) { int j = __builtin_ctzll(bits); bits &= bits - 1; int y = b0 ^ (w * 64 + j); cov.w[y >> 6] |= 1ULL << (y & 63); } } }
      { long mi = Q4 - (__builtin_popcountll(cov.w[0]) + __builtin_popcountll(cov.w[1]) + __builtin_popcountll(cov.w[2]) + __builtin_popcountll(cov.w[3]));
        if (mi > 0 && x == 0) { nmissp++; if (rand() % nmissp == 0) lastmiss = p; } total += mi; } } }
  return total; }
static unsigned long long rs = 88172645463325252ULL;
static unsigned long long rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static void randparams(void) { do { for (int v = 0; v < nb; v++) for (int t = 0; t < 2; t++) { for (int i = 0; i < 4; i++) for (int j = 0; j < 4; j++) PA[v][t].m[i][j] = rnd() & 3; PB[v][t] = rnd() & 255; } } while (!setup()); }
int main(int argc, char **argv) {
  FILE *f = fopen(argv[1], "r"); char line[16384]; m = 0;
  while (fgets(line, sizeof line, f)) { if (strlen(line) < 2) continue; char *p = line; int j = 0; while (*p) { while (*p == ' ') p++; if (*p == '\n' || !*p) break; T[m][j++] = strtol(p, &p, 10); } m++; }
  for (int i = 0; i < m; i++) { int ok = 1; for (int j = 0; j < m; j++) if (T[i][j] != j) { ok = 0; break; } if (ok) { e = i; break; } }
  for (int i = 0; i < m; i++) for (int j = 0; j < m; j++) if (T[i][j] == e) inv_[i] = j;
  FILE *cf = fopen(argv[2], "r"); int mm2; if (fscanf(cf, "%d %d", &k, &mm2) != 2) return 1; nb = 2 * k;
  for (int v = 0; v < nb; v++) if (fscanf(cf, "%d", &pa[v]) != 1) return 1; for (int v = 0; v < nb; v++) if (fscanf(cf, "%d", &pb[v]) != 1) return 1;
  for (int v = 0; v < nb; v++) if (fscanf(cf, "%d", &fa[v]) != 1) return 1; for (int v = 0; v < nb; v++) if (fscanf(cf, "%d", &fb[v]) != 1) return 1;
  for (int v = 0; v < nb; v++) { pai[pa[v]] = v; pbi[pb[v]] = v; }
  rs ^= (unsigned long long)atoll(argv[3]) * 0x9E3779B97F4A7C15ULL; long iters = atol(argv[4]); int restarts = atoi(argv[5]);
  build_lists();
  if (argc > 6) { FILE *ch = fopen(argv[6], "r"); int d[40], kk = 0, cc; while (kk < 40 && (cc = fgetc(ch)) != EOF) if (cc >= '0' && cc <= '3') d[kk++] = cc - '0';
    for (int v = 0; v < nb; v++) { for (int i = 0; i < 4; i++) for (int j = 0; j < 4; j++) { PA[v][0].m[i][j] = d[4*i+j]; PA[v][1].m[i][j] = d[20+4*i+j]; }
      PB[v][0] = 0; PB[v][1] = 0; for (int i = 0; i < 4; i++) { PB[v][0] |= d[16+i] << (2*i); PB[v][1] |= d[36+i] << (2*i); } }
    if (!setup()) { fprintf(stderr, "bad chart\n"); return 1; } }
  else randparams();
  precompute(); long c = missed(1L << 60), best = c; static Mat bPA[16][2]; static int bPB[16][2]; memcpy(bPA, PA, sizeof PA); memcpy(bPB, PB, sizeof PB);
  printf("pairs %d, start cost %ld\n", npairs, c); fflush(stdout);
  for (int r = 0; r < restarts && best > 0; r++) {
    if (r > 0) { randparams(); precompute(); c = missed(1L << 60); }
    double Tm = 0.05 * (c + 100); long stall = 0;
    for (long it = 0; it < iters && c > 0 && stall < iters / 4; it++) {
      static Mat sPA[16][2]; static int sPB[16][2]; memcpy(sPA, PA, sizeof PA); memcpy(sPB, PB, sizeof PB);
      int v = rnd() % nb, t = rnd() & 1;
      if (lastmiss >= 0 && rnd() % 10 < 7) {
        int p = lastmiss, ns = pstart[p + 1] - pstart[p];
        if (ns > 0) { int code = pseq[pstart[p] + rnd() % ns]; int len = code == 0 ? 0 : code < 2000 ? 2 : 4; int w = code == 0 ? 0 : code < 2000 ? code - 1000 : code - 2000;
          if (len > 0) { int labs[4]; for (int i = len - 1; i >= 0; i--) { labs[i] = w & 3; w >>= 2; }
            int st = rnd() % len; int bv = pv0[p]; for (int i = 0; i < st; i++) bv = bstep(labs[i], bv);
            int lab = labs[st];
            if (lab == 0 || lab == 2) { v = bv; t = lab >> 1; } else { v = lab == 1 ? pai[bv] : pbi[bv]; t = lab >> 1; } } } }
      if (rnd() % 5) PA[v][t].m[rnd() & 3][rnd() & 3] = rnd() & 3; else PB[v][t] ^= (rnd() & 3) << (2 * (rnd() & 3));
      if (!setup()) { memcpy(PA, sPA, sizeof PA); memcpy(PB, sPB, sizeof PB); setup(); continue; }
      precompute(); long c2 = missed(c + (long)(5 * Tm) + 1);
      if (c2 < c) stall = 0; else stall++;
      if (c2 <= c || (double)(rnd() % 1000000) / 1e6 < exp((double)(c - c2) / Tm)) c = c2; else { memcpy(PA, sPA, sizeof PA); memcpy(PB, sPB, sizeof PB); setup(); precompute(); }
      Tm *= 0.999; if (Tm < 1.0) Tm = 1.0; }
    if (c < best) { best = c; memcpy(bPA, PA, sizeof PA); memcpy(bPB, PB, sizeof PB); printf("restart %d cost %ld\n", r, c); fflush(stdout); } }
  memcpy(PA, bPA, sizeof PA); memcpy(PB, bPB, sizeof PB);
  printf("final cost %ld\nVCHART %d", best, nb);
  for (int v = 0; v < nb; v++) for (int t = 0; t < 2; t++) { printf(" "); for (int i = 0; i < 4; i++) for (int j = 0; j < 4; j++) printf("%d", PA[v][t].m[i][j]); printf(":"); for (int i = 0; i < 4; i++) printf("%d", (PB[v][t] >> (2*i)) & 3); }
  printf("\n"); return 0; }
