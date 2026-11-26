// cay_mq.c -- bitset-BFS defect search for Cayley graphs of G = K x| Q, K = Z_C (R=1) or Z_C^2 (R=C prime),
// Q = Z_A x Z_B (B may be 1), acting on K by commuting matrices P1 (generator of Z_A), P2 (generator of Z_B).
// Element (x; k), x=(x1,x2) level index x1*B+x2, k=(row,col).  Product (u,v)(x,y) = (u+x, M_x v + y), M_x = P1^x1 P2^x2.
// Left multiplication by s=(u,v): (x,y) -> (u+x, y + M_x v): bitset row rotation (+row shift for R>1).
// cay_mgk: group file header (p, -L0, k) = levels Q x Z_k, Z_k acting trivially (level j*L0+i).
// cay_mg: levels = elements of a matrix group Q in GL(2,p) (file), K = F_p^2 natural action. usage: cay_mg MODE FILE d K ...
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
typedef uint64_t u64; typedef unsigned __int128 u128;
static int L0, ZK; static int R, C, L, U, W, K, H, INV, ngen; static int *idx; static u64 *Rm, *Rinv; static int *lastu;
static u64 P1[4], P2[4], *Mx;           // Mx[x*4..]
static long long n; static u64 lastmask;
static u64 *vis, *fr, *nx, *lst, *lst2;
static int *DL, *SL, *TA, *TB, *GL;      // DL[g*L+x] dest level, SL[g*L+y] source level for dest y, TA/TB[g*L+x] shifts
static int gu[64]; static u64 gvr[64], gvc[64]; static int iu; static u64 ivr, ivc;
static u64 rs;
static inline u64 rnd(void){ rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static u64 mm(u64 a, u64 b, u64 m){ return (u64)((u128)a * b % m); }
static void matmul(const u64 *a, const u64 *b, u64 *o){   // modulus C (R>1) ; R==1 uses a[0]*b[0] mod C
  if (R == 1) { o[0] = mm(a[0], b[0], C); o[1] = o[2] = o[3] = 0; return; }
  u64 t[4]; t[0] = (mm(a[0], b[0], C) + mm(a[1], b[2], C)) % C; t[1] = (mm(a[0], b[1], C) + mm(a[1], b[3], C)) % C;
  t[2] = (mm(a[2], b[0], C) + mm(a[3], b[2], C)) % C; t[3] = (mm(a[2], b[1], C) + mm(a[3], b[3], C)) % C; memcpy(o, t, 32);
}
static void matvec(const u64 *a, u64 vr, u64 vc, u64 *orow, u64 *ocol){
  if (R == 1) { *orow = 0; *ocol = mm(a[0], vc, C); return; }
  *orow = (mm(a[0], vr, C) + mm(a[1], vc, C)) % C; *ocol = (mm(a[2], vr, C) + mm(a[3], vc, C)) % C;
}
static inline void shl_or(u64 *dst, const u64 *src, int s){
  int ws = s >> 6, bs = s & 63;
  if (bs == 0) { for (int i = ws; i < W; i++) dst[i] |= src[i - ws]; }
  else { dst[ws] |= src[0] << bs; for (int i = ws + 1; i < W; i++) dst[i] |= (src[i - ws] << bs) | (src[i - ws - 1] >> (64 - bs)); }
}
static inline void shr_or(u64 *dst, const u64 *src, int s){
  int ws = s >> 6, bs = s & 63;
  if (bs == 0) { for (int i = 0; i + ws < W; i++) dst[i] |= src[i + ws]; }
  else { for (int i = 0; i + ws + 1 < W; i++) dst[i] |= (src[i + ws] >> bs) | (src[i + ws + 1] << (64 - bs)); dst[W - 1 - ws] |= src[W - 1] >> bs; }
}
static int hlookup(u64 k);
static inline int lvmul(int u, int x){ const u64 *a = Rm + 4 * (u % L0), *b = Rm + 4 * (x % L0); u64 p = C; int jj = (u / L0 + x / L0) % ZK;
  u64 m0 = (a[0] * b[0] + a[1] * b[2]) % p, m1 = (a[0] * b[1] + a[1] * b[3]) % p, m2 = (a[2] * b[0] + a[3] * b[2]) % p, m3 = (a[2] * b[1] + a[3] * b[3]) % p;
  return jj * L0 + hlookup(((m0 * p + m1) * p + m2) * p + m3); }
static int lvneg(int x){ u64 p = C; const u64 *a = Rinv + 4 * (x % L0); return ((ZK - x / L0) % ZK) * L0 + hlookup(((a[0] * p + a[1]) * p + a[2]) * p + a[3]); }
static void gen_tables(int g, int u, u64 vr, u64 vc){
  GL[g] = u;
  int *dl = DL + g * L, *sl = SL + g * L;
  if (lastu[g] != u) { lastu[g] = u; for (int x = 0; x < L; x++) { int d = lvmul(u, x); dl[x] = d; sl[d] = x; } }
  for (int x = 0; x < L; x++) { u64 a, b; matvec(Mx + 4 * (x % L0), vr, vc, &a, &b); TA[g * L + x] = (int)a; TB[g * L + x] = (int)b; }
}
static void build_shifts(void){
  int g = 0;
  for (int i = 0; i < H; i++) {
    gen_tables(g++, gu[i], gvr[i], gvc[i]);
    int ni = lvneg(gu[i]); u64 a, b; matvec(Mx + 4 * (ni % L0), gvr[i], gvc[i], &a, &b);
    gen_tables(g++, ni, (C - a) % C, (C - b) % C);
  }
  if (INV) gen_tables(g++, iu, ivr, ivc);
}
static long long sizes[64]; static int ZERO_ONLY = 0; static int CB; static u64 *NC, *t1, *t2;
#define SPARSE_MAX (1LL << 20)
static inline void rot_or(u64 *dst, const u64 *src, int s){ if (s == 0) { for (int i = 0; i < W; i++) dst[i] |= src[i]; } else { shl_or(dst, src, s); shr_or(dst, src, CB - s); } }
// dst |= translate(src by (a,b)) on the flat bitset index row*C+col: masked double rotation (carry columns shift by s-C)
static inline void tr_or_s(u64 *dst, const u64 *src, int a, int b, u64 *t1, u64 *t2){
  int s = a * C + b;
  if (b == 0) { rot_or(dst, src, s); return; }
  const u64 *nc = NC + (size_t)b * W;
  for (int i = 0; i < W; i++) { u64 v = src[i]; t1[i] = v & nc[i]; t2[i] = v & ~nc[i]; }
  rot_or(dst, t1, s);
  int s2 = s - C; if (s2 < 0) s2 += CB;
  rot_or(dst, t2, s2);
}
// Ball BFS (2 bitsets): dense layers compute nx = union over generators of translates of the whole ball vis,
// rows in parallel by destination level (OpenMP); new layer = nx & ~vis.
static long long eval(void){
  build_shifts();
  size_t tot = (size_t)U * W; u64 rowC = CB;
  memset(vis, 0, tot * 8);
  long long cnt = 1; vis[0] = 1; sizes[0] = 1;
  long long nl = 1; lst[0] = 0; int dense = 0;
  for (int t = 1; t <= K; t++) {
    if (!dense && (nl * 1000 > n || nl > SPARSE_MAX)) dense = 1;
    if (!dense) {
      long long nn = 0;
      for (long long j = 0; j < nl; j++) {
        u64 e = lst[j]; int c = (int)(e % rowC); int x = (int)(e / rowC); int r = c / C, col = c % C;
        for (int g = 0; g < ngen; g++) {
          int x2 = DL[g * L + x]; int r2 = r + TA[g * L + x]; if (r2 >= C) r2 -= C; int c2 = col + TB[g * L + x]; if (c2 >= C) c2 -= C;
          int f2 = r2 * C + c2;
          u64 *w = &vis[(size_t)x2 * W + (f2 >> 6)]; u64 bb = 1ULL << (f2 & 63);
          if (!(*w & bb)) { *w |= bb; lst2[nn++] = (u64)x2 * rowC + f2; }
        }
      }
      u64 *tmp = lst; lst = lst2; lst2 = tmp; nl = nn; cnt += nn;
    } else if (ZERO_ONLY && t == K) {
      int bad = 0;
      #pragma omp parallel
      {
        u64 *tmp = malloc(W * 8), *s1 = malloc(W * 8), *s2 = malloc(W * 8);
        #pragma omp for schedule(dynamic, 64)
        for (int x2 = 0; x2 < L; x2++) {
          if (bad) continue;
          const u64 *v = vis + (size_t)x2 * W; memcpy(tmp, v, W * 8);
          for (int g = 0; g < ngen; g++) { int xs = SL[g * L + x2]; tr_or_s(tmp, vis + (size_t)xs * W, TA[g * L + xs], TB[g * L + xs], s1, s2); }
          tmp[W - 1] &= lastmask;
          int ok = 1;
          for (int i = 0; i < W - 1; i++) if (tmp[i] != ~0ULL) { ok = 0; break; }
          if (ok && tmp[W - 1] != lastmask) ok = 0;
          if (!ok) bad = 1;
        }
        free(tmp); free(s1); free(s2);
      }
      return bad;
    } else {
      #pragma omp parallel
      {
        u64 *s1 = malloc(W * 8), *s2 = malloc(W * 8);
        #pragma omp for schedule(dynamic, 64)
        for (int x2 = 0; x2 < L; x2++) {
          u64 *row = nx + (size_t)x2 * W; memset(row, 0, W * 8);
          for (int g = 0; g < ngen; g++) { int xs = SL[g * L + x2]; tr_or_s(row, vis + (size_t)xs * W, TA[g * L + xs], TB[g * L + xs], s1, s2); }
          row[W - 1] &= lastmask;
        }
        free(s1); free(s2);
      }
      long long nn = 0;
      #pragma omp parallel for reduction(+:nn) schedule(static)
      for (int ur = 0; ur < U; ur++) {
        u64 *a = nx + (size_t)ur * W, *v = vis + (size_t)ur * W;
        for (int i = 0; i < W; i++) { u64 z = a[i] & ~v[i]; v[i] |= z; nn += __builtin_popcountll(z); }
      }
      cnt += nn; nl = nn;
    }
    sizes[t] = nl;
    if (cnt == n || nl == 0) { for (int q = t + 1; q <= K; q++) sizes[q] = 0; break; }
  }
  return n - cnt;
}
// involution support: candidate levels with 2x=0 and v in the (-1)-eigen-space
static int *ilev, ni_, *ifull; static u64 *iwr, *iwc, *icount; static int INVNS;
static u64 gcdu(u64 a, u64 b){ while (b) { u64 t = a % b; a = b; b = t; } return a; }
static void init_inv(void){
  ni_ = 0; ilev = malloc(4 * L); ifull = malloc(4 * L); iwr = malloc(8 * L); iwc = malloc(8 * L); icount = malloc(8 * L);
  const char *im = getenv("INVMODE"); if (!im || (strcmp(im, "all") && strcmp(im, "nonscalar"))) { fprintf(stderr, "odd degree needs INVMODE=all|nonscalar\n"); exit(2); } INVNS = !strcmp(im, "nonscalar");
  for (int x = 0; x < L; x++) if (lvmul(x, x) == 0) {
    u64 *M = Mx + 4 * (x % L0);
    if (INVNS && M[1] == 0 && M[2] == 0 && M[0] == M[3]) continue;
    if (R == 1) { ifull[ni_] = 0; u64 b = (M[0] + 1) % C; u64 g = gcdu(b ? b : C, C); if (x == 0 && C % 2) continue; ilev[ni_] = x; iwr[ni_] = 0; iwc[ni_] = C / g; icount[ni_] = g; ni_++; }
    else {
      u64 B[4] = {(M[0] + 1) % C, M[1], M[2], (M[3] + 1) % C};
      if (!B[0] && !B[1] && !B[2] && !B[3]) { ilev[ni_] = x; ifull[ni_] = 1; ni_++; continue; }
      ifull[ni_] = 0;
      u64 al = B[0] | B[1] ? B[0] : B[2], be = B[0] | B[1] ? B[1] : B[3];
      u64 wr = (C - be) % C, wc = al;
      u64 chk1 = (mm(B[0], wr, C) + mm(B[1], wc, C)) % C, chk2 = (mm(B[2], wr, C) + mm(B[3], wc, C)) % C;
      if (chk1 || chk2) continue;
      ilev[ni_] = x; iwr[ni_] = wr; iwc[ni_] = wc; icount[ni_] = C; ni_++;
    }
  }
  if (INV && !ni_) { fprintf(stderr, "NOINV\n"); exit(2); }
}
static void rand_inv(void){ int k = (int)(rnd() % ni_); if (ifull[k]) { iu = ilev[k]; ivr = rnd() % C; ivc = rnd() % C; return; } u64 t = rnd() % icount[k]; iu = ilev[k]; ivr = R == 1 ? 0 : mm(t, iwr[k], C); ivc = mm(t, iwc[k], C); }
static void rand_v(int i){ gvr[i] = R == 1 ? 0 : rnd() % C; gvc[i] = rnd() % C; }
static void print_set(void){
  for (int i = 0; i < H; i++) printf(" (%d,%llu,%llu)", gu[i], (unsigned long long)gvr[i], (unsigned long long)gvc[i]);
  if (INV) printf(" inv(%d,%llu,%llu)", iu, (unsigned long long)ivr, (unsigned long long)ivc);
}
static int *hkeys_i; static u64 *hkeys; static u64 hmask;
static u64 code4(const u64 *a){ u64 p = C; return ((a[0] * p + a[1]) * p + a[2]) * p + a[3]; }
static u64 hh(u64 k){ k *= 0x9E3779B97F4A7C15ULL; return k >> 20; }
static int hlookup(u64 k){ u64 i = hh(k) & hmask; while (hkeys_i[i] >= 0) { if (hkeys[i] == k) return hkeys_i[i]; i = (i + 1) & hmask; } return -1; }
static void hput(u64 k, int v){ u64 i = hh(k) & hmask; while (hkeys_i[i] >= 0) i = (i + 1) & hmask; hkeys[i] = k; hkeys_i[i] = v; }
static u64 invmod(u64 a, u64 m){ long long t = 0, nt = 1, r = m, nr = a % m; while (nr) { long long q = r / nr, tmp = t - q * nt; t = nt; nt = tmp; tmp = r - q * nr; r = nr; nr = tmp; } if (r != 1) { fprintf(stderr, "matrix not invertible mod m\n"); exit(2); } if (t < 0) t += m; return (u64)t; }
static void inv2(const u64 *a, u64 *o){ u64 p = C; u64 det = (a[0] * a[3] + p * p - a[1] * a[2]) % p; u64 di = invmod(det, p);
  o[0] = a[3] * di % p; o[1] = (p - a[1]) * di % p; o[2] = (p - a[2]) * di % p; o[3] = a[0] * di % p; }
static void setup(const char *file){
  FILE *f = fopen(file, "rb"); if (!f) { fprintf(stderr, "no group file\n"); exit(2); }
  int hd[2]; if (fread(hd, 4, 2, f) != 2) exit(2); C = hd[0]; R = C;
  if (hd[1] < 0) { L = -hd[1]; if (fread(&ZK, 4, 1, f) != 1 || ZK < 1) { fprintf(stderr, "bad ZK\n"); exit(2); } } else { L = hd[1]; ZK = 1; }
  L0 = L;
  Rm = malloc(32 * L); Rinv = malloc(32 * L); Mx = Rinv; int *tmp = malloc(16 * L); if (fread(tmp, 16, L, f) != (size_t)L) { fprintf(stderr, "short file\n"); exit(2); } fclose(f);
  for (int i = 0; i < 4 * L; i++) Rm[i] = tmp[i]; free(tmp);
  u64 hs = 1; while (hs < (u64)4 * L) hs <<= 1; hmask = hs - 1; hkeys = malloc(8 * hs); hkeys_i = malloc(4 * hs); for (u64 i = 0; i < hs; i++) hkeys_i[i] = -1;
  idx = NULL; for (int x = 0; x < L; x++) { hput(code4(Rm + 4 * x), x); inv2(Rm + 4 * x, Rinv + 4 * x); }
  L = L0 * ZK; CB = C * C; U = L; n = (long long)U * CB; W = (CB + 63) / 64; lastmask = (CB & 63) ? ((1ULL << (CB & 63)) - 1) : ~0ULL;
  NC = calloc((size_t)C * W, 8);
  for (int b = 1; b < C; b++) for (int i = 0; i < CB; i++) if ((i % C) < C - b) NC[(size_t)b * W + (i >> 6)] |= 1ULL << (i & 63);
  size_t tot = (size_t)U * W;
  vis = malloc(tot * 8); nx = malloc(tot * 8); if (!vis || !nx) { fprintf(stderr, "oom\n"); exit(2); }
  { size_t cap = (size_t)(SPARSE_MAX + 4096) * 40; lst = malloc(8 * cap); lst2 = malloc(8 * cap); }
  ngen = 2 * H + INV; DL = malloc(4 * ngen * L); SL = malloc(4 * ngen * L); TA = malloc(4 * ngen * L); TB = malloc(4 * ngen * L); GL = malloc(4 * ngen);
  lastu = malloc(4 * ngen); for (int g = 0; g < ngen; g++) lastu[g] = -1;
}
static void seed(u64 s){ rs = s * 0x9E3779B97F4A7C15ULL + 88172645463325252ULL; for (int i = 0; i < 20; i++) rnd(); }
int main(int argc, char **argv){
  if (argc < 5) { fprintf(stderr, "usage: cay_mg MODE FILE d K ...\n"); return 1; }
  const char *mode = argv[1]; int a = 2; const char *file = argv[a++];
  int d = atoi(argv[a++]); K = atoi(argv[a++]); H = d / 2; INV = d & 1;
  setup(file); if (INV) init_inv();
  if (!strcmp(mode, "eval")) {   // ... gens: lev vr vc (H triples) [then inv lev vr vc]
    for (int i = 0; i < H; i++) { gu[i] = atoi(argv[a++]); gvr[i] = strtoull(argv[a++], 0, 10); gvc[i] = strtoull(argv[a++], 0, 10); }
    if (INV) { iu = atoi(argv[a++]); ivr = strtoull(argv[a++], 0, 10); ivc = strtoull(argv[a++], 0, 10); }
    long long df = eval();
    printf("n=%lld degree=%d k=%d defect=%lld layers:", n, d, K, df); for (int t = 0; t <= K; t++) printf(" %lld", sizes[t]); printf("\n"); return 0;
  }
  if (!strcmp(mode, "screen")) {   // S seed
    int S = atoi(argv[a++]); seed(strtoull(argv[a++], 0, 10)); long long *v = malloc(8 * S);
    for (int s = 0; s < S; s++) { for (int i = 0; i < H; i++) { gu[i] = 1 + (int)(rnd() % (L - 1)); rand_v(i); } if (INV) rand_inv(); v[s] = eval(); }
    for (int i = 1; i < S; i++) { long long t = v[i]; int j = i; while (j > 0 && v[j - 1] > t) { v[j] = v[j - 1]; j--; } v[j] = t; }
    double q = 0; int c = S / 4 > 0 ? S / 4 : 1; for (int i = 0; i < c; i++) q += v[i];
    printf("SCREEN n=%lld min=%lld lowq=%.1f\n", n, v[0], q / c); return 0;
  }
  if (!strcmp(mode, "popt")) {   // iters S seed restarts
    long long it_n = atoll(argv[a++]); int S = atoi(argv[a++]); seed(strtoull(argv[a++], 0, 10)); int RS = atoi(argv[a++]);
    u64 *vr = malloc(8 * S * 64), *vc = malloc(8 * S * 64), *ivr_ = malloc(8 * S), *ivc_ = malloc(8 * S); int *iuu = malloc(4 * S);
    int bestu[64]; double bestc = 1e30; long long CAP = 400;
    for (int rr = 0; rr < RS; rr++) {
      for (int s = 0; s < S; s++) { for (int i = 0; i < H; i++) { rand_v(i); vr[s * 64 + i] = gvr[i]; vc[s * 64 + i] = gvc[i]; } if (INV) { rand_inv(); ivr_[s] = ivr; ivc_[s] = ivc; iuu[s] = iu; } }
      for (int i = 0; i < H; i++) gu[i] = 1 + (int)(rnd() % (L - 1));
      #define COST(out) { double t_ = 0; for (int s = 0; s < S; s++) { for (int i = 0; i < H; i++) { gvr[i] = vr[s * 64 + i]; gvc[i] = vc[s * 64 + i]; } if (INV) { ivr = ivr_[s]; ivc = ivc_[s]; iu = iuu[s]; } long long df = eval(); t_ += df > CAP ? CAP : df; } out = t_ / S; }
      double cur; COST(cur);
      for (long long it = 0; it < it_n; it++) {
        int i = (int)(rnd() % H), old = gu[i];
        gu[i] = 1 + (int)(rnd() % (L - 1));
        double c; COST(c);
        if (c <= cur) cur = c; else gu[i] = old;
      }
      if (cur < bestc) { bestc = cur; memcpy(bestu, gu, sizeof gu); }
    }
    memcpy(gu, bestu, sizeof gu);
    int FS = getenv("POPT_FS") ? atoi(getenv("POPT_FS")) : 200; long long *dv = malloc(8 * FS); long long mn = -1; double tm = 0, lq = 0;
    for (int z = 0; z < FS; z++) { for (int i = 0; i < H; i++) rand_v(i); if (INV) rand_inv(); long long df = eval(); dv[z] = df; tm += df > CAP ? CAP : df; if (mn < 0 || df < mn) mn = df; }
    for (int i = 1; i < FS; i++) { long long t = dv[i]; int j = i; while (j > 0 && dv[j - 1] > t) { dv[j] = dv[j - 1]; j--; } dv[j] = t; }
    for (int i = 0; i < FS / 4; i++) lq += dv[i];
    printf("POPT n=%lld train=%.1f fresh_mean=%.1f fresh_lowq=%.1f fresh_min=%lld levels:", n, bestc, tm / FS, lq / (FS / 4), mn);
    for (int i = 0; i < H; i++) printf(" %d", gu[i]); printf("\n"); return 0;
  }
  if (!strcmp(mode, "zsample")) {   // S seed u1..uH
    long long S = atoll(argv[a++]); seed(strtoull(argv[a++], 0, 10));
    for (int i = 0; i < H; i++) gu[i] = atoi(argv[a++]);
    ZERO_ONLY = 1; time_t last = 0; long long hits = 0, hist[8] = {0};
    for (long long z = 0; z < S; z++) { for (int i = 0; i < H; i++) rand_v(i); if (INV) rand_inv();
      long long df = eval();
      { time_t now = time(NULL); if (!last) last = now; if (now - last >= 60) { last = now; printf("PROGRESS evals=%lld hits=%lld\n", z + 1, hits); fflush(stdout); } }
      if (df == 0) { hits++; ZERO_ONLY = 0; long long chk = eval(); ZERO_ONLY = 1;
        printf("%s n=%lld d=%d k=%d defect=%lld set:", chk == 0 ? "WITNESS" : "FALSEZERO", n, d, K, chk); print_set(); printf("\n"); fflush(stdout); } }
    printf("ZSAMPLE done S=%lld hits=%lld\n", S, hits); return 0;
  }
  if (!strcmp(mode, "lsample")) {   // S seed u1..uH : histogram of defects (no early abort)
    long long S = atoll(argv[a++]); seed(strtoull(argv[a++], 0, 10));
    for (int i = 0; i < H; i++) gu[i] = atoi(argv[a++]);
    long long hist[41]; memset(hist, 0, sizeof hist);
    for (long long z = 0; z < S; z++) { for (int i = 0; i < H; i++) rand_v(i); if (INV) rand_inv(); long long df = eval(); hist[df / 2 < 40 ? df / 2 : 40]++;
      if (df == 0) { printf("WITNESS n=%lld d=%d k=%d defect=0 set:", n, d, K); print_set(); printf("\n"); fflush(stdout); } }
    printf("HIST(pairs)"); for (int i = 0; i <= 40; i++) if (hist[i]) printf(" %d:%lld", i, hist[i]); printf("\n"); return 0;
  }
  fprintf(stderr, "unknown mode\n"); return 1;
}
