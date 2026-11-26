// indep_aff.c -- third independent diameter check for G = (F_p^2 x| Q) x Z_k (cay_mgk group file, header p,-L0,k or p,L).
// Different model of the group law: element (x,j,y) <-> affine matrix [[B_x, y],[0,1]] (B_x = rho(x)^-1, computed here by
// Gauss-Jordan) times Z_k component j; left multiplication s*e corresponds to matrix product M(e) M(s) (and j_e + j_s).
// Level of a product is decoded from its 2x2 block through a direct p^4 table. State per vertex: 2 bits (0 unseen,
// 1 current layer, 2 next layer, 3 older), N/4 bytes; push with 64-bit CAS; OpenMP.
// usage: indep_aff FILE d K lev vr vc ... [lev vr vc (involution)]   (levels: j*L0+i)
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
typedef int64_t i64; typedef uint64_t u64;
static i64 p; static int L0, ZK; static int *Bm; static i64 *skey; static int *sidx;
static i64 md(i64 a){ a %= p; return a < 0 ? a + p : a; }
static i64 pw(i64 b, i64 e){ i64 r = 1; b = md(b); while (e) { if (e & 1) r = r * b % p; b = b * b % p; e >>= 1; } return r; }
static i64 invm(i64 a, i64 m){ i64 t = 0, nt = 1, r = m, nr = md(a); while (nr) { i64 q = r / nr, tmp = t - q * nt; t = nt; nt = tmp; tmp = r - q * nr; r = nr; nr = tmp; } if (r != 1) { fprintf(stderr, "det not a unit\n"); exit(5); } return t < 0 ? t + m : t; }
static void ginv(const int *a, int *o){ // adjugate / det (ring Z_C, composite allowed)
  i64 di = invm(a[0] * (i64)a[3] - a[1] * (i64)a[2], p);
  o[0] = (int)md(a[3] * di); o[1] = (int)md(-a[1] * di); o[2] = (int)md(-a[2] * di); o[3] = (int)md(a[0] * di);
}
static inline i64 bcode(i64 a, i64 b, i64 c, i64 d){ return ((a * p + b) * p + c) * p + d; }
static int bfind(i64 c){ int lo = 0, hi = L0 - 1; while (lo <= hi) { int mid = (lo + hi) / 2; if (skey[mid] == c) return sidx[mid]; if (skey[mid] < c) lo = mid + 1; else hi = mid - 1; } return -1; }
static i64 *tkey; static int cmpk(const void *a, const void *b){ i64 x = tkey[*(const int *)a], y = tkey[*(const int *)b]; return x < y ? -1 : x > y; }
int main(int argc, char **argv){
  FILE *f = fopen(argv[1], "rb"); int hd[2]; if (!f || fread(hd, 4, 2, f) != 2) return 2; p = hd[0];
  if (hd[1] < 0) { L0 = -hd[1]; if (fread(&ZK, 4, 1, f) != 1 || ZK < 1) return 2; } else { L0 = hd[1]; ZK = 1; }
  int *R = malloc(16 * (size_t)L0); if (fread(R, 16, L0, f) != (size_t)L0) return 2; fclose(f);
  Bm = malloc(16 * (size_t)L0); tkey = malloc(8 * (size_t)L0); sidx = malloc(4 * (size_t)L0); skey = malloc(8 * (size_t)L0);
  for (int x = 0; x < L0; x++) { ginv(R + 4 * x, Bm + 4 * x); int *b = Bm + 4 * x; tkey[x] = bcode(b[0], b[1], b[2], b[3]); sidx[x] = x; }
  qsort(sidx, L0, 4, cmpk); for (int i = 0; i < L0; i++) skey[i] = tkey[sidx[i]];
  for (int i = 1; i < L0; i++) if (skey[i] == skey[i - 1]) { fprintf(stderr, "dup\n"); return 4; }
  int d = atoi(argv[2]), K = atoi(argv[3]), H = d / 2, INV = d & 1, a = 4, ng = 0;
  int sx[64], sj[64]; i64 sv0[64], sv1[64];
  for (int i = 0; i < H + INV; i++) {
    int lev = atoi(argv[a++]); i64 vr = atoll(argv[a++]), vc = atoll(argv[a++]);
    int x = lev % L0, j = lev / L0; sx[ng] = x; sj[ng] = j; sv0[ng] = vr; sv1[ng] = vc; ng++;
    if (i < H) { // inverse of M(s) = [[B, v],[0,1]] is [[B^-1, -B^-1 v],[0,1]]; B^-1 = R[x]
      const int *Ri = R + 4 * x; int Bi[4] = {Ri[0], Ri[1], Ri[2], Ri[3]}; int bi = bfind(bcode(Bi[0], Bi[1], Bi[2], Bi[3]));
      if (bi < 0) { fprintf(stderr, "inverse not in Q\n"); return 4; }
      sx[ng] = bi; sj[ng] = (ZK - j) % ZK; sv0[ng] = md(-(Bi[0] * vr + Bi[1] * vc)); sv1[ng] = md(-(Bi[2] * vr + Bi[3] * vc)); ng++; }
  }
  int *PT = malloc(4 * (size_t)ng * L0);   // PT[g*L0+x] = index of B_x B_s(g), validated once
  for (int g = 0; g < ng; g++) for (int x = 0; x < L0; x++) { const int *B = Bm + 4 * x, *S = Bm + 4 * sx[g];
    i64 c0 = (B[0] * (i64)S[0] + B[1] * (i64)S[2]) % p, c1 = (B[0] * (i64)S[1] + B[1] * (i64)S[3]) % p, c2 = (B[2] * (i64)S[0] + B[3] * (i64)S[2]) % p, c3 = (B[2] * (i64)S[1] + B[3] * (i64)S[3]) % p;
    int x2 = bfind(bcode(c0, c1, c2, c3)); if (x2 < 0) { fprintf(stderr, "product not in Q\n"); return 7; } PT[g * L0 + x] = x2; }
  i64 P2 = p * p, N = (i64)L0 * ZK * P2, NW = (N + 31) / 32;   // 32 vertices per u64 (2 bits each)
  u64 *st = calloc(NW, 8); if (!st) { fprintf(stderr, "oom\n"); return 6; }
  st[0] = 1; i64 tot = 1; printf("order %lld layers 1", (long long)N); fflush(stdout);
  for (int t = 1; t <= K; t++) {
    i64 nn = 0;
    #pragma omp parallel for schedule(dynamic, 1024) reduction(+:nn)
    for (i64 w = 0; w < NW; w++) {
      u64 word = st[w]; if (!word) continue;
      for (int q = 0; q < 32; q++) {
        if (((word >> (2 * q)) & 3) != 1) continue;
        i64 e = w * 32 + q; i64 lv = e / P2, y = e % P2; int x = lv % L0, j = lv / L0; i64 y0 = y / p, y1 = y % p;
        const int *B = Bm + 4 * x;
        for (int g = 0; g < ng; g++) {   // M(e) M(s): block B_x B_s, translation B_x v_s + y
          i64 z0 = (B[0] * sv0[g] + B[1] * sv1[g] + y0) % p, z1 = (B[2] * sv0[g] + B[3] * sv1[g] + y1) % p;
          int x2 = PT[g * L0 + x];
          i64 id = ((i64)((j + sj[g]) % ZK) * L0 + x2) * P2 + z0 * p + z1;
          u64 *wp = &st[id >> 5]; int sh = 2 * (id & 31);
          u64 old = __atomic_load_n(wp, __ATOMIC_RELAXED);
          while (((old >> sh) & 3) == 0) {
            if (__atomic_compare_exchange_n(wp, &old, old | (2ULL << sh), 1, __ATOMIC_RELAXED, __ATOMIC_RELAXED)) { nn++; break; }
          }
        }
      }
    }
    #pragma omp parallel for schedule(static)
    for (i64 w = 0; w < NW; w++) { u64 v = st[w]; if (!v) continue; u64 r = 0;
      for (int q = 0; q < 32; q++) { u64 s2 = (v >> (2 * q)) & 3; u64 n2 = s2 == 1 ? 3 : (s2 == 2 ? 1 : s2); r |= n2 << (2 * q); } st[w] = r; }
    tot += nn; printf(" %lld", (long long)nn); fflush(stdout); if (!nn) break;
  }
  printf("\nreached %lld defect %lld\n", (long long)tot, (long long)(N - tot)); return 0;
}
