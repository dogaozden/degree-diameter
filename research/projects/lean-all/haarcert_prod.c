/* haarcert_prod.c: word certificates for Haar graphs of SL(2,p) x SL(2,q) x Z_n and PSL(2,p) x SL(2,q) x Z_n
   (project lean-all, LeanAll/HaarProd.lean), of PSL(2,p) x SL(2,8) x Z_n (LeanAll/HaarGF8.lean), and of
   (P)SL(2,p) x PSL(2,q) x Z_n (LeanAll/HaarProdP.lean).

   usage: haarcert_prod SOLFILE KIND OUT.bin
     SOLFILE  research/frontier/sols format: "D D prod sl|psl p sl|psl q [poly x^3+x+1] n n N order", then the generators
              "idx prod[mat(a,b,c,d);mat(a,b,c,d)] z=k"
     KIND     even | left | right, as in haarcert.c
   Output: 5 bytes per element in slot order, the field sum_t digit_t << (4 t).
   Slot order: element (A1, A2, z) has index ((b2 * q + j2) * B + b1) * (p n) + j1, where
     b1, j1: the batch and slot of (A1, z) in the first factor (SL: B = p^2 - 1 batches, as in haarcert.c;
             PSL: B = p h + h sign-normalised batches, h = (p-1)/2, as for psl in haarcert.c), and
     b2, j2: the batch of A2 in SL(2,q) (a2 (q-1) + c2 - 1 if c2 != 0, q (q-1) + a2 - 1 if c2 == 0) and its free
             entry (d2 if c2 != 0, b2 if c2 == 0); for a psl second factor, of the sign-normalised A2 (c2 in
             1..h2, or c2 = 0 and a2 in 1..h2, h2 = (q-1)/2): a2 h2 + c2 - 1 if c2 != 0, q h2 + a2 - 1 if c2 == 0.
   With q = 8 and "poly x^3+x+1" the second factor is SL(2, GF(8)), entries as 3-bit codes (bit i = coefficient
   of x^i), products modulo x^3 + x + 1.
   Every word is re-evaluated before it is written (up to the signs of A1 and A2 for psl). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

static int P, Q, NZ, DEG, DIAM, PSL, HP, F8, PSL2, HQ;

/* the second factor's field: Z/Q, or GF(8) when F8 */
static int qmul(int a, int b) {
  if (!F8) return a * b % Q;
  int r = 0;
  for (int i = 0; i < 3; i++) if (b >> i & 1) r ^= a << i;
  for (int i = 4; i >= 3; i--) if (r >> i & 1) r ^= 0xb << (i - 3);
  return r;
}
static int qadd(int a, int b) { return F8 ? a ^ b : (a + b) % Q; }
static int qneg(int a) { return F8 ? a : (Q - a) % Q; }
static int qinv(int a) { for (int y = 1; y < Q; y++) if (qmul(a, y) == 1) return y; return -1; }
static long long B1, NS;  /* batches of the first factor, slots per batch */
static int S[16][9];

typedef struct { int a, b, c, d, a2, b2, c2, d2, z; } El;

static El mul(El x, El y) {
  El r;
  r.a = (x.a * y.a + x.b * y.c) % P;
  r.b = (x.a * y.b + x.b * y.d) % P;
  r.c = (x.c * y.a + x.d * y.c) % P;
  r.d = (x.c * y.b + x.d * y.d) % P;
  r.a2 = qadd(qmul(x.a2, y.a2), qmul(x.b2, y.c2));
  r.b2 = qadd(qmul(x.a2, y.b2), qmul(x.b2, y.d2));
  r.c2 = qadd(qmul(x.c2, y.a2), qmul(x.d2, y.c2));
  r.d2 = qadd(qmul(x.c2, y.b2), qmul(x.d2, y.d2));
  r.z = (x.z + y.z) % NZ;
  return r;
}
static El inv(El x) {
  El r = { x.d, (P - x.b) % P, (P - x.c) % P, x.a, x.d2, qneg(x.b2), qneg(x.c2), x.a2, (NZ - x.z) % NZ };
  return r;
}
static El gen(int u) {
  El r = { S[u][0], S[u][1], S[u][2], S[u][3], S[u][4], S[u][5], S[u][6], S[u][7], S[u][8] };
  return r;
}
static int pinv(int x, int m) { for (int y = 1; y < m; y++) if (x * y % m == 1) return y; return -1; }
static long long idx(El x) {
  long long b1, j1, b2, j2;
  if (PSL && (x.c != 0 ? x.c > HP : x.a > HP)) {
    x.a = (P - x.a) % P; x.b = (P - x.b) % P; x.c = (P - x.c) % P; x.d = (P - x.d) % P;
  }
  if (PSL) {
    if (x.c != 0) { b1 = (long long)x.a * HP + (x.c - 1); j1 = (long long)x.d * NZ + x.z; }
    else { b1 = (long long)P * HP + (x.a - 1); j1 = (long long)x.b * NZ + x.z; }
  } else {
    if (x.c != 0) { b1 = (long long)x.a * (P - 1) + (x.c - 1); j1 = (long long)x.d * NZ + x.z; }
    else { b1 = (long long)P * (P - 1) + (x.a - 1); j1 = (long long)x.b * NZ + x.z; }
  }
  if (PSL2 && (x.c2 != 0 ? x.c2 > HQ : x.a2 > HQ)) {
    x.a2 = qneg(x.a2); x.b2 = qneg(x.b2); x.c2 = qneg(x.c2); x.d2 = qneg(x.d2);
  }
  int cm2 = PSL2 ? HQ : Q - 1;
  if (x.c2 != 0) { b2 = (long long)x.a2 * cm2 + (x.c2 - 1); j2 = x.d2; }
  else { b2 = (long long)Q * cm2 + (x.a2 - 1); j2 = x.b2; }
  return ((b2 * Q + j2) * B1 + b1) * NS + j1;
}
static El el_of(long long k) {
  El x;
  long long j1 = k % NS, i = k / NS, b1 = i % B1, r = i / B1, j2 = r % Q, b2 = r / Q;
  x.z = (int)(j1 % NZ);
  int e = (int)(j1 / NZ);
  long long half = PSL ? (long long)P * HP : (long long)P * (P - 1);
  int cm = PSL ? HP : P - 1;
  if (b1 < half) {
    x.a = (int)(b1 / cm); x.c = (int)(b1 % cm) + 1; x.d = e;
    x.b = (int)((((long long)x.a * x.d - 1) % P + P) % P * pinv(x.c, P) % P);
  } else {
    x.a = (int)(b1 - half) + 1; x.c = 0; x.b = e; x.d = pinv(x.a, P);
  }
  int cm2 = PSL2 ? HQ : Q - 1;
  long long half2 = (long long)Q * cm2;
  if (b2 < half2) {
    x.a2 = (int)(b2 / cm2); x.c2 = (int)(b2 % cm2) + 1; x.d2 = (int)j2;
    x.b2 = qmul(qadd(qmul(x.a2, x.d2), qneg(1)), qinv(x.c2));
  } else {
    x.a2 = (int)(b2 - half2) + 1; x.c2 = 0; x.b2 = (int)j2; x.d2 = qinv(x.a2);
  }
  return x;
}

int main(int argc, char **argv) {
  if (argc != 4) { fprintf(stderr, "usage: haarcert_prod SOLFILE even|left|right OUT.bin\n"); return 2; }
  FILE *f = fopen(argv[1], "r");
  if (!f) { perror("sol"); return 2; }
  char g0[16], g1[16], g2[16], w1[32], w2[8];
  long long order;
  if (fscanf(f, "%d %d %15s %15s %d %15s %d %31s", &DEG, &DIAM, g0, g1, &P, g2, &Q, w1) != 8
      || strcmp(g0, "prod") || (strcmp(g1, "sl") && strcmp(g1, "psl")) || (strcmp(g2, "sl") && strcmp(g2, "psl"))) {
    fprintf(stderr, "expected 'D D prod sl|psl p sl|psl q [poly x^3+x+1] n n N order'\n"); return 2;
  }
  if (!strcmp(w1, "poly")) {
    if (fscanf(f, "%31s %7s", w1, w2) != 2 || strcmp(w1, "x^3+x+1") || Q != 8) {
      fprintf(stderr, "only GF(8) = F2[x]/(x^3+x+1)\n"); return 2;
    }
    F8 = 1;
  }
  if (fscanf(f, "%d %7s %lld", &NZ, w2, &order) != 3) { fprintf(stderr, "bad header\n"); return 2; }
  PSL = !strcmp(g1, "psl");
  PSL2 = !strcmp(g2, "psl");
  if (PSL2 && F8) { fprintf(stderr, "psl second factor over Z/q only\n"); return 2; }
  HP = (P - 1) / 2;
  HQ = (Q - 1) / 2;
  B1 = PSL ? (long long)P * HP + HP : (long long)P * P - 1;
  NS = (long long)P * NZ;
  for (int u = 0; u < DEG; u++) {
    long long dummy;
    if (fscanf(f, "%lld prod[mat(%d,%d,%d,%d);mat(%d,%d,%d,%d)] z=%d", &dummy, &S[u][0], &S[u][1], &S[u][2],
               &S[u][3], &S[u][4], &S[u][5], &S[u][6], &S[u][7], &S[u][8]) != 10) {
      fprintf(stderr, "bad generator line %d\n", u); return 2;
    }
    if (qadd(qmul(S[u][4], S[u][7]), qneg(qmul(S[u][5], S[u][6]))) != 1 ||
        ((S[u][0] * S[u][3] - S[u][1] * S[u][2]) % P + P) % P != 1) {
      fprintf(stderr, "generator %d: determinant is not 1\n", u); return 2;
    }
  }
  fclose(f);
  long long B2 = PSL2 ? (long long)Q * HQ + HQ : (long long)Q * Q - 1;
  long long G = B1 * NS * B2 * Q;
  if (G != order) { fprintf(stderr, "order mismatch %lld %lld\n", G, order); return 2; }
  int kind = !strcmp(argv[2], "even") ? 0 : !strcmp(argv[2], "left") ? 1 : !strcmp(argv[2], "right") ? 2 : -1;
  if (kind < 0) { fprintf(stderr, "bad kind\n"); return 2; }
  int L = DIAM - 1;
  int K = (kind == 0) ? (DIAM - 2) / 2 : (DIAM - 1) / 2;
  if ((kind == 0) != (DIAM % 2 == 0)) { fprintf(stderr, "kind does not match the parity of D\n"); return 2; }
  if (L > 9 || DEG > 16) { fprintf(stderr, "L <= 9 and Delta <= 16 needed\n"); return 2; }
  int NP = DEG * DEG;
  El pr[256];
  for (int s = 0; s < DEG; s++) for (int t = 0; t < DEG; t++)
    pr[s * DEG + t] = (kind == 2) ? mul(gen(s), inv(gen(t))) : mul(inv(gen(s)), gen(t));
  int8_t *lay = malloc(G);
  uint32_t *par = malloc(G * sizeof(uint32_t));
  uint8_t *pid = malloc(G);
  uint32_t *fr = malloc(G * sizeof(uint32_t)), *nf = malloc(G * sizeof(uint32_t));
  if (!lay || !par || !pid || !fr || !nf) { fprintf(stderr, "out of memory\n"); return 1; }
  memset(lay, -1, G);
  El one = { 1, 0, 0, 1, 1, 0, 0, 1, 0 };
  long long i0 = idx(one);
  lay[i0] = 0;
  long long nfr = 1, cnt = 1;
  fr[0] = (uint32_t)i0;
  for (int l = 1; l <= K; l++) {
    long long nn = 0;
    for (long long q = 0; q < nfr; q++) {
      El x = el_of(fr[q]);
      for (int k = 0; k < NP; k++) {
        long long j = idx(mul(x, pr[k]));
        if (lay[j] < 0) { lay[j] = l; par[j] = fr[q]; pid[j] = k; nf[nn++] = (uint32_t)j; }
      }
    }
    uint32_t *t = fr; fr = nf; nf = t; nfr = nn; cnt += nn;
    fprintf(stderr, "layer %d: %lld new, %lld reached of %lld\n", l, nn, cnt, G);
  }
  FILE *o = fopen(argv[3], "wb");
  if (!o) { perror("out"); return 2; }
  long long missing = 0;
  uint8_t buf[5];
  for (long long k = 0; k < G; k++) {
    El x = el_of(k);
    if (idx(x) != k) { fprintf(stderr, "index error at %lld\n", k); return 1; }
    int dig[9];
    int s0 = -1;
    long long y = k;
    if (kind == 0) {
      for (int u = 0; u < DEG; u++) {
        long long j = idx(mul(inv(gen(u)), x));
        if (lay[j] >= 0) { s0 = u; y = j; break; }
      }
      if (s0 < 0) { missing++; memset(buf, 0, 5); fwrite(buf, 1, 5, o); continue; }
    } else if (lay[y] < 0) { missing++; memset(buf, 0, 5); fwrite(buf, 1, 5, o); continue; }
    int pairs[8], m = lay[y];
    for (int q = m - 1; q >= 0; q--) { pairs[q] = pid[y]; y = par[y]; }
    for (int q = m; q < K; q++) pairs[q] = 0;
    int off = 0;
    if (kind == 0) { dig[0] = s0; off = 1; }
    for (int q = 0; q < K; q++) { dig[off + 2 * q] = pairs[q] / DEG; dig[off + 2 * q + 1] = pairs[q] % DEG; }
    El w = one;
    for (int t = 0; t < L; t++) {
      int invstep = (kind == 1) ? (t % 2 == 0) : (t % 2 == 1);
      w = mul(w, invstep ? inv(gen(dig[t])) : gen(dig[t]));
    }
    if (idx(w) != k) { fprintf(stderr, "word check failed at %lld\n", k); return 1; }
    uint64_t F = 0;
    for (int t = 0; t < L; t++) F |= (uint64_t)dig[t] << (4 * t);
    for (int b = 0; b < 5; b++) buf[b] = (F >> (8 * b)) & 255;
    fwrite(buf, 1, 5, o);
  }
  fclose(o);
  if (missing) { fprintf(stderr, "%lld elements have no word\n", missing); return 1; }
  fprintf(stderr, "ok: %lld words, L = %d, kind %s\n", G, L, argv[2]);
  return 0;
}
