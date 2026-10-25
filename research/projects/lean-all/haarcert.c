/* haarcert.c: word certificates for Haar graphs of SL(2,p) x Z_n (project lean-all).

   usage: haarcert SOLFILE KIND OUT.bin
     SOLFILE  research/frontier/sols format: "D D sl p n n N order", then the generators "idx mat(a,b,c,d) z=k"
     KIND     even  : x = s0 * (s1^-1 s2) (s3^-1 s4) ...      (L = D-1 letters, D even)
              left  : x = (s0^-1 s1) (s2^-1 s3) ...            (L = D-1 letters, D odd)
              right : x = (s0 s1^-1) (s2 s3^-1) ...            (L = D-1 letters, D odd)
   Output: for every element in slot order, 5 bytes (little endian): the field sum_t digit_t << (4 t).
   Slot order (the same as LeanAll/HaarSL.lean): element (a,b,c,d,z) has index i*n + z with
     i = (a*(p-1) + (c-1))*p + d      if c != 0,
     i = p*p*(p-1) + (a-1)*p + b      if c == 0,
   so batch b (p*n slots) covers the indices [b*p*n, (b+1)*p*n). Missing elements abort with an error.
   Every word is re-evaluated before it is written. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

static int P, NZ, DEG, DIAM;
static int S[16][5];      /* a b c d z */

typedef struct { int a, b, c, d, z; } El;

static El mul(El x, El y) {
  El r;
  r.a = (x.a * y.a + x.b * y.c) % P;
  r.b = (x.a * y.b + x.b * y.d) % P;
  r.c = (x.c * y.a + x.d * y.c) % P;
  r.d = (x.c * y.b + x.d * y.d) % P;
  r.z = (x.z + y.z) % NZ;
  return r;
}
static El inv(El x) {
  El r = { x.d, (P - x.b) % P, (P - x.c) % P, x.a, (NZ - x.z) % NZ };
  return r;
}
static El gen(int u) { El r = { S[u][0], S[u][1], S[u][2], S[u][3], S[u][4] }; return r; }
static long long idx(El x) {
  long long i;
  if (x.c != 0) i = ((long long)x.a * (P - 1) + (x.c - 1)) * P + x.d;
  else i = (long long)P * P * (P - 1) + (long long)(x.a - 1) * P + x.b;
  return i * NZ + x.z;
}
static int pinv(int x) { for (int y = 1; y < P; y++) if (x * y % P == 1) return y; return -1; }
static El el_of(long long k) {
  El x;
  long long i = k / NZ;
  x.z = (int)(k % NZ);
  long long half = (long long)P * P * (P - 1);
  if (i < half) {
    x.d = (int)(i % P);
    long long q = i / P;
    x.c = (int)(q % (P - 1)) + 1;
    x.a = (int)(q / (P - 1));
    /* b = (a d - 1) / c */
    x.b = (int)((((long long)x.a * x.d - 1) % P + P) % P * pinv(x.c) % P);
  } else {
    long long r = i - half;
    x.b = (int)(r % P);
    x.a = (int)(r / P) + 1;
    x.c = 0;
    x.d = pinv(x.a);
  }
  return x;
}

int main(int argc, char **argv) {
  if (argc != 4) { fprintf(stderr, "usage: haarcert SOLFILE even|left|right OUT.bin\n"); return 2; }
  FILE *f = fopen(argv[1], "r");
  if (!f) { perror("sol"); return 2; }
  char grp[16], w1[8], w2[8];
  long long order;
  if (fscanf(f, "%d %d %15s %d %7s %d %7s %lld", &DEG, &DIAM, grp, &P, w1, &NZ, w2, &order) != 8 || strcmp(grp, "sl")) {
    fprintf(stderr, "expected 'D D sl p n n N order'\n"); return 2;
  }
  for (int u = 0; u < DEG; u++) {
    long long dummy;
    if (fscanf(f, "%lld mat(%d,%d,%d,%d) z=%d", &dummy, &S[u][0], &S[u][1], &S[u][2], &S[u][3], &S[u][4]) != 6) {
      fprintf(stderr, "bad generator line %d\n", u); return 2;
    }
  }
  fclose(f);
  long long G = (long long)P * (P * P - 1) * NZ;
  if (G != order) { fprintf(stderr, "order mismatch %lld %lld\n", G, order); return 2; }
  int kind = !strcmp(argv[2], "even") ? 0 : !strcmp(argv[2], "left") ? 1 : !strcmp(argv[2], "right") ? 2 : -1;
  if (kind < 0) { fprintf(stderr, "bad kind\n"); return 2; }
  int L = DIAM - 1;
  int K = (kind == 0) ? (DIAM - 2) / 2 : (DIAM - 1) / 2;   /* number of pairs */
  if ((kind == 0) != (DIAM % 2 == 0)) { fprintf(stderr, "kind does not match the parity of D\n"); return 2; }
  if (L > 9 || DEG > 16) { fprintf(stderr, "L <= 9 and Delta <= 16 needed\n"); return 2; }
  /* the pair elements: left (s^-1 t), right (s t^-1) */
  int NP = DEG * DEG;
  El pr[256];
  for (int s = 0; s < DEG; s++) for (int t = 0; t < DEG; t++)
    pr[s * DEG + t] = (kind == 2) ? mul(gen(s), inv(gen(t))) : mul(inv(gen(s)), gen(t));
  /* BFS over pairs, right multiplication */
  int8_t *lay = malloc(G);
  uint32_t *par = malloc(G * sizeof(uint32_t));
  uint8_t *pid = malloc(G);
  if (!lay || !par || !pid) { fprintf(stderr, "out of memory\n"); return 1; }
  memset(lay, -1, G);
  El one = { 1, 0, 0, 1, 0 };
  long long i0 = idx(one);
  lay[i0] = 0;
  long long *fr = malloc(G * sizeof(long long)), *nf = malloc(G * sizeof(long long));
  long long nfr = 1, cnt = 1;
  fr[0] = i0;
  for (int l = 1; l <= K; l++) {
    long long nn = 0;
    for (long long q = 0; q < nfr; q++) {
      El x = el_of(fr[q]);
      for (int k = 0; k < NP; k++) {
        long long j = idx(mul(x, pr[k]));
        if (lay[j] < 0) { lay[j] = l; par[j] = (uint32_t)fr[q]; pid[j] = k; nf[nn++] = j; }
      }
    }
    long long *t = fr; fr = nf; nf = t; nfr = nn; cnt += nn;
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
    /* unwind the pairs of y */
    int pairs[8], m = lay[y];
    for (int q = m - 1; q >= 0; q--) { pairs[q] = pid[y]; y = par[y]; }
    for (int q = m; q < K; q++) pairs[q] = 0;      /* pad with s0^-1 s0 = 1 */
    int off = 0;
    if (kind == 0) { dig[0] = s0; off = 1; }
    for (int q = 0; q < K; q++) { dig[off + 2 * q] = pairs[q] / DEG; dig[off + 2 * q + 1] = pairs[q] % DEG; }
    /* re-evaluate */
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
