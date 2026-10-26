/* haarcert.c: word certificates for Haar graphs of SL(2,p) x Z_n and PSL(2,p) x Z_n (project lean-all).

   usage: haarcert SOLFILE KIND OUT.bin [scan|scan2 [FROM TO]]
     SOLFILE  research/frontier/sols format: "D D sl|psl p n n N order", then the generators "idx mat(a,b,c,d) z=k"
     KIND     even  : x = s0 * (s1^-1 s2) (s3^-1 s4) ...      (L = D-1 letters, D even)
              left  : x = (s0^-1 s1) (s2^-1 s3) ...            (L = D-1 letters, D odd)
              right : x = (s0 s1^-1) (s2 s3^-1) ...            (L = D-1 letters, D odd)
   Output: for every element in slot order, 5 bytes (little endian): the field sum_t digit_t << (4 t).
   Slot order (the same as LeanAll/HaarSL.lean): element (a,b,c,d,z) has index i*n + z with
     i = (a*(p-1) + (c-1))*p + d      if c != 0,
     i = p*p*(p-1) + (a-1)*p + b      if c == 0,
   so batch b (p*n slots) covers the indices [b*p*n, (b+1)*p*n). Missing elements abort with an error.
   For psl (LeanAll/HaarPSL.lean) elements are sign-normalised matrices (c in 1..h, or c = 0 and a in 1..h, with
   h = (p-1)/2) and the batch of (a,b,c,d,z) is a*h + (c-1) if c != 0, p*h + (a-1) if c == 0; the slot in the batch
   is d*n + z if c != 0, b*n + z if c == 0. A word for x may evaluate to x or -x in SL(2,p) x Z_n.
   Every word is re-evaluated before it is written.
   With `scan` the BFS finds each layer by scanning all elements instead of keeping frontier lists (6 bytes per
   element instead of 22; the parents, hence the words, differ from the default mode). `scan2` is `scan` without the
   parent table (2 bytes per element): the parent of x is recomputed as x * pair^-1, so the words are those of `scan`.
   With FROM TO only the words of the elements FROM <= k < TO are written (the same bytes as that part of the full
   file). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

static int P, NZ, DEG, DIAM, PSL, HP;
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
static El neg(El x) { El r = { (P - x.a) % P, (P - x.b) % P, (P - x.c) % P, (P - x.d) % P, x.z }; return r; }
static long long idx(El x) {
  long long i;
  if (PSL) {
    if (x.c != 0 ? x.c > HP : x.a > HP) x = neg(x);
    if (x.c != 0) return ((long long)x.a * HP + (x.c - 1)) * P * NZ + (long long)x.d * NZ + x.z;
    return ((long long)P * HP + (x.a - 1)) * P * NZ + (long long)x.b * NZ + x.z;
  }
  if (x.c != 0) i = ((long long)x.a * (P - 1) + (x.c - 1)) * P + x.d;
  else i = (long long)P * P * (P - 1) + (long long)(x.a - 1) * P + x.b;
  return i * NZ + x.z;
}
static int INV[4096];
static int pinv(int x) { return INV[x]; }
static void init_inv(void) { for (int x = 1; x < P; x++) for (int y = 1; y < P; y++) if (x * y % P == 1) INV[x] = y; }
static El el_of(long long k) {
  El x;
  if (PSL) {
    long long bi = k / ((long long)P * NZ), j = k % ((long long)P * NZ);
    x.z = (int)(j % NZ);
    if (bi < (long long)P * HP) {
      x.a = (int)(bi / HP); x.c = (int)(bi % HP) + 1; x.d = (int)(j / NZ);
      x.b = (int)((((long long)x.a * x.d - 1) % P + P) % P * pinv(x.c) % P);
    } else {
      x.a = (int)(bi - (long long)P * HP) + 1; x.c = 0; x.b = (int)(j / NZ); x.d = pinv(x.a);
    }
    return x;
  }
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
  if (!(argc == 4 || ((argc == 5 || argc == 7) && (!strcmp(argv[4], "scan") || !strcmp(argv[4], "scan2"))))) {
    fprintf(stderr, "usage: haarcert SOLFILE even|left|right OUT.bin [scan|scan2 [FROM TO]]\n"); return 2;
  }
  int scan = argc >= 5;
  int nopar = argc >= 5 && !strcmp(argv[4], "scan2");
  FILE *f = fopen(argv[1], "r");
  if (!f) { perror("sol"); return 2; }
  char grp[16], w1[8], w2[8];
  long long order;
  if (fscanf(f, "%d %d %15s %d %7s %d %7s %lld", &DEG, &DIAM, grp, &P, w1, &NZ, w2, &order) != 8 || (strcmp(grp, "sl") && strcmp(grp, "psl"))) {
    fprintf(stderr, "expected 'D D sl|psl p n n N order'\n"); return 2;
  }
  PSL = !strcmp(grp, "psl");
  if (P >= 4096) { fprintf(stderr, "p < 4096 needed\n"); return 2; }
  init_inv();
  HP = (P - 1) / 2;
  for (int u = 0; u < DEG; u++) {
    long long dummy;
    if (fscanf(f, "%lld mat(%d,%d,%d,%d) z=%d", &dummy, &S[u][0], &S[u][1], &S[u][2], &S[u][3], &S[u][4]) != 6) {
      fprintf(stderr, "bad generator line %d\n", u); return 2;
    }
  }
  fclose(f);
  long long G = (long long)P * (P * P - 1) * NZ / (PSL ? 2 : 1);
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
  El pinvs[256];
  for (int k = 0; k < NP; k++) pinvs[k] = inv(pr[k]);
  int8_t *lay = malloc(G);
  uint32_t *par = nopar ? NULL : malloc(G * sizeof(uint32_t));
  uint8_t *pid = malloc(G);
  if (!lay || (!nopar && !par) || !pid) { fprintf(stderr, "out of memory\n"); return 1; }
  if (G >= (1LL << 32)) { fprintf(stderr, "group too large\n"); return 1; }
  memset(lay, -1, G);
  El one = { 1, 0, 0, 1, 0 };
  long long i0 = idx(one);
  lay[i0] = 0;
  if (scan) {
    long long cnt = 1;
    for (int l = 1; l <= K; l++) {
      long long nn = 0;
      for (long long q = 0; q < G; q++) {
        if (lay[q] != l - 1) continue;
        El x = el_of(q);
        for (int k = 0; k < NP; k++) {
          long long j = idx(mul(x, pr[k]));
          if (lay[j] < 0) { lay[j] = l; if (par) par[j] = (uint32_t)q; pid[j] = k; nn++; }
        }
      }
      cnt += nn;
      fprintf(stderr, "layer %d: %lld new, %lld reached of %lld\n", l, nn, cnt, G);
    }
  } else {
    long long *fr = malloc(G * sizeof(long long)), *nf = malloc(G * sizeof(long long));
    if (!fr || !nf) { fprintf(stderr, "out of memory\n"); return 1; }
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
    free(fr); free(nf);
  }
  FILE *o = fopen(argv[3], "wb");
  if (!o) { perror("out"); return 2; }
  long long missing = 0;
  uint8_t buf[5];
  long long k0 = 0, k1 = G;   /* FROM TO: only the words of the elements k0 <= k < k1 */
  if (argc == 7) { k0 = atoll(argv[5]); k1 = atoll(argv[6]); }
  if (k0 < 0 || k1 > G || k0 > k1) { fprintf(stderr, "bad range\n"); return 2; }
  for (long long k = k0; k < k1; k++) {
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
    for (int q = m - 1; q >= 0; q--) {
      pairs[q] = pid[y];
      y = par ? par[y] : idx(mul(el_of(y), pinvs[pid[y]]));
    }
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
