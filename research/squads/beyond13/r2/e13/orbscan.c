/* orbscan.c (card c05, beyond-d13 round 1).
 * Haar graph H(G,S): vertices (g,A),(g,B), edges (g,A)~(s g,B). G = SL(2,p) x Z_n or PSL(2,p) x Z_n.
 * Exact diameter test via eccentricities (right multiplication is transitive on each side):
 *   even D: cost = #B-vertices not within D-1 of (e,A)            (one BFS)
 *   odd  D: cost = #A-vertices not within D-1 of (e,A) + #B-vertices not within D-1 of (e,B)   (two BFS)
 *   cost 0  <=>  diameter <= D.  (odd D: an early abort returns only the first term, which is > 0.)
 * Scan family: S = {e, x, a x, a^2 x}, a = conj by g=[[0,-1],[1,-1]] (order 3) times z -> r z (r of order 3 mod n).
 * Group element index g = z*S3 + slot, slot encodes SL element K=[[a,b],[c,d]]: slot = (a p + c) p + t with
 * t = b/a (a != 0) or slot = c p + t with t = d/c (a = 0), K = rep(v) u(t).  PSL: canonical sign (first nonzero of (a,c)
 * in 1..(p-1)/2).
 * Build: gcc -O3 -march=native -o orbscan orbscan.c
 * Usage: orbscan eval FILE D
 *        orbscan scan sl|psl p n D seconds seed OUTPREFIX [maxsol]
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

static int P, NC, PSLF, S3, NVS, RZ;
static long long NTOT;
static int NG;
static int *INV, *SLOTS, *TMP;
static uint8_t *VALID;
static int DG;
static uint32_t *Lf[8], *Li[8];
static uint32_t *stA, *stB, gen_;
static uint32_t *cur, *nxt;
static uint32_t E_IDX;

static int md(long long x) { x %= P; if (x < 0) x += P; return (int)x; }

static int encode(int a, int b, int c, int d) {
  if (PSLF) { int f = a ? a : c; if (f > (P - 1) / 2) { a = md(-a); b = md(-b); c = md(-c); d = md(-d); } }
  if (a) { int t = md((long long)b * INV[a]); return (a * P + c) * P + t; }
  int t = md((long long)d * INV[c]);
  return c * P + t;
}
static void decode(int slot, int *m) {
  if (slot < P * P) { int c = slot / P, t = slot % P; m[0] = 0; m[1] = md(-(long long)INV[c]); m[2] = c; m[3] = md((long long)c * t); return; }
  int v = slot / P, t = slot % P, a = v / P, c = v % P;
  m[0] = a; m[1] = md((long long)a * t); m[2] = c; m[3] = md((long long)c * t + INV[a]);
}
static int valid_slot(int slot) {
  if (slot < P || slot >= S3) return 0;
  if (!PSLF) return 1;
  int m[4]; decode(slot, m);
  int f = m[0] ? m[0] : m[2];
  return f <= (P - 1) / 2;
}
static void mul(const int *M, const int *K, int *R) {
  R[0] = md((long long)M[0] * K[0] + (long long)M[1] * K[2]);
  R[1] = md((long long)M[0] * K[1] + (long long)M[1] * K[3]);
  R[2] = md((long long)M[2] * K[0] + (long long)M[3] * K[2]);
  R[3] = md((long long)M[2] * K[1] + (long long)M[3] * K[3]);
}
/* left multiplication table by (M, w) into out[g], g = z*S3 + slot */
static void build_left(const int *M, int w, uint32_t *out) {
  int m[4], R[4];
  for (int k = 0; k < NVS; k++) { int s = SLOTS[k]; decode(s, m); mul(M, m, R); TMP[s] = encode(R[0], R[1], R[2], R[3]); }
  for (int z = 0; z < NC; z++) {
    int zz = (z + w) % NC;
    for (int k = 0; k < NVS; k++) { int s = SLOTS[k]; out[(size_t)z * S3 + s] = (uint32_t)(TMP[s] + zz * S3); }
  }
}
static void build_gen(int j, const int *M, int w) {
  int inv[4] = { M[3], md(-M[1]), md(-M[2]), M[0] };
  build_left(M, w, Lf[j]);
  build_left(inv, (NC - w) % NC, Li[j]);
}
/* BFS from (src side) src; steps expansions; counts visited on each side */
static void bfs(int srcA, uint32_t src, int steps, long long *cA, long long *cB) {
  long long nA = 0, nB = 0; int nc = 1, nn;
  gen_++;
  if (gen_ == 0) { memset(stA, 0, sizeof(uint32_t) * NG); memset(stB, 0, sizeof(uint32_t) * NG); gen_ = 1; }
  if (srcA) { stA[src] = gen_; nA = 1; cur[0] = src; } else { stB[src] = gen_; nB = 1; cur[0] = src + NG; }
  for (int s = 0; s < steps && nc; s++) {
    nn = 0;
    for (int q = 0; q < nc; q++) {
      uint32_t e = cur[q];
      if (e < (uint32_t)NG) {
        for (int j = 0; j < DG; j++) { uint32_t h = Lf[j][e]; if (stB[h] != gen_) { stB[h] = gen_; nxt[nn++] = h + NG; nB++; } }
      } else {
        uint32_t h = e - NG;
        for (int j = 0; j < DG; j++) { uint32_t a = Li[j][h]; if (stA[a] != gen_) { stA[a] = gen_; nxt[nn++] = a; nA++; } }
      }
    }
    uint32_t *t = cur; cur = nxt; nxt = t; nc = nn;
  }
  *cA = nA; *cB = nB;
}
static long long evalS(int D) {
  long long cA, cB;
  if (D % 2 == 0) { bfs(1, E_IDX, D - 1, &cA, &cB); return NTOT - cB; }
  bfs(1, E_IDX, D - 1, &cA, &cB);
  long long c1 = NTOT - cA;
  if (c1 > 0) return c1;
  bfs(0, E_IDX, D - 1, &cA, &cB);
  return c1 + (NTOT - cB);
}
static void setup(const char *fam, int p, int n) {
  P = p; NC = n; PSLF = strcmp(fam, "psl") == 0; S3 = P * P * P;
  INV = malloc(sizeof(int) * P); for (int x = 1; x < P; x++) for (int y = 1; y < P; y++) if ((long long)x * y % P == 1) INV[x] = y;
  SLOTS = malloc(sizeof(int) * S3); TMP = malloc(sizeof(int) * S3); VALID = calloc(S3, 1);
  NVS = 0;
  for (int s = 0; s < S3; s++) if (valid_slot(s)) { VALID[s] = 1; SLOTS[NVS++] = s; }
  NTOT = (long long)NVS * NC; NG = NC * S3;
  RZ = 0;
  if (NC > 1) { for (int r = 2; r < NC; r++) if ((long long)r * r % NC * r % NC == 1) { RZ = r; break; } }
  E_IDX = (uint32_t)(P * P);  /* identity, z = 0 */
  for (int j = 0; j < 8; j++) { Lf[j] = malloc(sizeof(uint32_t) * NG); Li[j] = malloc(sizeof(uint32_t) * NG); }
  stA = calloc(NG, sizeof(uint32_t)); stB = calloc(NG, sizeof(uint32_t));
  cur = malloc(sizeof(uint32_t) * 2 * NG); nxt = malloc(sizeof(uint32_t) * 2 * NG);
  gen_ = 0;
}
static int write_sol(const char *path, int d, int D, const char *fam, int gm[][4], int *gz) {
  FILE *f = fopen(path, "w"); if (!f) return 1;
  fprintf(f, "%d %d %s %d n %d N %lld\n", d, D, fam, P, NC, NTOT);
  for (int j = 0; j < d; j++) fprintf(f, "%d mat(%d,%d,%d,%d) z=%d\n", j, gm[j][0], gm[j][1], gm[j][2], gm[j][3], gz[j]);
  fclose(f); return 0;
}

int main(int argc, char **argv) {
  if (argc >= 3 && strcmp(argv[1], "eval") == 0) {
    FILE *f = fopen(argv[2], "r"); if (!f) { printf("no file\n"); return 1; }
    int D = atoi(argv[3]); char line[4096], fam[64]; int d, Df, p, n; long long NN;
    if (!fgets(line, sizeof line, f) || sscanf(line, "%d %d %63s %d n %d N %lld", &d, &Df, fam, &p, &n, &NN) != 6) { printf("bad header\n"); return 1; }
    setup(fam, p, n); DG = d; int gm[8][4], gz[8]; int k = 0;
    while (fgets(line, sizeof line, f) && k < d) {
      char *m = strstr(line, "mat("), *zz = strstr(line, "z=");
      if (!m || !zz) continue;
      sscanf(m, "mat(%d,%d,%d,%d)", &gm[k][0], &gm[k][1], &gm[k][2], &gm[k][3]); sscanf(zz, "z=%d", &gz[k]); k++;
    }
    fclose(f);
    if (k != d) { printf("bad file\n"); return 1; }
    for (int j = 0; j < d; j++) { for (int q = 0; q < 4; q++) gm[j][q] = md(gm[j][q]); build_gen(j, gm[j], gz[j] % NC); }
    printf("EVAL file=%s d=%d D=%d p=%d n=%d |G|=%lld cost=%lld\n", argv[2], d, D, p, n, NTOT, evalS(D));
    return 0;
  }
  if (argc >= 9 && strcmp(argv[1], "scan") == 0) {
    const char *fam = argv[2]; int p = atoi(argv[3]), n = atoi(argv[4]), D = atoi(argv[5]);
    double secs = atof(argv[6]); unsigned seed = (unsigned)atol(argv[7]); const char *outp = argv[8];
    int maxsol = argc > 9 ? atoi(argv[9]) : 3;
    setup(fam, p, n); DG = 4;
    uint32_t *perm = malloc(sizeof(uint32_t) * NG); for (int i = 0; i < NG; i++) perm[i] = i;
    uint64_t rs = seed * 2654435761ULL + 12345; 
    for (int i = NG - 1; i > 0; i--) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; int j = (int)(rs % (uint64_t)(i + 1)); uint32_t t = perm[i]; perm[i] = perm[j]; perm[j] = t; }
    int G[3][3] = { {0, P - 1, 0}, {0, 0, 0}, {0, 0, 0} }; (void)G;
    int g1[4] = { 0, md(-1), 1, md(-1) };   /* g = [[0,-1],[1,-1]] */
    int g2[4] = { md(-1), 1, md(-1), 0 };   /* g^2 = g^{-1} */
    long long hist[64] = {0}; long long tries = 0, found = 0; long long best = -1;
    clock_t t0 = clock();
    int gm[4][4], gz[4];
    for (long long pi = 0; pi < NG; pi++) {
      if ((double)(clock() - t0) / CLOCKS_PER_SEC > secs) break;
      uint32_t g = perm[pi]; int slot = g % S3, z = g / S3;
      if (!VALID[slot] || g == E_IDX) continue;
      int m[4], R[4], R2[4], m1[4], m2[4];
      decode(slot, m);
      mul(g1, m, R); mul(R, g2, m1);            /* alpha(x) matrix */
      int z1 = (int)((long long)RZ * z % NC);
      uint32_t i1 = (uint32_t)(z1 * S3 + encode(m1[0], m1[1], m1[2], m1[3]));
      if (i1 == g) continue;                     /* alpha-fixed */
      mul(g1, m1, R2); mul(R2, g2, m2);          /* alpha^2(x) matrix */
      int z2 = (int)((long long)RZ * z1 % NC);
      uint32_t i2 = (uint32_t)(z2 * S3 + encode(m2[0], m2[1], m2[2], m2[3]));
      if (g > i1 || g > i2) continue;            /* one representative per orbit */
      int ident[4] = { 1, 0, 0, 1 };
      memcpy(gm[0], ident, sizeof ident); gz[0] = 0;
      memcpy(gm[1], m, sizeof m); gz[1] = z;
      memcpy(gm[2], m1, sizeof m1); gz[2] = z1;
      memcpy(gm[3], m2, sizeof m2); gz[3] = z2;
      for (int j = 0; j < 4; j++) build_gen(j, gm[j], gz[j] % NC);
      long long c = evalS(D);
      tries++;
      if (c < 64) hist[c]++; else hist[63]++;
      if (best < 0 || c < best) best = c;
      if (c == 0) {
        found++;
        char path[512]; snprintf(path, sizeof path, "%s_%lld.txt", outp, found);
        write_sol(path, 4, D, fam, gm, gz);
        printf("SOL #%lld tries=%lld x=mat(%d,%d,%d,%d) z=%d file=%s\n", found, tries, m[0], m[1], m[2], m[3], z, path);
        fflush(stdout);
        if (found >= maxsol) break;
      }
    }
    printf("SCAN %s p=%d n=%d |G|=%lld 2|G|=%lld D=%d tries=%lld found=%lld best=%lld time=%.1fs\n", fam, p, n, NTOT, 2 * NTOT, D, tries, found, best,
           (double)(clock() - t0) / CLOCKS_PER_SEC);
    printf("HIST");
    for (int c = 0; c < 64; c++) if (hist[c]) printf(" %d:%lld", c, hist[c]);
    printf("\n");
    return 0;
  }
  printf("usage: orbscan eval FILE D | orbscan scan sl|psl p n D seconds seed OUTPREFIX [maxsol]\n");
  return 1;
}
