/* orbitpack.c: packings of type-2 unit zones that are unions of orbits of a Singer cycle of SL(3,q) acting on H(q).
   Session cell-14-7 (second), 2026-10-24.
   SL(3,q) acts on the split Cayley hexagon in Tits coordinates by x -> g x on (X0,X1,X2), X3 fixed, y -> g^-T y on
   (X4,X5,X6) (it preserves X0X4+X1X5+X2X6 = X3^2, and maps hexagon lines to lines: checked on all lines here).
   A Singer cycle (order q^2+q+1) acts semiregularly on points and lines; its orbits on flags have size q^2+q+1.
   An orbit is usable if its flags have pairwise disjoint zones (point zone {p} u {points collinear with p off l}, line
   zone {l} u {lines meeting l off p}); the program packs usable orbits greedily (random orders, restarts), then fills
   the gaps with single flags. Output: flags "p l" (input for t2design FLAGS= / t2cell.sh).
   Usage: orbitpack GHFILE COORDFILE SECONDS SEED OUTFLAGS     (COORDFILE from gh_build q COORDFILE)
   Compile: gcc -O3 -march=native -o orbitpack orbitpack.c */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>

static int P, q, Q1, ZN;
static int32_t *LP, *PL;
static uint64_t rs = 0x9E3779B97F4A7C15ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline int rndi(int n) { return (int)(rnd() % (uint64_t)n); }
static int md(long a) { a %= q; return (int)(a < 0 ? a + q : a); }
static int inv(int a) { int r = 1, e = q - 2; long b = a; while (e) { if (e & 1) r = (int)(r * b % q); b = b * b % q; e >>= 1; } return r; }

static int zoneP(int p, int l, int *out) { int c = 0; out[c++] = p;
    for (int a = 0; a < Q1; a++) { int L = PL[p * Q1 + a]; if (L == l) continue; for (int b = 0; b < Q1; b++) { int w = LP[L * Q1 + b]; if (w != p) out[c++] = w; } }
    return c; }
static int zoneL(int p, int l, int *out) { int c = 0; out[c++] = l;
    for (int a = 0; a < Q1; a++) { int x = LP[l * Q1 + a]; if (x == p) continue; for (int b = 0; b < Q1; b++) { int K = PL[x * Q1 + b]; if (K != l) out[c++] = K; } }
    return c; }

static void matmul(int A[3][3], int B[3][3], int C[3][3]) { int T[3][3]; for (int i = 0; i < 3; i++) for (int j = 0; j < 3; j++) { long s = 0; for (int k = 0; k < 3; k++) s += (long)A[i][k] * B[k][j]; T[i][j] = md(s); } memcpy(C, T, sizeof(T)); }
static int isid(int A[3][3]) { for (int i = 0; i < 3; i++) for (int j = 0; j < 3; j++) if (A[i][j] != (i == j)) return 0; return 1; }

int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: orbitpack GHFILE COORDFILE SECONDS SEED OUTFLAGS\n"); return 2; }
    FILE *f = fopen(argv[1], "r"); if (!f || fscanf(f, "%d %d", &P, &q) != 2) return 2; Q1 = q + 1; ZN = q * q + 1;
    LP = malloc(sizeof(int32_t) * (size_t)P * Q1); PL = malloc(sizeof(int32_t) * (size_t)P * Q1);
    for (size_t i = 0; i < (size_t)P * Q1; i++) if (fscanf(f, "%d", &LP[i]) != 1) return 2;
    fclose(f);
    { int *c = calloc(P, sizeof(int)); for (int l = 0; l < P; l++) for (int k = 0; k < Q1; k++) { int p = LP[l * Q1 + k]; PL[p * Q1 + c[p]++] = l; } free(c); }
    double secs = atof(argv[3]); rs ^= strtoull(argv[4], 0, 10) * 0x2545F4914F6CDD1DULL;
    /* coordinates */
    int (*X)[7] = malloc(sizeof(int) * 7 * P); f = fopen(argv[2], "r");
    for (int i = 0; i < P; i++) for (int k = 0; k < 7; k++) if (fscanf(f, "%d", &X[i][k]) != 1) { fprintf(stderr, "bad coords\n"); return 2; }
    fclose(f);
    long code_max = 1; for (int k = 0; k < 7; k++) code_max *= q;
    int32_t *pidx = malloc(sizeof(int32_t) * code_max); memset(pidx, 255, sizeof(int32_t) * code_max);
    for (int i = 0; i < P; i++) { long e = 0; for (int k = 0; k < 7; k++) e = e * q + X[i][k]; pidx[e] = i; }
    /* Singer cycle: companion matrix of t^3 + c2 t^2 + c1 t - 1 with order q^2+q+1 */
    int ord = q * q + q + 1, Cm[3][3], found = 0;
    for (int c2 = 0; c2 < q && !found; c2++) for (int c1 = 0; c1 < q && !found; c1++) {
        int root = 0; for (int t = 0; t < q; t++) if (md((long)t * t * t + (long)c2 * t * t + (long)c1 * t - 1) == 0) root = 1;
        if (root) continue;
        int A[3][3] = {{0, 0, 1}, {1, 0, md(-c1)}, {0, 1, md(-c2)}};   /* companion of t^3 + c2 t^2 + c1 t - 1 */
        int Pw[3][3] = {{1,0,0},{0,1,0},{0,0,1}}; int o = 0;
        for (int k = 1; k <= ord * (q - 1); k++) { matmul(Pw, A, Pw); if (isid(Pw)) { o = k; break; } }
        if (o == ord) { memcpy(Cm, A, sizeof(A)); found = 1; fprintf(stderr, "Singer: t^3 + %d t^2 + %d t - 1, order %d\n", c2, c1, o); }
    }
    if (!found) { fprintf(stderr, "no Singer cycle found\n"); return 1; }
    /* inverse transpose */
    int Ci[3][3]; { int a=Cm[0][0],b=Cm[0][1],c=Cm[0][2],d=Cm[1][0],e=Cm[1][1],ff=Cm[1][2],g=Cm[2][0],h=Cm[2][1],ii=Cm[2][2];
        int det = md((long)a*(e*ii-ff*h) - (long)b*(d*ii-ff*g) + (long)c*(d*h-e*g)), di = inv(det);
        int adj[3][3] = {{e*ii-ff*h, -(b*ii-c*h), b*ff-c*e}, {-(d*ii-ff*g), a*ii-c*g, -(a*ff-c*d)}, {d*h-e*g, -(a*h-b*g), a*e-b*d}};
        for (int r = 0; r < 3; r++) for (int s = 0; s < 3; s++) Ci[r][s] = md((long)adj[r][s] * di); }
    int CiT[3][3]; for (int r = 0; r < 3; r++) for (int s = 0; s < 3; s++) CiT[r][s] = Ci[s][r];
    /* action on points */
    int *piP = malloc(sizeof(int) * P);
    for (int i = 0; i < P; i++) {
        int v[7]; for (int r = 0; r < 3; r++) { long s = 0, t = 0; for (int k = 0; k < 3; k++) { s += (long)Cm[r][k] * X[i][k]; t += (long)CiT[r][k] * X[i][4 + k]; } v[r] = md(s); v[4 + r] = md(t); }
        v[3] = X[i][3];
        int lead = 0; while (v[lead] == 0) lead++; int s = inv(v[lead]); long e = 0; for (int k = 0; k < 7; k++) e = e * q + (long)v[k] * s % q;
        piP[i] = pidx[e]; if (piP[i] < 0) { fprintf(stderr, "point image not found\n"); return 1; }
    }
    /* action on lines (and check that lines go to lines) */
    int *piL = malloc(sizeof(int) * P); long badl = 0;
    for (int l = 0; l < P; l++) {
        int a = piP[LP[l * Q1]], b = piP[LP[l * Q1 + 1]], img = -1;
        for (int k = 0; k < Q1 && img < 0; k++) { int L = PL[a * Q1 + k]; for (int t = 0; t < Q1; t++) if (LP[L * Q1 + t] == b) { img = L; break; } }
        if (img < 0) { badl++; continue; }
        for (int t = 2; t < Q1; t++) { int c = piP[LP[l * Q1 + t]], in = 0; for (int u = 0; u < Q1; u++) if (LP[img * Q1 + u] == c) in = 1; if (!in) badl++; }
        piL[l] = img;
    }
    if (badl) { fprintf(stderr, "the map is not an automorphism (%ld bad)\n", badl); return 1; }
    fprintf(stderr, "automorphism of order %d verified on all lines\n", ord);
    /* flag orbits: flag id = p*Q1 + k (k-th line through p) */
    long NF = (long)P * Q1; int *orb = malloc(sizeof(int) * NF); memset(orb, 255, sizeof(int) * NF);
    int norb = 0; int *rep = malloc(sizeof(int) * (NF / ord + 2));
    for (long fl = 0; fl < NF; fl++) if (orb[fl] < 0) {
        int p = (int)(fl / Q1), l = PL[fl];
        for (int k = 0; k < ord; k++) { int kk = 0; while (PL[p * Q1 + kk] != l) kk++; orb[(long)p * Q1 + kk] = norb; p = piP[p]; l = piL[l]; }
        rep[norb++] = (int)fl;
    }
    fprintf(stderr, "%d flag orbits\n", norb);
    /* usable orbits */
    int *zp = malloc(sizeof(int) * 512), *zl = malloc(sizeof(int) * 512), *zp2 = malloc(sizeof(int) * 512), *zl2 = malloc(sizeof(int) * 512);
    int *stP = calloc(P, sizeof(int)), *stL = calloc(P, sizeof(int)); int stamp = 0;
    char *usable = calloc(norb, 1); int nus = 0;
    int *op = malloc(sizeof(int) * ord), *ol = malloc(sizeof(int) * ord);
    for (int o = 0; o < norb; o++) {
        int p = rep[o] / Q1, l = PL[rep[o]];
        for (int k = 0; k < ord; k++) { op[k] = p; ol[k] = l; p = piP[p]; l = piL[l]; }
        stamp++; int ok = 1;
        for (int k = 0; k < ord && ok; k++) { int n1 = zoneP(op[k], ol[k], zp), n2 = zoneL(op[k], ol[k], zl);
            for (int i = 0; i < n1; i++) { if (stP[zp[i]] == stamp) { ok = 0; break; } stP[zp[i]] = stamp; }
            for (int i = 0; i < n2 && ok; i++) { if (stL[zl[i]] == stamp) { ok = 0; break; } stL[zl[i]] = stamp; } }
        if (ok) { usable[o] = 1; nus++; }
    }
    fprintf(stderr, "%d usable orbits (pairwise disjoint zones within the orbit)\n", nus);
    /* greedy packing of usable orbits, random orders */
    int *uo = malloc(sizeof(int) * nus); { int c = 0; for (int o = 0; o < norb; o++) if (usable[o]) uo[c++] = o; }
    char *occP = malloc(P), *occL = malloc(P); int best = -1; int *bestset = malloc(sizeof(int) * (nus + 1)), nbest = 0;
    int *cur = malloc(sizeof(int) * (nus + 1));
    clock_t c0 = clock(); int restarts = 0;
    while (restarts == 0 || (double)(clock() - c0) / CLOCKS_PER_SEC < secs) {
        restarts++;
        memset(occP, 0, P); memset(occL, 0, P); int nc = 0;
        for (int i = nus - 1; i > 0; i--) { int r = rndi(i + 1); int t = uo[i]; uo[i] = uo[r]; uo[r] = t; }
        for (int i = 0; i < nus; i++) {
            int o = uo[i], p = rep[o] / Q1, l = PL[rep[o]], ok = 1;
            for (int k = 0; k < ord; k++) { op[k] = p; ol[k] = l; p = piP[p]; l = piL[l]; }
            for (int k = 0; k < ord && ok; k++) { int n1 = zoneP(op[k], ol[k], zp), n2 = zoneL(op[k], ol[k], zl);
                for (int t = 0; t < n1; t++) if (occP[zp[t]]) { ok = 0; break; }
                for (int t = 0; t < n2 && ok; t++) if (occL[zl[t]]) { ok = 0; break; } }
            if (!ok) continue;
            for (int k = 0; k < ord; k++) { int n1 = zoneP(op[k], ol[k], zp), n2 = zoneL(op[k], ol[k], zl);
                for (int t = 0; t < n1; t++) occP[zp[t]] = 1; for (int t = 0; t < n2; t++) occL[zl[t]] = 1; }
            cur[nc++] = o;
        }
        if (nc > best) { best = nc; nbest = nc; memcpy(bestset, cur, sizeof(int) * nc); fprintf(stderr, "restart %d: %d orbits = %d flags\n", restarts, nc, nc * ord); }
    }
    /* rebuild the best and fill gaps with single flags */
    memset(occP, 0, P); memset(occL, 0, P);
    f = fopen(argv[5], "w"); long nflags = 0;
    for (int i = 0; i < nbest; i++) { int o = bestset[i], p = rep[o] / Q1, l = PL[rep[o]];
        for (int k = 0; k < ord; k++) { int n1 = zoneP(p, l, zp), n2 = zoneL(p, l, zl);
            for (int t = 0; t < n1; t++) occP[zp[t]] = 1; for (int t = 0; t < n2; t++) occL[zl[t]] = 1;
            fprintf(f, "%d %d\n", p, l); nflags++; p = piP[p]; l = piL[l]; } }
    long filled = 0;
    for (int p = 0; p < P; p++) { if (occP[p]) continue; for (int a = 0; a < Q1; a++) { int l = PL[p * Q1 + a], ok = 1;
        int n1 = zoneP(p, l, zp), n2 = zoneL(p, l, zl);
        for (int t = 0; t < n1 && ok; t++) if (occP[zp[t]]) ok = 0;
        for (int t = 0; t < n2 && ok; t++) if (occL[zl[t]]) ok = 0;
        if (!ok) continue;
        for (int t = 0; t < n1; t++) occP[zp[t]] = 1; for (int t = 0; t < n2; t++) occL[zl[t]] = 1;
        fprintf(f, "%d %d\n", p, l); nflags++; filled++; break; } }
    fclose(f);
    fprintf(stderr, "best: %d orbits (%d flags) + %ld filled = %ld flags (%d restarts)\n", nbest, nbest * ord, filled, nflags, restarts);
    (void)zp2; (void)zl2;
    return 0;
}
