/* Universal route charts over F_4^4 for the alphabet {a, A=a^-1, b, B=b^-1} and label-reduced words of length 4.
   Chart: A_a, A_b in GL_4(F_4), b_a, b_b in F_4^4; A_A = A_a^-1, b_A = A_a^-1 b_a (same for b).
   M_w = [A4 A3 A2 b1 | A4 A3 b2 | A4 b3 | b4] must be nonsingular for all 108 words.
   Mode "field": A = multiplication by alpha/beta in F_256 (= F_4^4), b_a = 1, b_b = gamma, exhaustive.
   Mode "anneal": general matrices, simulated annealing on the number of singular words. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
typedef unsigned char u8;
static u8 F4mul[4][4] = {{0,0,0,0},{0,1,2,3},{0,2,3,1},{0,3,1,2}};
static u8 F4inv[4] = {0,1,3,2};
typedef struct { u8 m[4][4]; } Mat;
typedef struct { u8 v[4]; } Vec;
static Vec mv(const Mat *A, Vec x) { Vec y; for (int i = 0; i < 4; i++) { u8 s = 0; for (int j = 0; j < 4; j++) s ^= F4mul[A->m[i][j]][x.v[j]]; y.v[i] = s; } return y; }
static Mat mm(const Mat *A, const Mat *B) { Mat C; for (int i = 0; i < 4; i++) for (int j = 0; j < 4; j++) { u8 s = 0; for (int k = 0; k < 4; k++) s ^= F4mul[A->m[i][k]][B->m[k][j]]; C.m[i][j] = s; } return C; }
static int rank4(u8 M[4][4]) { u8 a[4][4]; memcpy(a, M, 16); int r = 0;
    for (int c = 0; c < 4 && r < 4; c++) { int p = -1; for (int i = r; i < 4; i++) if (a[i][c]) { p = i; break; } if (p < 0) continue;
        if (p != r) for (int j = 0; j < 4; j++) { u8 t = a[p][j]; a[p][j] = a[r][j]; a[r][j] = t; }
        u8 iv = F4inv[a[r][c]]; for (int j = 0; j < 4; j++) a[r][j] = F4mul[iv][a[r][j]];
        for (int i = 0; i < 4; i++) if (i != r && a[i][c]) { u8 f = a[i][c]; for (int j = 0; j < 4; j++) a[i][j] ^= F4mul[f][a[r][j]]; }
        r++; }
    return r; }
static int inverse(const Mat *A, Mat *R) { u8 a[4][8]; for (int i = 0; i < 4; i++) for (int j = 0; j < 8; j++) a[i][j] = j < 4 ? A->m[i][j] : (j - 4 == i);
    for (int c = 0; c < 4; c++) { int p = -1; for (int i = c; i < 4; i++) if (a[i][c]) { p = i; break; } if (p < 0) return 0;
        if (p != c) for (int j = 0; j < 8; j++) { u8 t = a[p][j]; a[p][j] = a[c][j]; a[c][j] = t; }
        u8 iv = F4inv[a[c][c]]; for (int j = 0; j < 8; j++) a[c][j] = F4mul[iv][a[c][j]];
        for (int i = 0; i < 4; i++) if (i != c && a[i][c]) { u8 f = a[i][c]; for (int j = 0; j < 8; j++) a[i][j] ^= F4mul[f][a[c][j]]; } }
    for (int i = 0; i < 4; i++) for (int j = 0; j < 4; j++) R->m[i][j] = a[i][j + 4]; return 1; }
/* cost = number of label-reduced words of length 4 with singular M_w */
static Mat Am[4]; static Vec Bv[4];
static int setup(const Mat *Aa, Vec ba, const Mat *Ab, Vec bb) {
    Am[0] = *Aa; Bv[0] = ba; if (!inverse(Aa, &Am[1])) return 0; Bv[1] = mv(&Am[1], ba);
    Am[2] = *Ab; Bv[2] = bb; if (!inverse(Ab, &Am[3])) return 0; Bv[3] = mv(&Am[3], bb); return 1; }
static int cost(int verbose) {
    int bad = 0;
    for (int t1 = 0; t1 < 4; t1++) for (int t2 = 0; t2 < 4; t2++) { if (t2 == (t1 ^ 1)) continue;
      for (int t3 = 0; t3 < 4; t3++) { if (t3 == (t2 ^ 1)) continue;
        for (int t4 = 0; t4 < 4; t4++) { if (t4 == (t3 ^ 1)) continue;
          Vec c1 = mv(&Am[t4], mv(&Am[t3], mv(&Am[t2], Bv[t1]))), c2 = mv(&Am[t4], mv(&Am[t3], Bv[t2])), c3 = mv(&Am[t4], Bv[t3]), c4 = Bv[t4];
          u8 M[4][4]; for (int i = 0; i < 4; i++) { M[i][0] = c1.v[i]; M[i][1] = c2.v[i]; M[i][2] = c3.v[i]; M[i][3] = c4.v[i]; }
          if (rank4(M) < 4) { bad++; if (verbose) printf("  singular word %d%d%d%d\n", t1, t2, t3, t4); } } } }
    return bad; }

static int vecid(Vec x) { return x.v[0] | x.v[1] << 2 | x.v[2] << 4 | x.v[3] << 6; }
static Vec vadd(Vec x, Vec y) { Vec z; for (int i = 0; i < 4; i++) z.v[i] = x.v[i] ^ y.v[i]; return z; }
static Vec vscale(u8 c, Vec x) { Vec z; for (int i = 0; i < 4; i++) z.v[i] = F4mul[c][x.v[i]]; return z; }
typedef struct { unsigned long long w[4]; } Mask;
static Mask span3(Vec p1, Vec p2, Vec v) { Mask m = {{0,0,0,0}};
    for (int a = 0; a < 4; a++) for (int b = 0; b < 4; b++) for (int c = 0; c < 4; c++) {
        int id = vecid(vadd(vadd(vscale(a, p1), vscale(b, p2)), vscale(c, v))); m.w[id >> 6] |= 1ULL << (id & 63); }
    return m; }
static int d2cost(int verbose) {
    int bad = 0;
    for (int t1 = 0; t1 < 4; t1++) for (int t2 = 0; t2 < 4; t2++) { if (t2 == (t1 ^ 1)) continue; if ((t1 >> 1) == (t2 >> 1)) continue;
        Vec p1 = mv(&Am[t2], Bv[t1]), p2 = Bv[t2];
        Mask P = span3(p1, p2, p1);   /* the plane itself (third vector inside P) */
        Mask seen[16]; int ns = 0;
        for (int r = 0; r < 4; r++) for (int k = 0; k < 3; k++) {
            Vec v = k == 0 ? mv(&Am[t2], mv(&Am[t1], Bv[r])) : k == 1 ? mv(&Am[t2], Bv[r]) : Bv[r];
            int id = vecid(v); if (P.w[id >> 6] >> (id & 63) & 1) continue;   /* v in P: no new hyperplane */
            Mask H = span3(p1, p2, v); int dup = 0;
            for (int i = 0; i < ns; i++) if (!memcmp(&seen[i], &H, sizeof H)) { dup = 1; break; }
            if (!dup) seen[ns++] = H; }
        if (ns < 5) { bad += 5 - ns; if (verbose) printf("  pair %d%d covers %d of 5 hyperplanes\n", t1, t2, ns); }
    }
    return bad; }

static unsigned long long rs = 88172645463325252ULL;
static unsigned long long rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static void printchart(const Mat *Aa, Vec ba, const Mat *Ab, Vec bb) {
    printf("A_a ="); for (int i = 0; i < 4; i++) { printf(" ["); for (int j = 0; j < 4; j++) printf("%d", Aa->m[i][j]); printf("]"); } printf("  b_a = ["); for (int i = 0; i < 4; i++) printf("%d", ba.v[i]); printf("]\n");
    printf("A_b ="); for (int i = 0; i < 4; i++) { printf(" ["); for (int j = 0; j < 4; j++) printf("%d", Ab->m[i][j]); printf("]"); } printf("  b_b = ["); for (int i = 0; i < 4; i++) printf("%d", bb.v[i]); printf("]\n"); }
int main(int argc, char **argv) {
    rs ^= (unsigned long long)(argc > 1 ? atoll(argv[1]) : time(NULL)) * 0x9E3779B97F4A7C15ULL;
    long iters = argc > 2 ? atol(argv[2]) : 2000000;
    Mat Aa, Ab; Vec ba, bb; int best = 1 << 30;
    for (int restart = 0; ; restart++) {
        do { for (int i = 0; i < 4; i++) for (int j = 0; j < 4; j++) { Aa.m[i][j] = rnd() & 3; Ab.m[i][j] = rnd() & 3; }
             for (int i = 0; i < 4; i++) { ba.v[i] = rnd() & 3; bb.v[i] = rnd() & 3; } } while (!setup(&Aa, ba, &Ab, bb));
        int c = cost(0) + d2cost(0); double T = 2.0;
        for (long it = 0; it < iters && c > 0; it++) {
            Mat Aa2 = Aa, Ab2 = Ab; Vec ba2 = ba, bb2 = bb; int which = rnd() % 4;
            if (which == 0) Aa2.m[rnd() & 3][rnd() & 3] = rnd() & 3; else if (which == 1) Ab2.m[rnd() & 3][rnd() & 3] = rnd() & 3;
            else if (which == 2) ba2.v[rnd() & 3] = rnd() & 3; else bb2.v[rnd() & 3] = rnd() & 3;
            if (!setup(&Aa2, ba2, &Ab2, bb2)) { setup(&Aa, ba, &Ab, bb); continue; }
            int c2 = cost(0) + d2cost(0);
            if (c2 <= c || (double)(rnd() % 1000000) / 1e6 < __builtin_exp((c - c2) / T)) { Aa = Aa2; Ab = Ab2; ba = ba2; bb = bb2; c = c2; }
            else setup(&Aa, ba, &Ab, bb);
            T *= 0.999995; if (T < 0.05) T = 0.05;
        }
        if (c < best) { best = c; printf("restart %d: cost %d\n", restart, c); fflush(stdout); }
        if (c == 0) { setup(&Aa, ba, &Ab, bb); printchart(&Aa, ba, &Ab, bb); printf("check cost %d d2 %d\n", cost(1), d2cost(1)); return 0; }
    }
}
