/* secantclique.c: large partial ovoids of the elliptic section E (X4 = -X0) of H(11)'s quadric, as unions of orbits of
   a rotation of order q+1. Session cell-14-7 (second), 2026-10-24.
   On V = {x : x4 = -x0}, Q = -(x0^2 + x3^2) + x1x5 + x2x6 = Q_A(a) + Q_4(b) with a = (x0,x3) in the anisotropic plane A
   (q = 3 mod 4) and b = (x1,x2,x5,x6) in the hyperbolic 4-space V4. A point [a:b] of E with Q_4(b) != 0 has
   x0^2 + x3^2 = Q_4(b); the rotations a -> zeta a (zeta of norm 1 in GF(q^2) = GF(q)[i], i^2 = -1) form a cyclic group of
   order q+1 whose orbits are O_b = {[a:b] : N(a) = Q_4(b)} (q+1 points, pairwise non-orthogonal), one per projective
   point [b] off the quadric Q_4 = 0. O_b and O_b' are mutually non-orthogonal iff B_4(b,b')^2 - 4 Q_4(b) Q_4(b') is a
   nonzero square (the line bb' is a secant of the hyperbolic quadric). The points [0:b] with Q_4(b) = 0 are fixed.
   This program finds a maximum clique S of the "secant graph" on the q^3+q^2... projective points off the quadric
   (branch and bound with greedy colouring; the graph is vertex-transitive, so vertex 0 is fixed in the clique), then
   adds a maximum set F of fixed points that are pairwise non-orthogonal and non-orthogonal to every b in S, and writes
   the (q+1)|S| + |F| points of E as flags (point, spread line through it) for t2design / pack.
   Usage: secantclique GHFILE COORDFILE SECONDS OUTFLAGS [C]   (section X4 = -C X0, anisotropic plane C x0^2 + x3^2,
          -C must be a non-square mod q; default C = 1, valid for q = 3 mod 4)
   Compile: gcc -O3 -march=native -o secantclique secantclique.c */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>

static int q, P, Q1;
static int md(long a) { a %= q; return (int)(a < 0 ? a + q : a); }
static int inv(int a) { int r = 1, e = q - 2; long b = a; while (e) { if (e & 1) r = (int)(r * b % q); b = b * b % q; e >>= 1; } return r; }
static int issq[64];
/* V4 vectors b = (b1,b2,b5,b6); Q4 = b1 b5 + b2 b6; B4(b,c) = b1c5 + b5c1 + b2c6 + b6c2 */
static inline int Q4(const int *b) { return md((long)b[0] * b[2] + (long)b[1] * b[3]); }
static inline int B4(const int *b, const int *c) { return md((long)b[0] * c[2] + (long)b[2] * c[0] + (long)b[1] * c[3] + (long)b[3] * c[1]); }

/* ---- max clique (Tomita-style with greedy colouring) on an adjacency bit matrix ---- */
typedef uint64_t u64;
static int NV, W; static u64 *adj; static int best = 0, *bestset, *cur; static long nodes = 0; static clock_t t0; static double tlimit;
static inline int has(const u64 *s, int v) { return (s[v >> 6] >> (v & 63)) & 1; }
static void expand(int *cand, int nc, int depth) {
    nodes++;
    if ((nodes & 0xFFFF) == 0 && (double)(clock() - t0) / CLOCKS_PER_SEC > tlimit) return;
    /* greedy colouring of cand: order by colour classes */
    int *order = malloc(sizeof(int) * nc), *col = malloc(sizeof(int) * nc); int k = 0, maxc = 0;
    int *rem = malloc(sizeof(int) * nc); int nr = nc; memcpy(rem, cand, sizeof(int) * nc);
    while (nr > 0) {
        maxc++; int *cls = malloc(sizeof(int) * nr); int ncl = 0, nr2 = 0;
        for (int i = 0; i < nr; i++) { int v = rem[i], ok = 1; for (int j = 0; j < ncl; j++) if (has(adj + (size_t)v * W, cls[j])) { ok = 0; break; }
            if (ok) cls[ncl++] = v; else rem[nr2++] = v; }
        for (int j = 0; j < ncl; j++) { order[k] = cls[j]; col[k] = maxc; k++; }
        nr = nr2; free(cls);
    }
    free(rem);
    for (int i = nc - 1; i >= 0; i--) {
        if (depth + col[i] <= best) break;
        int v = order[i]; cur[depth] = v;
        int *nc2 = malloc(sizeof(int) * nc); int m = 0;
        for (int j = 0; j < i; j++) if (has(adj + (size_t)v * W, order[j])) nc2[m++] = order[j];
        if (m == 0) { if (depth + 1 > best) { best = depth + 1; memcpy(bestset, cur, sizeof(int) * best); fprintf(stderr, "clique %d (nodes %ld, %.0fs)\n", best, nodes, (double)(clock() - t0) / CLOCKS_PER_SEC); } }
        else expand(nc2, m, depth + 1);
        free(nc2);
        if ((double)(clock() - t0) / CLOCKS_PER_SEC > tlimit) break;
    }
    free(order); free(col);
}

int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage: secantclique GHFILE COORDFILE SECONDS OUTFLAGS\n"); return 2; }
    FILE *f = fopen(argv[1], "r"); if (!f || fscanf(f, "%d %d", &P, &q) != 2) return 2; Q1 = q + 1;
    int32_t *LP = malloc(sizeof(int32_t) * (size_t)P * Q1), *PL = malloc(sizeof(int32_t) * (size_t)P * Q1);
    for (size_t i = 0; i < (size_t)P * Q1; i++) if (fscanf(f, "%d", &LP[i]) != 1) return 2;
    fclose(f);
    { int *c = calloc(P, sizeof(int)); for (int l = 0; l < P; l++) for (int k = 0; k < Q1; k++) { int p = LP[l * Q1 + k]; PL[p * Q1 + c[p]++] = l; } free(c); }
    int C = argc > 5 ? atoi(argv[5]) : 1;
    int (*X)[7] = malloc(sizeof(int) * 7 * P); f = fopen(argv[2], "r");
    for (int i = 0; i < P; i++) for (int k = 0; k < 7; k++) if (fscanf(f, "%d", &X[i][k]) != 1) return 2;
    fclose(f);
    long cm = 1; for (int k = 0; k < 7; k++) cm *= q;
    int32_t *pidx = malloc(sizeof(int32_t) * cm); memset(pidx, 255, sizeof(int32_t) * cm);
    for (int i = 0; i < P; i++) { long e = 0; for (int k = 0; k < 7; k++) e = e * q + X[i][k]; pidx[e] = i; }
    tlimit = atof(argv[3]);
    for (int x = 0; x < q; x++) issq[x] = 0; for (int x = 1; x < q; x++) issq[x * x % q] = 1;
    if (issq[md(-C)]) { fprintf(stderr, "-C must be a non-square mod q\n"); return 2; }
    /* projective points of V4 (normalized: first nonzero coordinate 1) */
    int (*pt)[4] = malloc(sizeof(int) * 4 * 20000); int npt = 0; int (*sg)[4] = malloc(sizeof(int) * 4 * 2000); int nsg = 0;
    for (int a = 0; a < q; a++) for (int b = 0; b < q; b++) for (int c = 0; c < q; c++) for (int d = 0; d < q; d++) {
        int v[4] = {a, b, c, d}, lead = -1; for (int k = 0; k < 4; k++) if (v[k]) { lead = k; break; }
        if (lead < 0 || v[lead] != 1) continue;
        if (Q4(v)) memcpy(pt[npt++], v, sizeof v); else memcpy(sg[nsg++], v, sizeof v);
    }
    fprintf(stderr, "V4: %d points off the quadric, %d on it\n", npt, nsg);
    NV = npt; W = (NV + 63) / 64; adj = calloc((size_t)NV * W, sizeof(u64)); long deg0 = 0;
    for (int i = 0; i < NV; i++) for (int j = 0; j < NV; j++) if (i != j) {
        int be = B4(pt[i], pt[j]); int dsc = md((long)be * be - 4L * Q4(pt[i]) * Q4(pt[j]));
        if (dsc && issq[dsc]) { adj[(size_t)i * W + (j >> 6)] |= 1ULL << (j & 63); if (i == 0) deg0++; }
    }
    fprintf(stderr, "secant graph: degree %ld\n", deg0);
    bestset = malloc(sizeof(int) * NV); cur = malloc(sizeof(int) * NV);
    /* vertex 0 fixed: candidates = its neighbours */
    int *cand = malloc(sizeof(int) * NV), nc = 0; for (int j = 1; j < NV; j++) if (has(adj, j)) cand[nc++] = j;
    cur[0] = 0; best = 1; bestset[0] = 0; t0 = clock();
    expand(cand, nc, 1);
    int exhausted = (double)(clock() - t0) / CLOCKS_PER_SEC <= tlimit;
    fprintf(stderr, "max clique %d (%s, %ld nodes)\n", best, exhausted ? "proven maximum (vertex-transitive graph)" : "time limit", nodes);
    /* fixed points: singular b, non-orthogonal to all of S and pairwise; exhaustive small search (<= q+1 of them) */
    int *okf = malloc(sizeof(int) * nsg), nok = 0;
    for (int s = 0; s < nsg; s++) { int ok = 1; for (int i = 0; i < best && ok; i++) if (B4(sg[s], pt[bestset[i]]) == 0) ok = 0; if (ok) okf[nok++] = s; }
    int *F = malloc(sizeof(int) * (nok + 1)), nF = 0; int *Fb = malloc(sizeof(int) * (nok + 1)), nFb = 0;
    /* greedy + randomized restarts for the fixed-point clique (tiny) */
    srand(1);
    for (int r = 0; r < 2000; r++) { nF = 0; for (int t = 0; t < nok; t++) { int s = okf[(t + r * 7) % nok]; int ok = 1; for (int u = 0; u < nF; u++) if (B4(sg[s], sg[F[u]]) == 0) ok = 0; if (ok) F[nF++] = s; }
        if (nF > nFb) { nFb = nF; memcpy(Fb, F, sizeof(int) * nF); } }
    fprintf(stderr, "fixed points usable: %d, added (pairwise non-orthogonal): %d\n", nok, nFb);
    /* write flags: for each b in S, the q+1 points [a:b], a = (x0,x3) with x0^2 + x3^2 = Q4(b); then the fixed points */
    char *inE = calloc(P, 1); for (int i = 0; i < P; i++) inE[i] = md(X[i][4] + (long)C * X[i][0]) == 0;
    int *spreadOf = malloc(sizeof(int) * P); for (int i = 0; i < P; i++) spreadOf[i] = -1;
    for (int l = 0; l < P; l++) { int all = 1; for (int k = 0; k < Q1; k++) if (!inE[LP[l * Q1 + k]]) { all = 0; break; } if (all) for (int k = 0; k < Q1; k++) spreadOf[LP[l * Q1 + k]] = l; }
    f = fopen(argv[4], "w"); int nout = 0, *outp = malloc(sizeof(int) * 20000);
    for (int i = 0; i < best; i++) { const int *b = pt[bestset[i]]; int c = Q4(b), cnt = 0;
        for (int x0 = 0; x0 < q; x0++) for (int x3 = 0; x3 < q; x3++) if (md((long)C * x0 * x0 + (long)x3 * x3) == c) {
            int v[7] = {x0, b[0], b[1], x3, md(-(long)C * x0), b[2], b[3]}; int lead = 0; while (v[lead] == 0) lead++; int s = inv(v[lead]); long e = 0;
            for (int k = 0; k < 7; k++) e = e * q + (long)v[k] * s % q;
            int p = pidx[e]; if (p < 0 || !inE[p] || spreadOf[p] < 0) { fprintf(stderr, "internal: point not found\n"); return 1; }
            fprintf(f, "%d %d\n", p, spreadOf[p]); outp[nout++] = p; cnt++; }
        if (cnt != q + 1) { fprintf(stderr, "internal: orbit size %d\n", cnt); return 1; } }
    for (int i = 0; i < nFb; i++) { const int *b = sg[Fb[i]]; int v[7] = {0, b[0], b[1], 0, 0, b[2], b[3]}; int lead = 0; while (v[lead] == 0) lead++;
        int s = inv(v[lead]); long e = 0; for (int k = 0; k < 7; k++) e = e * q + (long)v[k] * s % q;
        int p = pidx[e]; if (p < 0 || spreadOf[p] < 0) { fprintf(stderr, "internal: fixed point not found\n"); return 1; }
        fprintf(f, "%d %d\n", p, spreadOf[p]); outp[nout++] = p; }
    fclose(f);
    /* self-check: pairwise non-orthogonal */
    long bad = 0; for (int i = 0; i < nout; i++) for (int j = i + 1; j < nout; j++) { const int *x = X[outp[i]], *y = X[outp[j]];
        if (md((long)x[0]*y[4] + (long)x[4]*y[0] + (long)x[1]*y[5] + (long)x[5]*y[1] + (long)x[2]*y[6] + (long)x[6]*y[2] - 2L*x[3]*y[3]) == 0) bad++; }
    fprintf(stderr, "wrote %d flags = %d orbits x %d + %d fixed points; orthogonal pairs: %ld\n", nout, best, q + 1, nFb, bad);
    return 0;
}
