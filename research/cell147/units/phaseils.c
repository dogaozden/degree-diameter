/* phaseils.c: partial ovoids of the elliptic section E (X4 = -C X0) of H(q)'s quadric built from "phase classes".
   Session cell-14-7 (second), 2026-10-24.
   V = A ⊥ V4 with A = (x0,x3), Q_A = -(C x0^2 + x3^2) = -N(a) for a = x3 + x0 s in GF(q^2) = GF(q)[s]/(s^2 + C), and
   V4 = (x1,x2,x5,x6), Q4 = x1x5 + x2x6. A point of E off the fixed set is (b,k): b a projective point of PG(3,q) with
   Q4(b) != 0 (vector normalized), a = a_b zeta^k (a_b a fixed element of norm Q4(b), zeta of order q+1 and norm 1).
   (b,k) and (b',k') are orthogonal iff Tr(a_b conj(a_b') zeta^(k-k')) = B4(b,b'), i.e. k-k' in Bad(b,b') (0, 1 or 2
   residues mod q+1); points with the same b are never orthogonal. Fixed points [0:b] (Q4(b) = 0) are orthogonal to
   (b',k') iff B4(b,b') = 0. With d | q+1, the "sub-orbits" (b, j) = {(b,k) : k = j mod d} (size (q+1)/d) conflict iff
   (j - j') mod d is in Bad(b,b') mod d. This program runs an iterated local search for a maximum independent set of
   sub-orbits (d = 1: whole rotation orbits; d = q+1: single points), adds fixed points greedily, and writes flags.
   Usage: phaseils GHFILE COORDFILE C d SECONDS SEED OUTFLAGS
   Compile: gcc -O3 -march=native -o phaseils phaseils.c */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>

static int q, P, Q1, C;
static int md(long a) { a %= q; return (int)(a < 0 ? a + q : a); }
static int inv(int a) { int r = 1, e = q - 2; long b = a; while (e) { if (e & 1) r = (int)(r * b % q); b = b * b % q; e >>= 1; } return r; }
static uint64_t rs = 0x9E3779B97F4A7C15ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline int rndi(int n) { return (int)(rnd() % (uint64_t)n); }
typedef struct { int re, im; } G;   /* re + im*s, s^2 = -C */
static G gm(G x, G y) { G r = { md((long)x.re * y.re - (long)C * x.im * y.im), md((long)x.re * y.im + (long)x.im * y.re) }; return r; }
static G gc(G x) { G r = { x.re, md(-x.im) }; return r; }
static int gN(G x) { return md((long)x.re * x.re + (long)C * x.im * x.im); }
static inline int Q4(const int *b) { return md((long)b[0] * b[2] + (long)b[1] * b[3]); }
static inline int B4(const int *b, const int *c) { return md((long)b[0] * c[2] + (long)b[2] * c[0] + (long)b[1] * c[3] + (long)b[3] * c[1]); }

int main(int argc, char **argv) {
    if (argc < 8) { fprintf(stderr, "usage: phaseils GHFILE COORDFILE C d SECONDS SEED OUTFLAGS\n"); return 2; }
    FILE *f = fopen(argv[1], "r"); if (!f || fscanf(f, "%d %d", &P, &q) != 2) return 2; Q1 = q + 1;
    int32_t *LP = malloc(sizeof(int32_t) * (size_t)P * Q1);
    for (size_t i = 0; i < (size_t)P * Q1; i++) if (fscanf(f, "%d", &LP[i]) != 1) return 2;
    fclose(f);
    int (*X)[7] = malloc(sizeof(int) * 7 * P); f = fopen(argv[2], "r");
    for (int i = 0; i < P; i++) for (int k = 0; k < 7; k++) if (fscanf(f, "%d", &X[i][k]) != 1) return 2;
    fclose(f);
    C = atoi(argv[3]); int d = atoi(argv[4]); double secs = atof(argv[5]); rs ^= strtoull(argv[6], 0, 10) * 0x2545F4914F6CDD1DULL;
    if ((q + 1) % d) { fprintf(stderr, "d must divide q+1\n"); return 2; }
    long cm = 1; for (int k = 0; k < 7; k++) cm *= q;
    int32_t *pidx = malloc(sizeof(int32_t) * cm); memset(pidx, 255, sizeof(int32_t) * cm);
    for (int i = 0; i < P; i++) { long e = 0; for (int k = 0; k < 7; k++) e = e * q + X[i][k]; pidx[e] = i; }
    /* zeta: norm 1, order q+1 */
    G zeta = {0, 0}; int found = 0;
    for (int re = 0; re < q && !found; re++) for (int im = 0; im < q && !found; im++) { G z = {re, im}; if (gN(z) != 1) continue;
        G w = z; int o = 1; while (!(w.re == 1 && w.im == 0)) { w = gm(w, z); o++; if (o > q + 2) break; } if (o == q + 1) { zeta = z; found = 1; } }
    if (!found) { fprintf(stderr, "no zeta (is -C a non-square?)\n"); return 2; }
    G *zp = malloc(sizeof(G) * (q + 1)); zp[0].re = 1; zp[0].im = 0; for (int k = 1; k <= q; k++) zp[k] = gm(zp[k - 1], zeta);
    /* projective points of V4 */
    int (*pt)[4] = malloc(sizeof(int) * 4 * 30000); int npt = 0; int (*sg)[4] = malloc(sizeof(int) * 4 * 4000); int nsg = 0;
    for (int a = 0; a < q; a++) for (int b = 0; b < q; b++) for (int c = 0; c < q; c++) for (int e = 0; e < q; e++) {
        int v[4] = {a, b, c, e}, lead = -1; for (int k = 0; k < 4; k++) if (v[k]) { lead = k; break; }
        if (lead < 0 || v[lead] != 1) continue;
        if (Q4(v)) memcpy(pt[npt++], v, sizeof v); else memcpy(sg[nsg++], v, sizeof v); }
    G *ab = malloc(sizeof(G) * npt);
    for (int i = 0; i < npt; i++) { int c = Q4(pt[i]), ok = 0; for (int re = 0; re < q && !ok; re++) for (int im = 0; im < q && !ok; im++) { G z = {re, im}; if (gN(z) == c) { ab[i] = z; ok = 1; } } if (!ok) return 3; }
    /* sub-orbit conflict graph: vertex (i, j), j in Z_d, id = i*d + j */
    int NVt = npt * d; int **adj = malloc(sizeof(int *) * NVt); int *deg = calloc(NVt, sizeof(int));
    {   int *tmpc = malloc(sizeof(int) * NVt * 2 + 16); int (*bad)[3] = malloc(sizeof(int) * 3 * npt);
        for (int i = 0; i < npt; i++) {
            /* Bad(i, i2) residues mod d */
            for (int i2 = 0; i2 < npt; i2++) { bad[i2][0] = 0; if (i2 == i) continue;
                G z = gm(ab[i], gc(ab[i2])); int beta = B4(pt[i], pt[i2]);
                for (int m = 0; m <= q; m++) { G w = gm(z, zp[m]); if (md(2L * w.re) == beta) { int r = m % d; int dup = 0; for (int t = 1; t <= bad[i2][0]; t++) if (bad[i2][t] == r) dup = 1; if (!dup) bad[i2][++bad[i2][0]] = r; } } }
            for (int j = 0; j < d; j++) { int n = 0;
                for (int i2 = 0; i2 < npt; i2++) for (int t = 1; t <= bad[i2][0]; t++) { int j2 = md(0) ; j2 = ((j - bad[i2][t]) % d + d) % d; tmpc[n++] = i2 * d + j2; }
                adj[i * d + j] = malloc(sizeof(int) * (n + 1)); memcpy(adj[i * d + j], tmpc, sizeof(int) * n); deg[i * d + j] = n; }
        }
        free(tmpc); free(bad); }
    long sd = 0; for (int v = 0; v < NVt; v++) sd += deg[v];
    fprintf(stderr, "q=%d C=%d d=%d: %d sub-orbits of size %d, average conflict degree %.1f\n", q, C, d, NVt, (q + 1) / d, (double)sd / NVt);
    /* ILS for maximum independent set */
    int *inS = calloc(NVt, sizeof(int)), *tau = calloc(NVt, sizeof(int)), *S = malloc(sizeof(int) * NVt), *pos = malloc(sizeof(int) * NVt); int ns = 0;
    #define ADD(v) do { int v_ = (v); inS[v_] = 1; pos[v_] = ns; S[ns++] = v_; for (int e_ = 0; e_ < deg[v_]; e_++) tau[adj[v_][e_]]++; } while (0)
    #define REM(v) do { int v_ = (v); inS[v_] = 0; int p_ = pos[v_]; S[p_] = S[--ns]; pos[S[p_]] = p_; for (int e_ = 0; e_ < deg[v_]; e_++) tau[adj[v_][e_]]--; } while (0)
    int *order = malloc(sizeof(int) * NVt); for (int i = 0; i < NVt; i++) order[i] = i;
    for (int i = NVt - 1; i > 0; i--) { int r = rndi(i + 1); int t = order[i]; order[i] = order[r]; order[r] = t; }
    for (int i = 0; i < NVt; i++) { int v = order[i]; if (!inS[v] && tau[v] == 0) ADD(v); }
    int *best = malloc(sizeof(int) * NVt), nbest = ns; memcpy(best, S, sizeof(int) * ns);
    fprintf(stderr, "greedy: %d sub-orbits\n", ns);
    clock_t c0 = clock(); long it = 0;
    while ((double)(clock() - c0) / CLOCKS_PER_SEC < secs) {
        it++; int v = rndi(NVt);
        if (inS[v]) continue;
        if (tau[v] == 0) ADD(v);
        else if (tau[v] == 1) { int u = -1; for (int e = 0; e < deg[v]; e++) if (inS[adj[v][e]]) { u = adj[v][e]; break; }
            REM(u); ADD(v); for (int e = 0; e < deg[u]; e++) { int w = adj[u][e]; if (!inS[w] && tau[w] == 0) ADD(w); } }
        else if (tau[v] == 2 && rndi(40) == 0) { for (int e = 0; e < deg[v]; e++) { int u = adj[v][e]; if (inS[u]) REM(u); } ADD(v); }
        if (ns > nbest) { nbest = ns; memcpy(best, S, sizeof(int) * ns); fprintf(stderr, "it %ld: %d sub-orbits = %d points\n", it, ns, ns * ((q + 1) / d)); }
        if (ns < nbest - 6) { while (ns) REM(S[ns - 1]); for (int i = 0; i < nbest; i++) ADD(best[i]); }
    }
    /* fixed points: greedy with restarts */
    int *okf = malloc(sizeof(int) * nsg), nok = 0;
    for (int s2 = 0; s2 < nsg; s2++) { int ok = 1; for (int i = 0; i < nbest && ok; i++) if (B4(sg[s2], pt[best[i] / d]) == 0) ok = 0; if (ok) okf[nok++] = s2; }
    int *F = malloc(sizeof(int) * (nok + 1)), nF = 0, *Fb = malloc(sizeof(int) * (nok + 1)), nFb = 0;
    for (int r = 0; r < 3000; r++) { nF = 0; for (int t = 0; t < nok; t++) { int s2 = okf[(t + r * 13) % (nok ? nok : 1)]; int ok = 1; for (int u = 0; u < nF; u++) if (B4(sg[s2], sg[F[u]]) == 0) ok = 0; if (ok) F[nF++] = s2; }
        if (nF > nFb) { nFb = nF; memcpy(Fb, F, sizeof(int) * nF); } }
    /* spread lines, output */
    char *inE = calloc(P, 1); for (int i = 0; i < P; i++) inE[i] = md(X[i][4] + (long)C * X[i][0]) == 0;
    int *spreadOf = malloc(sizeof(int) * P); for (int i = 0; i < P; i++) spreadOf[i] = -1;
    for (int l = 0; l < P; l++) { int all = 1; for (int k = 0; k < Q1; k++) if (!inE[LP[l * Q1 + k]]) { all = 0; break; } if (all) for (int k = 0; k < Q1; k++) spreadOf[LP[l * Q1 + k]] = l; }
    int *outp = malloc(sizeof(int) * (nbest * (q + 1) + nFb + 1)), nout = 0;
    for (int t = 0; t < nbest; t++) { int i = best[t] / d, j = best[t] % d; const int *b = pt[i];
        for (int k = j; k <= q; k += d) { G a = gm(ab[i], zp[k]); int x0 = a.im, x3 = a.re;
            int v[7] = {x0, b[0], b[1], x3, md(-(long)C * x0), b[2], b[3]}; int lead = 0; while (v[lead] == 0) lead++; int s = inv(v[lead]); long e = 0;
            for (int kk = 0; kk < 7; kk++) e = e * q + (long)v[kk] * s % q;
            int p = pidx[e]; if (p < 0 || !inE[p] || spreadOf[p] < 0) { fprintf(stderr, "internal: point not found\n"); return 1; }
            outp[nout++] = p; } }
    for (int t = 0; t < nFb; t++) { const int *b = sg[Fb[t]]; int v[7] = {0, b[0], b[1], 0, 0, b[2], b[3]}; int lead = 0; while (v[lead] == 0) lead++;
        int s = inv(v[lead]); long e = 0; for (int kk = 0; kk < 7; kk++) e = e * q + (long)v[kk] * s % q;
        int p = pidx[e]; if (p < 0 || spreadOf[p] < 0) { fprintf(stderr, "internal: fixed point not found\n"); return 1; } outp[nout++] = p; }
    long badp = 0; for (int i = 0; i < nout; i++) for (int j = i + 1; j < nout; j++) { const int *x = X[outp[i]], *y = X[outp[j]];
        if (md((long)x[0]*y[4] + (long)x[4]*y[0] + (long)x[1]*y[5] + (long)x[5]*y[1] + (long)x[2]*y[6] + (long)x[6]*y[2] - 2L*x[3]*y[3]) == 0) badp++; }
    f = fopen(argv[7], "w"); for (int i = 0; i < nout; i++) fprintf(f, "%d %d\n", outp[i], spreadOf[outp[i]]); fclose(f);
    fprintf(stderr, "best: %d sub-orbits x %d + %d fixed = %d points; orthogonal pairs %ld (%ld iterations)\n", nbest, (q + 1) / d, nFb, nout, badp, it);
    return badp ? 1 : 0;
}
