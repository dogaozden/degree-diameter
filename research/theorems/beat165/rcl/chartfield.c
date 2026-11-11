/* Exhaustive search over field charts: F_4^4 = F_256 (poly 0x11D, generator g = 2), F_4 = {0,1,w,w^2}, w = g^85.
   A_a = mult by alpha, A_b = mult by beta, b_a = 1, b_b = gamma. Cost = #singular reduced 4-words + D2 deficiency
   (all 12 patterns; also reported separately for the 8 mixed patterns). F_4-independence via coordinates in the
   F_4-basis {1, g, g^2, g^3}. Prints the best charts in the 40-digit chart format (digit code: 0,1,w,w^2 -> 0,1,2,3). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef unsigned char u8;
static u8 EXP[512], LOG[256];
static u8 gmul(u8 a, u8 b) { if (!a || !b) return 0; return EXP[LOG[a] + LOG[b]]; }
static u8 ginv(u8 a) { return EXP[255 - LOG[a]]; }
static u8 F4of[256];       /* code (0..3) of an F_4 element of F_256, 255 if not in F_4 */
static u8 F4el[4];
static u8 coord[256][4];   /* F_4 coordinates (codes) of an element w.r.t. basis 1, g, g^2, g^3 */
static u8 MUL4[4][4] = {{0,0,0,0},{0,1,2,3},{0,2,3,1},{0,3,1,2}}, INV4[4] = {0,1,3,2};
static int rank4(u8 v[4]) { u8 a[4][4]; for (int i = 0; i < 4; i++) memcpy(a[i], coord[v[i]], 4); int r = 0;
    for (int c = 0; c < 4 && r < 4; c++) { int p = -1; for (int i = r; i < 4; i++) if (a[i][c]) { p = i; break; } if (p < 0) continue;
        u8 t[4]; memcpy(t, a[p], 4); memcpy(a[p], a[r], 4); memcpy(a[r], t, 4); u8 iv = INV4[a[r][c]]; for (int j = 0; j < 4; j++) a[r][j] = MUL4[iv][a[r][j]];
        for (int i = 0; i < 4; i++) if (i != r && a[i][c]) { u8 f = a[i][c]; for (int j = 0; j < 4; j++) a[i][j] ^= MUL4[f][a[r][j]]; } r++; }
    return r; }
int main(int argc, char **argv) {
    int x = 1; for (int i = 0; i < 255; i++) { EXP[i] = x; LOG[x] = i; x <<= 1; if (x & 256) x ^= 0x11D; } for (int i = 255; i < 512; i++) EXP[i] = EXP[i - 255];
    memset(F4of, 255, 256); F4el[0] = 0; F4el[1] = 1; F4el[2] = EXP[85]; F4el[3] = EXP[170]; for (int c = 0; c < 4; c++) F4of[F4el[c]] = c;
    for (int c0 = 0; c0 < 4; c0++) for (int c1 = 0; c1 < 4; c1++) for (int c2 = 0; c2 < 4; c2++) for (int c3 = 0; c3 < 4; c3++) {
        u8 v = gmul(F4el[c0], 1) ^ gmul(F4el[c1], EXP[1]) ^ gmul(F4el[c2], EXP[2]) ^ gmul(F4el[c3], EXP[3]);
        coord[v][0] = c0; coord[v][1] = c1; coord[v][2] = c2; coord[v][3] = c3; }
    int bestall = 1 << 30, bestmixed = 1 << 30; long nzero = 0, nzeromixed = 0;
    for (int al = 1; al < 256; al++) for (int be = 1; be < 256; be++) {
        u8 A[4] = { (u8)al, ginv(al), (u8)be, ginv(be) };   /* labels a, A, b, B as multipliers */
        for (int ga = 1; ga < 256; ga++) {
            u8 b[4] = { 1, ginv(al), (u8)ga, gmul(ginv(be), ga) };
            int sing = 0;
            for (int t1 = 0; t1 < 4 && sing < 3; t1++) for (int t2 = 0; t2 < 4; t2++) { if (t2 == (t1 ^ 1)) continue;
              for (int t3 = 0; t3 < 4; t3++) { if (t3 == (t2 ^ 1)) continue; for (int t4 = 0; t4 < 4; t4++) { if (t4 == (t3 ^ 1)) continue;
                u8 v[4] = { gmul(gmul(gmul(A[t4], A[t3]), A[t2]), b[t1]), gmul(gmul(A[t4], A[t3]), b[t2]), gmul(A[t4], b[t3]), b[t4] };
                if (rank4(v) < 4) sing++; } } }
            if (sing >= 3) continue;
            int d2all = 0, d2mix = 0;
            for (int t1 = 0; t1 < 4; t1++) for (int t2 = 0; t2 < 4; t2++) { if (t2 == (t1 ^ 1)) continue;
                u8 p1 = gmul(A[t2], b[t1]), p2 = b[t2];
                /* classes of vectors mod P: canonical representative = min over the coset's projective class */
                int seen[8], ns = 0;
                for (int r = 0; r < 4; r++) for (int kk = 0; kk < 3; kk++) {
                    u8 v = kk == 0 ? gmul(gmul(A[t2], A[t1]), b[r]) : kk == 1 ? gmul(A[t2], b[r]) : b[r];
                    /* hyperplane id: the set span{p1,p2,v}; use its minimal nonzero element outside P as id */
                    int inP = 0; for (int a1 = 0; a1 < 4 && !inP; a1++) for (int a2 = 0; a2 < 4; a2++) if ((gmul(F4el[a1], p1) ^ gmul(F4el[a2], p2)) == v) { inP = 1; break; }
                    if (inP) continue;
                    int id = 256; for (int c = 1; c < 4; c++) for (int a1 = 0; a1 < 4; a1++) for (int a2 = 0; a2 < 4; a2++) { int w = gmul(F4el[c], v) ^ gmul(F4el[a1], p1) ^ gmul(F4el[a2], p2); if (w < id) id = w; }
                    int dup = 0; for (int i = 0; i < ns; i++) if (seen[i] == id) dup = 1; if (!dup && ns < 8) seen[ns++] = id; }
                int def = ns < 5 ? 5 - ns : 0; d2all += def; if ((t1 >> 1) != (t2 >> 1)) d2mix += def; }
            int call = sing + d2all, cmix = sing + d2mix;
            if (call == 0) nzero++; if (cmix == 0) nzeromixed++;
            if (call < bestall || (call == 0 && nzero <= 3) || (cmix == 0 && nzeromixed <= 3)) {
                if (call < bestall) bestall = call;
                printf("alpha=%d beta=%d gamma=%d singular=%d d2all=%d d2mixed=%d\n", al, be, ga, sing, d2all, d2mix); fflush(stdout); }
        } }
    printf("done: best all-pattern cost %d, #charts with cost 0 (all) %ld, (mixed) %ld\n", bestall, nzero, nzeromixed);
    return 0; }
