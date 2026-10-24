/* gh_build.c: incidence structure of the split Cayley hexagon H(q), q prime.
   Points: points of the quadric X0X4 + X1X5 + X2X6 = X3^2 in PG(6,q) (Tits' coordinates, as in
   research/lifts/polygons.py). Lines: quadric lines whose Grassmann coordinates satisfy
   p12=p34, p54=p32, p20=p35, p65=p30, p01=p36, p46=p31.
   For a point x the points collinear with x form a plane pi_x = kernel of 7 linear forms in y (the polar
   condition and the six Grassmann conditions), so the q+1 lines through x are the 2-spaces of pi_x through x.
   Output (text): "P q" then P lines (one per hexagon line) with its q+1 point indices.
   Self-checks: |pi_x| = q^2+q+1 for every x, every kernel vector is singular, every line has q+1 points,
   exactly P lines, every point on q+1 lines.
   Usage: gh_build q [COORDFILE] > gh_q.txt   (COORDFILE: one line per point, its normalized vector)          (compile: gcc -O2 -o gh_build gh_build.c) */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

static int q;
static int md(long long a) { a %= q; return (int)(a < 0 ? a + q : a); }
static int inv(int a) { int r = 1, e = q - 2; long long b = a; while (e) { if (e & 1) r = (int)(r * b % q); b = b * b % q; e >>= 1; } return r; }

static int32_t *idx; /* encoding -> point index */
static long long enc(const int *v) { long long e = 0; for (int i = 0; i < 7; i++) e = e * q + v[i]; return e; }
static void normalize(int *v) {
    for (int i = 0; i < 7; i++) if (v[i]) { int s = inv(v[i]); for (int k = 0; k < 7; k++) v[k] = (int)((long long)v[k] * s % q); return; }
}
static int singular(const int *v) { return md((long long)v[0] * v[4] + (long long)v[1] * v[5] + (long long)v[2] * v[6] - (long long)v[3] * v[3]) == 0; }

/* kernel of a 7x7 matrix mod q; returns dimension, basis rows in K */
static int kernel(int A[7][7], int K[7][7]) {
    int M[7][7]; memcpy(M, A, sizeof(M));
    int piv[7], r = 0; int isp[7] = {0};
    for (int c = 0; c < 7 && r < 7; c++) {
        int p = -1; for (int i = r; i < 7; i++) if (M[i][c]) { p = i; break; }
        if (p < 0) continue;
        for (int k = 0; k < 7; k++) { int t = M[r][k]; M[r][k] = M[p][k]; M[p][k] = t; }
        int s = inv(M[r][c]); for (int k = 0; k < 7; k++) M[r][k] = (int)((long long)M[r][k] * s % q);
        for (int i = 0; i < 7; i++) if (i != r && M[i][c]) { int f = M[i][c]; for (int k = 0; k < 7; k++) M[i][k] = md(M[i][k] - (long long)f * M[r][k]); }
        piv[r] = c; isp[c] = 1; r++;
    }
    int d = 0;
    for (int fcol = 0; fcol < 7; fcol++) if (!isp[fcol]) {
        int v[7] = {0}; v[fcol] = 1;
        for (int i = 0; i < r; i++) v[piv[i]] = md(-(long long)M[i][fcol]);
        memcpy(K[d++], v, sizeof(v));
    }
    return d;
}

int main(int argc, char **argv) {
    if (argc < 2) { fprintf(stderr, "usage: gh_build q\n"); return 2; }
    q = atoi(argv[1]);
    long long tot = 1; for (int i = 0; i < 7; i++) tot *= q;
    idx = malloc(sizeof(int32_t) * tot); for (long long i = 0; i < tot; i++) idx[i] = -1;
    long long Pexp = 0; { long long t = 1; for (int i = 0; i < 6; i++) { Pexp += t; t *= q; } }
    int *pts = malloc(sizeof(int) * 7 * Pexp); int P = 0;
    int v[7];
    for (long long e = 0; e < tot; e++) {
        long long t = e; for (int i = 6; i >= 0; i--) { v[i] = (int)(t % q); t /= q; }
        int f = -1; for (int i = 0; i < 7; i++) if (v[i]) { f = i; break; }
        if (f < 0 || v[f] != 1 || !singular(v)) continue;
        if (P >= Pexp) { fprintf(stderr, "too many points\n"); return 1; }
        memcpy(pts + 7 * P, v, sizeof(v)); idx[e] = P; P++;
    }
    if (P != Pexp) { fprintf(stderr, "point count %d != %lld\n", P, Pexp); return 1; }
    /* lines */
    long long HS = 1; while (HS < 4LL * P) HS <<= 1;
    long long *hkey = malloc(sizeof(long long) * HS); int *hval = malloc(sizeof(int) * HS);
    for (long long i = 0; i < HS; i++) hkey[i] = -1;
    int *lines = malloc(sizeof(int) * (q + 1) * (long long)P); int L = 0;
    int *deg = calloc(P, sizeof(int));
    for (int i = 0; i < P; i++) {
        int *x = pts + 7 * i; int A[7][7] = {{0}};
        /* polar */
        A[0][0] = x[4]; A[0][1] = x[5]; A[0][2] = x[6]; A[0][3] = md(-2LL * x[3]); A[0][4] = x[0]; A[0][5] = x[1]; A[0][6] = x[2];
        /* p12 - p34 */ A[1][1] = md(-x[2]); A[1][2] = x[1]; A[1][3] = x[4]; A[1][4] = md(-x[3]);
        /* p54 - p32 */ A[2][4] = x[5]; A[2][5] = md(-x[4]); A[2][2] = md(-x[3]); A[2][3] = x[2];
        /* p20 - p35 */ A[3][0] = x[2]; A[3][2] = md(-x[0]); A[3][5] = md(-x[3]); A[3][3] = x[5];
        /* p65 - p30 */ A[4][5] = x[6]; A[4][6] = md(-x[5]); A[4][0] = md(-x[3]); A[4][3] = x[0];
        /* p01 - p36 */ A[5][1] = x[0]; A[5][0] = md(-x[1]); A[5][6] = md(-x[3]); A[5][3] = x[6];
        /* p46 - p31 */ A[6][6] = x[4]; A[6][4] = md(-x[6]); A[6][1] = md(-x[3]); A[6][3] = x[1];
        int K[7][7]; int d = kernel(A, K);
        if (d != 3) { fprintf(stderr, "kernel dim %d at point %d\n", d, i); return 1; }
        /* basis {x, u, w}: pick two kernel vectors independent mod x */
        int B[3][7]; memcpy(B[0], x, sizeof(int) * 7);
        int nb = 1;
        for (int k = 0; k < 3 && nb < 3; k++) {
            /* test independence of B[0..nb-1], K[k] via rank */
            int T[3][7]; for (int r = 0; r < nb; r++) memcpy(T[r], B[r], sizeof(int) * 7); memcpy(T[nb], K[k], sizeof(int) * 7);
            int rr = 0; int rows = nb + 1;
            for (int c = 0; c < 7 && rr < rows; c++) {
                int p = -1; for (int a = rr; a < rows; a++) if (T[a][c]) { p = a; break; }
                if (p < 0) continue;
                for (int z = 0; z < 7; z++) { int t = T[rr][z]; T[rr][z] = T[p][z]; T[p][z] = t; }
                int s = inv(T[rr][c]); for (int z = 0; z < 7; z++) T[rr][z] = (int)((long long)T[rr][z] * s % q);
                for (int a = 0; a < rows; a++) if (a != rr && T[a][c]) { int f = T[a][c]; for (int z = 0; z < 7; z++) T[a][z] = md(T[a][z] - (long long)f * T[rr][z]); }
                rr++;
            }
            if (rr == rows) { memcpy(B[nb], K[k], sizeof(int) * 7); nb++; }
        }
        if (nb != 3) { fprintf(stderr, "basis fail at %d\n", i); return 1; }
        /* all points of pi_x must be singular */
        for (int a = 0; a < q; a++) for (int b = 0; b < q; b++) {
            int y[7]; for (int k = 0; k < 7; k++) y[k] = md((long long)a * B[1][k] + (long long)b * B[2][k] + B[0][k]);
            if (!singular(y)) { fprintf(stderr, "pi_x not totally singular at %d\n", i); return 1; }
        }
        for (int t = 0; t <= q; t++) {
            int y[7];
            for (int k = 0; k < 7; k++) y[k] = (t < q) ? md(B[1][k] + (long long)t * B[2][k]) : B[2][k];
            int mem[64]; int nm = 0; mem[nm++] = i;
            for (int c = 0; c < q; c++) {
                int z[7]; for (int k = 0; k < 7; k++) z[k] = md(y[k] + (long long)c * x[k]);
                normalize(z); int id = idx[enc(z)];
                if (id < 0) { fprintf(stderr, "line point not on quadric\n"); return 1; }
                mem[nm++] = id;
            }
            /* sort */
            for (int a = 1; a < nm; a++) { int w = mem[a], b = a - 1; while (b >= 0 && mem[b] > w) { mem[b + 1] = mem[b]; b--; } mem[b + 1] = w; }
            for (int a = 1; a < nm; a++) if (mem[a] == mem[a - 1]) { fprintf(stderr, "repeated point on line\n"); return 1; }
            long long key = (long long)mem[0] * P + mem[1];
            long long h = (key * 0x9E3779B97F4A7C15ULL) & (HS - 1);
            while (hkey[h] != -1 && hkey[h] != key) h = (h + 1) & (HS - 1);
            if (hkey[h] == -1) {
                hkey[h] = key; hval[h] = L;
                if (L >= P) { fprintf(stderr, "too many lines\n"); return 1; }
                memcpy(lines + (long long)(q + 1) * L, mem, sizeof(int) * (q + 1));
                for (int a = 0; a < nm; a++) deg[mem[a]]++;
                L++;
            }
        }
    }
    if (L != P) { fprintf(stderr, "line count %d != %d\n", L, P); return 1; }
    for (int i = 0; i < P; i++) if (deg[i] != q + 1) { fprintf(stderr, "point %d on %d lines\n", i, deg[i]); return 1; }
    if (argc > 2) { /* coordinates file: point index -> normalized vector (Tits coordinates x0..x6) */
        FILE *cf = fopen(argv[2], "w");
        for (int i = 0; i < P; i++) { for (int k = 0; k < 7; k++) fprintf(cf, k ? " %d" : "%d", pts[7 * i + k]); fprintf(cf, "\n"); }
        fclose(cf);
    }
    printf("%d %d\n", P, q);
    for (int l = 0; l < L; l++) {
        for (int a = 0; a <= q; a++) printf(a ? " %d" : "%d", lines[(long long)(q + 1) * l + a]);
        printf("\n");
    }
    fprintf(stderr, "H(%d): %d points, %d lines, all checks passed\n", q, P, L);
    return 0;
}
