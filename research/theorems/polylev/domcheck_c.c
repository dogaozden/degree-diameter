/* domcheck_c.c: independent checker for ball-lift colourings at large q (the C counterpart of domcheck.py).
   polylev job (Opus), 2026-10-28. Written separately from the search programs; it only reads the hexagon and the
   colour files.

   For every point p it lists the 2-ball (p and the points on the q+1 lines through p) and records which colours occur;
   the same for every line l (l and the lines through the q+1 points of l). A colour is good on a side when every
   2-ball of that side contains it. Prints the number of good colours per side, the class sizes and the balance
   condition sum_i max(|A_i|, |B_i|) <= N, and k = number of colours good on both sides (if balanced).
   Usage: domcheck_c HEXBIN POINTCOL LINECOL */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

int main(int argc, char **argv) {
    if (argc < 4) { fprintf(stderr, "usage: domcheck_c HEXBIN POINTCOL LINECOL\n"); return 1; }
    FILE *f = fopen(argv[1], "rb"); int32_t h[3]; if (!f || fread(h, 4, 3, f) != 3) return 1;
    int q = h[0], N = h[1], Q1 = q + 1;
    int *LP = malloc(sizeof(int) * (size_t)N * Q1); if (fread(LP, 4, (size_t)N * Q1, f) != (size_t)N * Q1) return 1; fclose(f);
    int *PL = malloc(sizeof(int) * (size_t)N * Q1), *c = calloc(N, sizeof(int));
    for (int l = 0; l < N; l++) for (int a = 0; a < Q1; a++) { int p = LP[l * Q1 + a]; PL[p * Q1 + c[p]++] = l; }
    for (int p = 0; p < N; p++) if (c[p] != Q1) { fprintf(stderr, "point %d on %d lines\n", p, c[p]); return 1; }
    int *col[2];
    for (int s = 0; s < 2; s++) { col[s] = malloc(sizeof(int) * N); f = fopen(argv[2 + s], "rb");
        if (!f || fread(col[s], 4, N, f) != (size_t)N) { fprintf(stderr, "bad colour file %s\n", argv[2 + s]); return 1; } fclose(f); }
    int K = 0; for (int s = 0; s < 2; s++) for (int x = 0; x < N; x++) if (col[s][x] + 1 > K) K = col[s][x] + 1;
    long *size[2]; int *good[2];
    for (int s = 0; s < 2; s++) {      /* s = 0: points, s = 1: lines */
        size[s] = calloc(K, sizeof(long)); good[s] = malloc(sizeof(int) * K);
        for (int i = 0; i < K; i++) good[s][i] = 1;
        for (int x = 0; x < N; x++) if (col[s][x] >= 0) size[s][col[s][x]]++;
        int *seen = calloc(K, sizeof(int)), stamp = 0;
        for (int x = 0; x < N; x++) {
            stamp++;
            if (col[s][x] >= 0) seen[col[s][x]] = stamp;
            for (int a = 0; a < Q1; a++) {
                int m = s == 0 ? PL[x * Q1 + a] : LP[x * Q1 + a];
                for (int b = 0; b < Q1; b++) { int y = s == 0 ? LP[m * Q1 + b] : PL[m * Q1 + b]; if (col[s][y] >= 0) seen[col[s][y]] = stamp; }
            }
            for (int i = 0; i < K; i++) if (seen[i] != stamp) good[s][i] = 0;
        }
        free(seen);
    }
    int gp = 0, gl = 0, both = 0; long bal = 0;
    for (int i = 0; i < K; i++) { gp += good[0][i]; gl += good[1][i];
        if (good[0][i] && good[1][i]) { both++; bal += size[0][i] > size[1][i] ? size[0][i] : size[1][i]; } }
    long mn = N, mx = 0; for (int i = 0; i < K; i++) for (int s = 0; s < 2; s++) { if (size[s][i] < mn) mn = size[s][i]; if (size[s][i] > mx) mx = size[s][i]; }
    printf("q=%d N=%d colours=%d: good point colours %d, good line colours %d, good on both %d; class sizes %ld..%ld; "
           "sum max = %ld (N = %d) -> %s; k = %d\n", q, N, K, gp, gl, both, mn, mx, bal, N, bal <= N ? "balanced" : "NOT balanced",
           bal <= N ? both : 0);
    return 0;
}
