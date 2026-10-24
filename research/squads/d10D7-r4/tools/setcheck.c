/* setcheck.c: score a set of points or lines of the hexagon H(q) (squad round 4, d10D7).
   Usage: setcheck HEXBIN FILE KIND REL
     KIND: points | lines;  REL: opposite (pairwise distance 6) | noncollinear (points: no two on a common line;
     lines: no two through a common point, i.e. pairwise distance >= 4)
   FILE: whitespace-separated ids (points 0..N-1, lines 0..N-1 as in research/d10D7/hex/hex_qQ.bin).
   Prints "VALID size S" or "INVALID ..." (first violating pair). */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
static int q, N, Q1, *LP, *PL;
static void bfs(int s, int isline, uint8_t *d) {   /* d[0..N) points, d[N..2N) lines */
    int *qq = malloc(sizeof(int) * 2 * N), h = 0, t = 0; memset(d, 255, 2 * N);
    int v0 = isline ? N + s : s; d[v0] = 0; qq[t++] = v0;
    while (h < t) { int v = qq[h++];
        if (v < N) { for (int k = 0; k < Q1; k++) { int w = N + PL[v * Q1 + k]; if (d[w] == 255) { d[w] = d[v] + 1; qq[t++] = w; } } }
        else { for (int k = 0; k < Q1; k++) { int w = LP[(v - N) * Q1 + k]; if (d[w] == 255) { d[w] = d[v] + 1; qq[t++] = w; } } } }
    free(qq);
}
int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage: setcheck HEXBIN FILE points|lines opposite|noncollinear\n"); return 2; }
    FILE *f = fopen(argv[1], "rb"); int32_t hdr[3]; if (!f || fread(hdr, 4, 3, f) != 3) return 2;
    q = hdr[0]; N = hdr[1]; Q1 = q + 1; LP = malloc(sizeof(int) * N * Q1); if (fread(LP, 4, (size_t)N * Q1, f) != (size_t)N * Q1) return 2; fclose(f);
    PL = malloc(sizeof(int) * N * Q1); int *c = calloc(N, sizeof(int));
    for (int l = 0; l < N; l++) for (int k = 0; k < Q1; k++) { int p = LP[l * Q1 + k]; PL[p * Q1 + c[p]++] = l; }
    int isline = !strcmp(argv[3], "lines"), opp = !strcmp(argv[4], "opposite");
    int *S = malloc(sizeof(int) * N), n = 0, x; f = fopen(argv[2], "r"); if (!f) { perror(argv[2]); return 2; }
    while (fscanf(f, "%d", &x) == 1) { if (x < 0 || x >= N) { printf("INVALID id %d out of range\n", x); return 1; } if (n < N) S[n++] = x; } fclose(f);
    char *in = calloc(N, 1); for (int i = 0; i < n; i++) { if (in[S[i]]) { printf("INVALID repeated id %d\n", S[i]); return 1; } in[S[i]] = 1; }
    if (opp) {
        uint8_t *d = malloc(2 * N);
        for (int i = 0; i < n; i++) { bfs(S[i], isline, d);
            for (int j = i + 1; j < n; j++) { int dd = d[isline ? N + S[j] : S[j]]; if (dd != 6) { printf("INVALID %d and %d at distance %d\n", S[i], S[j], dd); return 1; } } }
    } else {
        int *mark = calloc(N, sizeof(int));
        for (int i = 0; i < n; i++) for (int k = 0; k < Q1; k++) { int y = isline ? LP[S[i] * Q1 + k] : PL[S[i] * Q1 + k];
            if (mark[y]) { printf("INVALID %d and %d share %s %d\n", S[i], S[mark[y] - 1], isline ? "point" : "line", y); return 1; } mark[y] = i + 1; }
    }
    printf("VALID size %d (q=%d %s %s)\n", n, q, argv[3], argv[4]);
    return 0;
}
