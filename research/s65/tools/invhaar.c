/* Inverse-closed Haar graphs at (6,5), exhaustively (job fresh-6-5).
 *
 * If S = S^-1, then S^-1 S = S S^-1 = S^2 and H(G,S) (the bipartite double of Cay(G,S)) has diameter <= 5
 * iff S^4 = G: one covering condition instead of the two of a general Haar graph. S is a union of inverse
 * classes {g, g^-1} (size 2) and involutions (size 1) with |S| = 6; every such S is tried (no symmetry
 * reduction needed: about (N/2)^3/6 sets). cost = N - |S^4|.
 *
 * input: N, then the N x N multiplication table (0-based; element 0 = identity), as written by tables.g.
 * usage: invhaar FILE [MAXINV]   (MAXINV: skip candidates using more than this many involutions; default 6)
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

#define W 8
static int N, *M, *INV, ncl, *clsz, (*cl)[2];
static long cand, hist[64], nvalid;
static int best = 1 << 30, bestS[6], S[6], ns, maxinv = 6, ninv;
static char *label;

static void eval(void) {
    cand++;
    int S2[36], n2 = 0;
    uint64_t c2[W] = {0};
    for (int i = 0; i < 6; i++) for (int j = 0; j < 6; j++) {
        int x = M[S[i] * N + S[j]];
        if (!(c2[x >> 6] >> (x & 63) & 1)) { c2[x >> 6] |= 1ULL << (x & 63); S2[n2++] = x; }
    }
    uint64_t c4[W] = {0};
    for (int i = 0; i < n2; i++) { const int *row = M + S2[i] * N; for (int j = 0; j < n2; j++) { int x = row[S2[j]]; c4[x >> 6] |= 1ULL << (x & 63); } }
    int t = 0; for (int w = 0; w < W; w++) t += __builtin_popcountll(c4[w]);
    int c = N - t;
    hist[c < 63 ? c : 63]++;
    if (c < best) { best = c; memcpy(bestS, S, sizeof S); }
    if (c == 0 && ++nvalid <= 5) { printf("VALID %s S = %d %d %d %d %d %d\n", label, S[0], S[1], S[2], S[3], S[4], S[5]); fflush(stdout); }
}

static void rec(int start, int left) {
    if (left == 0) { eval(); return; }
    for (int k = start; k < ncl; k++) {
        if (clsz[k] > left) continue;
        if (clsz[k] == 1 && ninv >= maxinv) continue;
        for (int i = 0; i < clsz[k]; i++) S[ns++] = cl[k][i];
        ninv += clsz[k] == 1;
        rec(k + 1, left - clsz[k]);
        ninv -= clsz[k] == 1;
        ns -= clsz[k];
    }
}

int main(int argc, char **argv) {
    FILE *f = fopen(argv[1], "r"); if (!f) return 2;
    label = argv[1];
    if (argc > 2) maxinv = atoi(argv[2]);
    if (fscanf(f, "%d", &N) != 1 || N > 64 * W) return 2;
    M = malloc(sizeof(int) * N * N); INV = malloc(sizeof(int) * N);
    for (int i = 0; i < N * N; i++) if (fscanf(f, "%d", &M[i]) != 1) return 2;
    fclose(f);
    for (int a = 0; a < N; a++) for (int b = 0; b < N; b++) if (M[a * N + b] == 0) INV[a] = b;
    cl = malloc(sizeof(*cl) * N); clsz = malloc(sizeof(int) * N);
    int ni = 0;
    for (int g = 1; g < N; g++) {
        if (INV[g] == g) { cl[ncl][0] = g; clsz[ncl++] = 1; ni++; }
        else if (g < INV[g]) { cl[ncl][0] = g; cl[ncl][1] = INV[g]; clsz[ncl++] = 2; }
    }
    rec(0, 6);
    printf("DONE %s N=%d involutions=%d candidates=%ld valid=%ld min=%d bestS=%d,%d,%d,%d,%d,%d hist", label, N, ni, cand, nvalid, best,
           bestS[0], bestS[1], bestS[2], bestS[3], bestS[4], bestS[5]);
    int shown = 0;
    for (int c = 0; c < 64 && shown < 6; c++) if (hist[c]) { printf(" %d:%ld", c, hist[c]); shown++; }
    printf("\n");
    return 0;
}
