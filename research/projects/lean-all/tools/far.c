// far: count same-side pairs at distance > 6 in a bipartite graph (B side nB, A side nA), edges "b a".
// usage: far EDGES nB nA [listfile]
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
static int nB, nA, ne; static int *eb, *ea;
static int *degB, *degA, **nbB, **nbA;
static void layer(int nX, int **nbX, int *degX, uint64_t *prev, uint64_t *out, int W) {
  for (int x = 0; x < nX; x++) { uint64_t *o = out + (size_t)x * W; memset(o, 0, 8 * W);
    for (int t = 0; t < degX[x]; t++) { uint64_t *p = prev + (size_t)nbX[x][t] * W; for (int w = 0; w < W; w++) o[w] |= p[w]; } }
}
static long side(int nS, int nO, int **nbS, int *degS, int **nbO, int *degO, FILE *lf, int tag) {
  int W = (nS + 63) / 64; uint64_t *cur = calloc((size_t)nS * W, 8), *oth = calloc((size_t)nO * W, 8), *nx = calloc((size_t)nS * W, 8);
  for (int i = 0; i < nS; i++) cur[(size_t)i * W + i / 64] |= 1ULL << (i % 64);
  for (int r = 0; r < 3; r++) { layer(nO, nbO, degO, cur, oth, W); layer(nS, nbS, degS, oth, nx, W);
    for (size_t k = 0; k < (size_t)nS * W; k++) cur[k] |= nx[k]; }
  long miss = 0;
  for (int i = 0; i < nS; i++) for (int j = i + 1; j < nS; j++) if (!((cur[(size_t)i * W + j / 64] >> (j % 64)) & 1)) { miss++; if (lf) fprintf(lf, "%d %d %d\n", tag, i, j); }
  free(cur); free(oth); free(nx); return miss;
}
int main(int argc, char **argv) {
  FILE *f = fopen(argv[1], "r"); nB = atoi(argv[2]); nA = atoi(argv[3]); FILE *lf = argc > 4 ? fopen(argv[4], "w") : NULL;
  int cap = 1 << 20; eb = malloc(4 * cap); ea = malloc(4 * cap); ne = 0;
  while (fscanf(f, "%d %d", &eb[ne], &ea[ne]) == 2) ne++;
  degB = calloc(nB, 4); degA = calloc(nA, 4);
  for (int e = 0; e < ne; e++) { degB[eb[e]]++; degA[ea[e]]++; }
  nbB = malloc(8 * nB); nbA = malloc(8 * nA);
  for (int i = 0; i < nB; i++) nbB[i] = malloc(4 * degB[i]); for (int i = 0; i < nA; i++) nbA[i] = malloc(4 * degA[i]);
  int *cB = calloc(nB, 4), *cA = calloc(nA, 4);
  for (int e = 0; e < ne; e++) { nbB[eb[e]][cB[eb[e]]++] = ea[e]; nbA[ea[e]][cA[ea[e]]++] = eb[e]; }
  int mxB = 0, mxA = 0; for (int i = 0; i < nB; i++) if (degB[i] > mxB) mxB = degB[i]; for (int i = 0; i < nA; i++) if (degA[i] > mxA) mxA = degA[i];
  long mb = side(nB, nA, nbB, degB, nbA, degA, lf, 0), ma = side(nA, nB, nbA, degA, nbB, degB, lf, 1);
  printf("edges %d maxdegB %d maxdegA %d farB %ld farA %ld\n", ne, mxB, mxA, mb, ma);
  return 0;
}
