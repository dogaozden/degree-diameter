/* c7: base X(M0,M1,M2) with level-dependent bijections M_i (points of level i -> lines of level i+1).
   usage: lvl HEXBIN seed mode out.txt   mode 0: independent M_0,M_1,M_2; mode 1: M_0=M_1=M_2 (the table base)
   writes "n" then the edge list (hexagon edges at every level + cross edges (p,i)~(M_i(p),i+1)). */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
static int q, N, Q1; static int32_t *LP, *PL; static int *M[3], *Minv[3];
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline int rndi(int n) { return (int)(rnd() % (uint64_t)n); }
static inline int VP(int p, int i) { return i * 2 * N + p; }
static inline int VL(int l, int i) { return i * 2 * N + N + l; }
static int nbrs(int v, int *out) {
    int c = 0, i = v / (2 * N), r = v % (2 * N);
    if (r < N) { int p = r;
        for (int k = 0; k < Q1; k++) out[c++] = VL(PL[p * Q1 + k], i);
        out[c++] = VL(M[i][p], (i + 1) % 3);
    } else { int l = r - N;
        for (int k = 0; k < Q1; k++) out[c++] = VP(LP[l * Q1 + k], i);
        int ip = (i + 2) % 3; out[c++] = VP(Minv[ip][l], ip);
    }
    return c;
}
int main(int argc, char **argv) {
    FILE *f = fopen(argv[1], "rb"); int32_t hdr[3]; if (fread(hdr, 4, 3, f) != 3) return 1;
    q = hdr[0]; N = hdr[1]; Q1 = q + 1;
    LP = malloc(4 * (size_t)N * Q1); if (fread(LP, 4, (size_t)N * Q1, f) != (size_t)N * Q1) return 1; fclose(f);
    PL = malloc(4 * (size_t)N * Q1); int *cnt = calloc(N, sizeof(int));
    for (int l = 0; l < N; l++) for (int k = 0; k < Q1; k++) { int p = LP[l * Q1 + k]; PL[p * Q1 + cnt[p]++] = l; }
    rs ^= (uint64_t)atoll(argv[2]) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 20; i++) rnd();
    int mode = atoi(argv[3]);
    for (int i = 0; i < 3; i++) { M[i] = malloc(sizeof(int) * N); Minv[i] = malloc(sizeof(int) * N);
        for (int p = 0; p < N; p++) M[i][p] = p;
        for (int p = N - 1; p > 0; p--) { int r = rndi(p + 1); int t = M[i][p]; M[i][p] = M[i][r]; M[i][r] = t; }
        for (int p = 0; p < N; p++) Minv[i][M[i][p]] = p; }
    if (mode == 1) for (int i = 1; i < 3; i++) { memcpy(M[i], M[0], sizeof(int) * N); memcpy(Minv[i], Minv[0], sizeof(int) * N); }
    int NV = 6 * N; FILE *o = fopen(argv[4], "w"); fprintf(o, "%d\n", NV);
    int nb[64]; long m = 0;
    for (int v = 0; v < NV; v++) { int c = nbrs(v, nb); for (int k = 0; k < c; k++) if (nb[k] > v) { fprintf(o, "%d %d\n", v, nb[k]); m++; } }
    fclose(o); fprintf(stderr, "wrote n=%d edges=%ld (mode %d)\n", NV, m, mode);
    return 0;
}
