/* gtab.c: rebuild a full multiplication table (hx.c 'tab' format) from generator permutations.

   Input (from fscreen.py's GAP export): first line "N e t", then t lines of N 0-based indices; line j lists x*g_j for
   x = 0..N-1 (right multiplication by the j-th generator).
   Every y is a word e*g_{w1}*...*g_{wk}; with parent(y) = y*g_{w_k}^-1 from a BFS of the right Cayley graph,
   x*y = (x*parent(y))*g_{w_k}, so each table column is one permutation lookup of an earlier column.
   Output: "N e" then N rows; row x lists x*y for y = 0..N-1.
   Usage: gtab GENS OUT
*/
#include <stdio.h>
#include <stdlib.h>

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: gtab GENS OUT\n"); return 2; }
    FILE *f = fopen(argv[1], "r"); if (!f) { perror("gens"); return 2; }
    int N, e, t;
    if (fscanf(f, "%d %d %d", &N, &e, &t) != 3) return 2;
    int *R = malloc(sizeof(int) * (size_t)N * t);
    for (int j = 0; j < t; j++) for (int x = 0; x < N; x++) if (fscanf(f, "%d", &R[(size_t)j * N + x]) != 1) return 2;
    fclose(f);
    int *par = malloc(sizeof(int) * N), *gen = malloc(sizeof(int) * N), *ord = malloc(sizeof(int) * N);
    for (int y = 0; y < N; y++) par[y] = -1;
    int h = 0, tl = 0; ord[tl++] = e; par[e] = e; gen[e] = -1;
    while (h < tl) {
        int y = ord[h++];
        for (int j = 0; j < t; j++) { int z = R[(size_t)j * N + y]; if (par[z] < 0) { par[z] = y; gen[z] = j; ord[tl++] = z; } }
    }
    if (tl != N) { fprintf(stderr, "generators do not generate (%d of %d)\n", tl, N); return 3; }
    int *T = malloc(sizeof(int) * (size_t)N * N);       /* column-major: T[y*N + x] = x*y */
    for (int x = 0; x < N; x++) T[(size_t)e * N + x] = x;
    for (int k = 1; k < N; k++) {
        int y = ord[k], p = par[y]; const int *Rg = R + (size_t)gen[y] * N;
        int *cy = T + (size_t)y * N; const int *cp = T + (size_t)p * N;
        for (int x = 0; x < N; x++) cy[x] = Rg[cp[x]];
    }
    FILE *o = fopen(argv[2], "w"); if (!o) { perror("out"); return 2; }
    fprintf(o, "%d %d\n", N, e);
    for (int x = 0; x < N; x++) {
        for (int y = 0; y < N; y++) fprintf(o, y ? " %d" : "%d", T[(size_t)y * N + x]);
        fputc('\n', o);
    }
    fclose(o);
    return 0;
}
