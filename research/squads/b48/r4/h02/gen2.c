/* gen2 GROUP.bin: voltage lines "0 a 0 0 b c" for the 2+2 cubic base b22_cubic (edges 0,2,3 at identity), with a
   restricted to one representative per conjugacy class (inner automorphisms h: a,b,c -> h a h^-1, ... keep the fixed
   tree at identity and the lift isomorphic). Every orbit of triples under conjugation has a member with a = class rep. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
int main(int argc, char **argv) {
    FILE *f = fopen(argv[1], "rb"); int32_t n32; if (!f || fread(&n32, 4, 1, f) != 1) return 2;
    int N = n32; uint16_t *MT = malloc((size_t)N * N * 2); if (fread(MT, 2, (size_t)N * N, f) != (size_t)N * N) return 2; fclose(f);
    int *INV = malloc(N * sizeof(int));
    for (int g = 0; g < N; g++) { INV[g] = -1; for (int h = 0; h < N; h++) if (MT[(size_t)g * N + h] == 0) { INV[g] = h; break; } }
    char *seen = calloc(N, 1); int nrep = 0; int *rep = malloc(N * sizeof(int));
    for (int g = 0; g < N; g++) if (!seen[g]) {
        rep[nrep++] = g;
        for (int h = 0; h < N; h++) { int c = MT[(size_t)MT[(size_t)h * N + g] * N + INV[h]]; seen[c] = 1; }
    }
    fprintf(stderr, "N=%d classes=%d lines=%lld\n", N, nrep, (long long)nrep * N * N);
    char buf[64];
    for (int r = 0; r < nrep; r++) for (int b = 0; b < N; b++) for (int c = 0; c < N; c++) {
        int len = sprintf(buf, "0 %d 0 0 %d %d\n", rep[r], b, c); fwrite(buf, 1, len, stdout); }
    return 0;
}
