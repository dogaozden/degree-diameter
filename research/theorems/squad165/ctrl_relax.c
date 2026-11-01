/* Relaxed Haar controllers H(G,S), |S| = 4 (for pencil-complete universal charts, chart2.py):
   (a) every g = s_a^-1 s_b s_c^-1 s_d (any a,b,c,d: bipartite diameter <= 5 on the A side),
   (b) every g = s_a s_b^-1 s_c s_d^-1 (B side),
   (c) a 4-cycle: s_i4^-1 s_i3 s_i2^-1 s_i1 = e for some i1!=i2!=i3!=i4.
   Exhaustive over S = {e,x,y,z}.  usage: ctrl_relax TABLE [maxprint] */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int m, *T, *Inv, e;
static inline int mul(int a, int b) { return T[a * m + b]; }
int main(int argc, char **argv) {
    FILE *f = fopen(argv[1], "r"); int maxprint = argc > 2 ? atoi(argv[2]) : 3;
    if (fscanf(f, "%d", &m) != 1) return 2;
    T = malloc(sizeof(int) * m * m); Inv = malloc(sizeof(int) * m);
    for (int i = 0; i < m * m; i++) if (fscanf(f, "%d", &T[i]) != 1) return 3;
    for (int i = 0; i < m; i++) { int ok = 1; for (int j = 0; j < m; j++) if (T[i * m + j] != j) { ok = 0; break; } if (ok) e = i; }
    for (int i = 0; i < m; i++) for (int j = 0; j < m; j++) if (T[i * m + j] == e) Inv[i] = j;
    char *cA = malloc(m), *cB = malloc(m);
    int best = 1 << 30, nsol = 0, bestS[4] = {0}; long tried = 0, nocycle = 0;
    int others[4096], no = 0; for (int i = 0; i < m; i++) if (i != e) others[no++] = i;
    for (int x = 0; x < no; x++) for (int y = x + 1; y < no; y++) for (int z = y + 1; z < no; z++) {
        int S[4] = { e, others[x], others[y], others[z] }, Si[4];
        for (int k = 0; k < 4; k++) Si[k] = Inv[S[k]];
        int dA[4][4], dB[4][4];
        for (int j = 0; j < 4; j++) for (int i = 0; i < 4; i++) { dA[j][i] = mul(Si[j], S[i]); dB[j][i] = mul(S[j], Si[i]); }
        /* 4-cycle */
        int cyc = 0;
        for (int i1 = 0; i1 < 4 && !cyc; i1++) for (int i2 = 0; i2 < 4 && !cyc; i2++) if (i2 != i1)
            for (int i3 = 0; i3 < 4 && !cyc; i3++) if (i3 != i2) for (int i4 = 0; i4 < 4; i4++) if (i4 != i3)
                if (mul(dA[i4][i3], dA[i2][i1]) == e) { cyc = 1; break; }
        tried++;
        if (!cyc) { nocycle++; continue; }
        memset(cA, 0, m); memset(cB, 0, m);
        for (int a = 0; a < 4; a++) for (int b = 0; b < 4; b++) for (int c = 0; c < 4; c++) for (int d = 0; d < 4; d++) {
            cA[mul(dA[a][b], dA[c][d])] = 1;      /* s_a^-1 s_b s_c^-1 s_d */
            cB[mul(dB[a][b], dB[c][d])] = 1;      /* s_a s_b^-1 s_c s_d^-1 */
        }
        int c = 0; for (int i = 0; i < m; i++) c += !cA[i] + !cB[i];
        if (c < best) { best = c; for (int k = 0; k < 4; k++) bestS[k] = S[k]; }
        if (c == 0) { nsol++; if (nsol <= maxprint) printf("SOL S = %d %d %d %d\n", S[0], S[1], S[2], S[3]); }
    }
    printf("m=%d tried=%ld with4cycle=%ld best_cost=%d solutions=%d bestS=%d %d %d %d\n", m, tried, tried - nocycle, best, nsol,
           bestS[0], bestS[1], bestS[2], bestS[3]);
    return 0;
}
