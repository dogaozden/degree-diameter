/* Exhaustive search for Haar controllers H(G,S), |S| = 4, with exact-NB-4 coverage on both sides:
   every g in G is s_i4^-1 s_i3 s_i2^-1 s_i1 (A side) and s_i4 s_i3^-1 s_i2 s_i1^-1 (B side), i1!=i2!=i3!=i4.
   WLOG s_1 = e.  Input: multiplication table file (m, then m*m entries, row-major T[i*m+j] = i*j).
   usage: ctrl_exh TABLE [maxprint]   -> prints every S with cost 0, and the min cost found. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int m, *T, *Inv, e;
int W[108][4], nw = 0;
static inline int mul(int a, int b) { return T[a * m + b]; }
int main(int argc, char **argv) {
    FILE *f = fopen(argv[1], "r"); int maxprint = argc > 2 ? atoi(argv[2]) : 5;
    if (fscanf(f, "%d", &m) != 1) return 2;
    T = malloc(sizeof(int) * m * m); Inv = malloc(sizeof(int) * m);
    for (int i = 0; i < m * m; i++) if (fscanf(f, "%d", &T[i]) != 1) return 3;
    for (int i = 0; i < m; i++) { int ok = 1; for (int j = 0; j < m; j++) if (T[i * m + j] != j) { ok = 0; break; } if (ok) e = i; }
    for (int i = 0; i < m; i++) for (int j = 0; j < m; j++) if (T[i * m + j] == e) Inv[i] = j;
    for (int a = 0; a < 4; a++) for (int b = 0; b < 4; b++) for (int c = 0; c < 4; c++) for (int d = 0; d < 4; d++)
        if (a != b && b != c && c != d) { W[nw][0] = a; W[nw][1] = b; W[nw][2] = c; W[nw][3] = d; nw++; }
    char *cA = malloc(m), *cB = malloc(m);
    int best = 1 << 30, nsol = 0; long tried = 0;
    int others[4096], no = 0; for (int i = 0; i < m; i++) if (i != e) others[no++] = i;
    for (int x = 0; x < no; x++) for (int y = x + 1; y < no; y++) for (int z = y + 1; z < no; z++) {
        int S[4] = { e, others[x], others[y], others[z] }, Si[4];
        for (int k = 0; k < 4; k++) Si[k] = Inv[S[k]];
        memset(cA, 0, m); memset(cB, 0, m);
        /* precompute d(j,i) = s_j^-1 s_i and e(j,i) = s_j s_i^-1 */
        int dA[4][4], dB[4][4];
        for (int j = 0; j < 4; j++) for (int i = 0; i < 4; i++) { dA[j][i] = mul(Si[j], S[i]); dB[j][i] = mul(S[j], Si[i]); }
        for (int w = 0; w < nw; w++) {
            int i1 = W[w][0], i2 = W[w][1], i3 = W[w][2], i4 = W[w][3];
            cA[mul(dA[i4][i3], dA[i2][i1])] = 1;
            cB[mul(dB[i4][i3], dB[i2][i1])] = 1;
        }
        int c = 0; for (int i = 0; i < m; i++) c += !cA[i] + !cB[i];
        tried++;
        if (c < best) best = c;
        if (c == 0) { nsol++; if (nsol <= maxprint) printf("SOL S = %d %d %d %d\n", S[0], S[1], S[2], S[3]); }
    }
    printf("m=%d tried=%ld best_cost=%d solutions=%d\n", m, tried, best, nsol);
    return 0;
}
