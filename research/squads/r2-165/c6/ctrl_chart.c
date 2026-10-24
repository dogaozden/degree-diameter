/* Chart-aware exhaustive search for Haar controllers H(G,S), |S| = 4 (squad165 round 2, card C6).
   Copy of ctrl_relax.c with the cost replaced by the chart-aware rule of mlift_chart.c:
   controller H(G,S), S = (s_0..s_3): A-vertex g ~ B-vertex s_i g, edge colour i.  A same-side pair (source, x) is
   covered iff
     - x = s_j^-1 s_i (A side) or s_j s_i^-1 (B side) for some i != j (a walk of length 2, not the source), or
     - x is the end of a nonbacktracking walk of length 4, colours (i1,i2,i3,i4), i1!=i2!=i3!=i4, whose pattern
       is nonsingular (rank 4).  Ends: A: s_i4^-1 s_i3 s_i2^-1 s_i1 ; B: s_i4 s_i3^-1 s_i2 s_i1^-1.
   Cost = #{x in G uncovered on A} + #{x in G uncovered on B}.  The identity is a target (it needs a nonsingular
   nonbacktracking 4-cycle), exactly as in mlift_chart.c.  Cost 0 = perfect controller.
   Search: ALL ordered 4-tuples S with S[idcol] = e and the other three entries distinct non-identity elements.
   Left translation S -> cS leaves every word end unchanged, so idcol = 0 is WLOG; idcol != 0 is a cross-check.
   usage: ctrl_chart TABLE PATTERN [maxprint] [idcol]
   TABLE: "m" then m*m ints, T[i*m+j] = index of i*j.  PATTERN: 216 lines "A|B i1 i2 i3 i4 rank" (rank < 4 = singular).
   Output: "SOL S = s0 s1 s2 s3" for the first maxprint cost-0 tuples, then one summary line. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int m, *T, e, Inv[4096];
static inline int mul(int a, int b) { return T[a * m + b]; }
int nA = 0, nB = 0, WA[108][4], WB[108][4];
int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: ctrl_chart TABLE PATTERN [maxprint] [idcol]\n"); return 1; }
    int maxprint = argc > 3 ? atoi(argv[3]) : 3, idcol = argc > 4 ? atoi(argv[4]) : 0;
    FILE *f = fopen(argv[1], "r"); if (!f) return 2;
    if (fscanf(f, "%d", &m) != 1) return 2;
    T = malloc(sizeof(int) * m * m);
    for (int i = 0; i < m * m; i++) if (fscanf(f, "%d", &T[i]) != 1) return 3;
    fclose(f);
    e = -1;
    for (int i = 0; i < m; i++) { int ok = 1; for (int j = 0; j < m; j++) if (T[i * m + j] != j) { ok = 0; break; } if (ok) e = i; }
    if (e < 0) return 4;
    for (int i = 0; i < m; i++) for (int j = 0; j < m; j++) if (T[i * m + j] == e) Inv[i] = j;
    f = fopen(argv[2], "r"); if (!f) return 5;
    char side[4]; int a1, a2, a3, a4, r, np = 0;
    while (fscanf(f, "%3s %d %d %d %d %d", side, &a1, &a2, &a3, &a4, &r) == 6) {
        np++;
        if (r < 4) continue;                       /* singular: never covers */
        int *w;
        if (side[0] == 'A') { w = WA[nA++]; } else { w = WB[nB++]; }
        w[0] = a1; w[1] = a2; w[2] = a3; w[3] = a4;
    }
    fclose(f);
    if (np != 216) { printf("pattern file has %d lines\n", np); return 6; }
    int others[4096], no = 0;
    for (int i = 0; i < m; i++) if (i != e) others[no++] = i;
    char *hA = malloc(m), *hB = malloc(m);
    int best = 1 << 30, nbest = 0, nsol = 0, bestS[4] = {0}; long tried = 0;
    for (int x = 0; x < no; x++) for (int y = 0; y < no; y++) if (y != x)
    for (int z = 0; z < no; z++) if (z != x && z != y) {
        int vals[3] = { others[x], others[y], others[z] }, vi = 0, S[4], Si[4];
        for (int c = 0; c < 4; c++) S[c] = (c == idcol) ? e : vals[vi++];
        for (int c = 0; c < 4; c++) Si[c] = Inv[S[c]];
        int dA[4][4], dB[4][4];
        for (int j = 0; j < 4; j++) for (int i = 0; i < 4; i++) { dA[j][i] = mul(Si[j], S[i]); dB[j][i] = mul(S[j], Si[i]); }
        memset(hA, 0, m); memset(hB, 0, m);
        for (int j = 0; j < 4; j++) for (int i = 0; i < 4; i++) if (i != j) { hA[dA[j][i]] = 1; hB[dB[j][i]] = 1; }
        for (int w = 0; w < nA; w++) hA[mul(dA[WA[w][3]][WA[w][2]], dA[WA[w][1]][WA[w][0]])] = 1;
        for (int w = 0; w < nB; w++) hB[mul(dB[WB[w][3]][WB[w][2]], dB[WB[w][1]][WB[w][0]])] = 1;
        int c = 0; for (int t = 0; t < m; t++) c += !hA[t] + !hB[t];
        tried++;
        if (c < best) { best = c; nbest = 1; memcpy(bestS, S, sizeof S); }
        else if (c == best) nbest++;
        if (c == 0) { nsol++; if (nsol <= maxprint) printf("SOL S = %d %d %d %d\n", S[0], S[1], S[2], S[3]); }
    }
    printf("m=%d pattern=%s idcol=%d nA=%d nB=%d tried=%ld best_cost=%d nbest=%d solutions=%d bestS=%d %d %d %d\n",
           m, argv[2], idcol, nA, nB, tried, best, nbest, nsol, bestS[0], bestS[1], bestS[2], bestS[3]);
    return 0;
}
