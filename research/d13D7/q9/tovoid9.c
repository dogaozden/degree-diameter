/* tovoid9.c: search for translation ovoids of Q(6,9) in the affine chart of e4 (side quest of job cell-13-7, for (11,7)).
   Points opposite e4 = (0,0,0,0,1,0,0): x = (1, a, b, c, c^2 - ae - bf, e, f); B(x,x') = Q'(x - x'),
   Q'(a,b,c,e,f) = c^2 - ae - bf.  Ansatz: e = Ea(a) + Eb(b) + Ec(c), f = Fa(a) + Fb(b) + Fc(c) with F_3-linear maps
   g(t) = g1 t + g3 t^3 (all F_3-linear maps F_9 -> F_9).  Then the 729 affine points + e4 are pairwise opposite iff
   c^2 - a e(a,b,c) - b f(a,b,c) != 0 for every (a,b,c) != 0.  F_9 = F_3[al], al^2 = 2, element a + 3b (as hexgen.c).
   Prints the first solution (the 12 coefficients) and writes the 730 points (7 coordinates each). usage: tovoid9 out.txt */
#include <stdio.h>
#include <stdlib.h>
static int ADD[9][9], MUL[9][9], NEG[9];
static int LIN[81][9];   /* LIN[g][t] = g1 t + g3 t^3, g = g1 + 9 g3 */
static int SQ[9];
static int ad(int a, int b) { return ADD[a][b]; }
static int mu(int a, int b) { return MUL[a][b]; }
int main(int argc, char **argv) {
    for (int x = 0; x < 9; x++) for (int y = 0; y < 9; y++) {
        int a = x % 3, b = x / 3, c = y % 3, d = y / 3;
        ADD[x][y] = (a + c) % 3 + 3 * ((b + d) % 3);
        MUL[x][y] = (a * c + 2 * b * d) % 3 + 3 * ((a * d + b * c) % 3);
    }
    for (int x = 0; x < 9; x++) for (int y = 0; y < 9; y++) if (ADD[x][y] == 0) NEG[x] = y;
    for (int t = 0; t < 9; t++) SQ[t] = mu(t, t);
    for (int g = 0; g < 81; g++) { int g1 = g % 9, g3 = g / 9; for (int t = 0; t < 9; t++) LIN[g][t] = ad(mu(g1, t), mu(g3, mu(t, mu(t, t)))); }
    /* Q'(a,b,c) given e,f values */
    long nodes = 0;
    for (int Ea = 0; Ea < 81; Ea++) {
        int ok = 1; for (int a = 1; a < 9 && ok; a++) if (mu(a, LIN[Ea][a]) == 0) ok = 0;   /* -a Ea(a) != 0 */
        if (!ok) continue;
        for (int Fb = 0; Fb < 81; Fb++) {
            ok = 1; for (int b = 1; b < 9 && ok; b++) if (mu(b, LIN[Fb][b]) == 0) ok = 0;
            if (!ok) continue;
            for (int Ec = 0; Ec < 81; Ec++) {
                ok = 1; for (int a = 1; a < 9 && ok; a++) for (int c = 0; c < 9 && ok; c++) if (SQ[c] == mu(a, ad(LIN[Ea][a], LIN[Ec][c]))) ok = 0;
                if (!ok) continue;
                for (int Fc = 0; Fc < 81; Fc++) {
                    ok = 1; for (int b = 1; b < 9 && ok; b++) for (int c = 0; c < 9 && ok; c++) if (SQ[c] == mu(b, ad(LIN[Fb][b], LIN[Fc][c]))) ok = 0;
                    if (!ok) continue;
                    for (int Eb = 0; Eb < 81; Eb++) for (int Fa = 0; Fa < 81; Fa++) {
                        nodes++;
                        ok = 1;
                        for (int a = 1; a < 9 && ok; a++) for (int b = 1; b < 9 && ok; b++) for (int c = 0; c < 9 && ok; c++) {
                            int e = ad(ad(LIN[Ea][a], LIN[Eb][b]), LIN[Ec][c]), f = ad(ad(LIN[Fa][a], LIN[Fb][b]), LIN[Fc][c]);
                            if (SQ[c] == ad(mu(a, e), mu(b, f))) ok = 0;
                        }
                        if (!ok) continue;
                        printf("solution: Ea=(%d,%d) Eb=(%d,%d) Ec=(%d,%d) Fa=(%d,%d) Fb=(%d,%d) Fc=(%d,%d) after %ld nodes\n",
                               Ea % 9, Ea / 9, Eb % 9, Eb / 9, Ec % 9, Ec / 9, Fa % 9, Fa / 9, Fb % 9, Fb / 9, Fc % 9, Fc / 9, nodes);
                        FILE *o = fopen(argv[1], "w");
                        fprintf(o, "# translation ovoid of Q(6,9): e4 + 729 affine points; F_9 = F_3[al], al^2 = 2, index a + 3b\n0 0 0 0 1 0 0\n");
                        for (int a = 0; a < 9; a++) for (int b = 0; b < 9; b++) for (int c = 0; c < 9; c++) {
                            int e = ad(ad(LIN[Ea][a], LIN[Eb][b]), LIN[Ec][c]), f = ad(ad(LIN[Fa][a], LIN[Fb][b]), LIN[Fc][c]);
                            int x4 = ad(SQ[c], NEG[ad(mu(a, e), mu(b, f))]);
                            fprintf(o, "1 %d %d %d %d %d %d\n", a, b, c, x4, e, f);
                        }
                        fclose(o);
                        return 0;
                    }
                }
            }
        }
    }
    printf("no solution (%ld nodes)\n", nodes);
    return 1;
}
