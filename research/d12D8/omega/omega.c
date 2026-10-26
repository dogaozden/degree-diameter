/* Gomez's bipartite compound graph Omega B_1 (thesis UPC 1986, sec. 2.9.3, pp. 43-46, Figs 2.21a/b) for B_1 = H(q).
   5*alpha copies of B_1 in alpha blocks of 5 (block type a = Fig. 2.21a, b = Fig. 2.21b) and 10 sets of n = N_1/2 new
   vertices ("copies of K_1"): (t,k) and (t,kbar), t in [n], k in Z_5. Copy c of block B is global copy 5B + c.
   Fig. 2.21a: new vertex k (on the star) ~ the inner dots of copies k-1, k+1; kbar (on the circle) ~ the outer dots of
               copies k+2, k+3.
   Fig. 2.21b: k (on the circle) ~ outer dots of copies k+3, k+4; kbar (on the star) ~ inner dots of copies k-1, k+1.
   Reading 1 (the thesis's own drawing convention, Figs 2.6, 2.18: the dot above the dashed line is class 0): outer dot
     = class 0 = point (t,0) = point t, inner dot = class 1 = line (t,1) = line sigma(t); sigma = a bijection points->lines
     (the thesis's labels (t,j) fix one; any bijection can be given in SIGMA, default sigma(t) = t).
     So (t,k) ~ line sigma(t) in a-copies, point t in b-copies; (t,kbar) ~ point t in a-copies, line sigma(t) in b-copies.
   Reading 2 (the Oct 25 session's mk_omega.py): new vertex k always on a point, kbar always on a line:
     (t,k) ~ point t (a: k+-1, b: k+3,k+4); (t,kbar) ~ line t (a: k+2,k+3; b: k+-1)  [line index t, no sigma].
   Vertex ids: copy c, local v (points 0..n-1, lines n..2n-1): c*N1 + v.  New: C*N1 + 10*t + 5*bar + k.
   Usage: omega HEX TYPES READING OUT [SIGMA]      (TYPES e.g. aaabbb; SIGMA: text file with n line indices in [0,n)) */
#include <stdio.h>
#include <stdlib.h>
int main(int argc, char **argv) {
    FILE *f = fopen(argv[1], "r"); int q, n, nl; if (fscanf(f, "%d %d %d", &q, &n, &nl) != 3) return 2;
    int *L = malloc(sizeof(int) * nl * (q + 1)); for (long i = 0; i < (long)nl * (q + 1); i++) if (fscanf(f, "%d", &L[i]) != 1) return 2;
    fclose(f);
    const char *types = argv[2]; int reading = atoi(argv[3]); int al = 0; while (types[al]) al++;
    int *sig = malloc(sizeof(int) * n); for (int t = 0; t < n; t++) sig[t] = t;
    if (argc > 5) { FILE *g = fopen(argv[5], "r"); for (int t = 0; t < n; t++) if (fscanf(g, "%d", &sig[t]) != 1) return 3; fclose(g); }
    long N1 = 2L * n, C = 5L * al, base = C * N1, nv = base + 10L * n;
    FILE *o = fopen(argv[4], "w"); fprintf(o, "%ld\n", nv); long ne = 0;
    for (long c = 0; c < C; c++) for (int l = 0; l < nl; l++) for (int j = 0; j <= q; j++) { fprintf(o, "%ld %ld\n", c * N1 + L[(long)l * (q + 1) + j], c * N1 + n + l); ne++; }
    for (int B = 0; B < al; B++) {
        int a = types[B] == 'a';
        for (int t = 0; t < n; t++) for (int k = 0; k < 5; k++) for (int bar = 0; bar < 2; bar++) {
            int cs[2];
            if (a) { if (!bar) { cs[0] = k + 4; cs[1] = k + 1; } else { cs[0] = k + 2; cs[1] = k + 3; } }
            else   { if (!bar) { cs[0] = k + 3; cs[1] = k + 4; } else { cs[0] = k + 4; cs[1] = k + 1; } }
            long v;   /* local vertex in B_1 */
            if (reading == 1) { int online = a ? !bar : bar; v = online ? n + sig[t] : t; }
            else v = bar ? n + t : t;
            long h = base + 10L * t + 5 * bar + k;
            for (int i = 0; i < 2; i++) { long c = 5L * B + cs[i] % 5; fprintf(o, "%ld %ld\n", h, c * N1 + v); ne++; }
        }
    }
    fclose(o); fprintf(stderr, "vertices %ld edges %ld (copies %ld x %ld + new %ld)\n", nv, ne, C, N1, 10L * n); return 0;
}
