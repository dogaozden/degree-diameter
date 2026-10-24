/* abfilt.c: rigorous abelianization filter for Haar graphs H(G,S), |S| = DELTA, diameter <= D.

   Walks of H(G,S) project to walks of H(A, S-bar), A = G/G' (abelian).  Every target vertex within D-1 of the source
   is the end of a non-backtracking walk of length <= D-1 (its geodesic), so every G'-coset on the target side needs at
   least K = |G'| such walks.  D even: source (e,A), targets on side B (odd lengths).  D odd: source (e,A), targets on
   side A (even lengths), and the mirror condition from (e,B) (= the same count for -S-bar, so the same condition up to
   z -> -z, which this program also checks).
   Usage: abfilt DELTA D K d1 [d2 ...]      (A = Z_d1 x Z_d2 x ...)
   Prints "pass P of T" where T = number of multisets {x1 <= ... <= x_{DELTA-1}} (S-bar = {0, x1, ...}) and P = number
   that satisfy the condition.  Exit code 0 iff P > 0.
*/
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int na, dd[8], A = 1, DELTA, D; static long long K;

static int add(int x, int y, int sgn) {   /* x + sgn*y in A, mixed radix */
    int z = 0, mult = 1;
    for (int i = 0; i < na; i++) {
        int xi = (x / mult) % dd[i], yi = (y / mult) % dd[i];
        int zi = ((xi + sgn * yi) % dd[i] + dd[i]) % dd[i];
        z += zi * mult; mult *= dd[i];
    }
    return z;
}

static int **ADD, **SUB;

static int ok_dir(const int *sb, int startB) {
    int L = DELTA + 1;
    long long *cur = calloc((size_t)2 * A * L, 8), *nxt = calloc((size_t)2 * A * L, 8), *tot = calloc(A, 8);
    int tside = (D % 2 == 0) ? !startB : startB;
#define IX(s, v, l) (((size_t)(s) * A + (v)) * L + (l))
    cur[IX(startB, 0, DELTA)] = 1;
    if (tside == startB) tot[0]++;
    for (int len = 1; len <= D - 1; len++) {
        memset(nxt, 0, 8 * (size_t)2 * A * L);
        for (int s = 0; s < 2; s++) for (int v = 0; v < A; v++) for (int l = 0; l < L; l++) {
            long long c = cur[IX(s, v, l)]; if (!c) continue;
            for (int t = 0; t < DELTA; t++) if (t != l) {
                int w = s == 0 ? ADD[sb[t]][v] : SUB[sb[t]][v];
                nxt[IX(1 - s, w, t)] += c;
            }
        }
        long long *tmp = cur; cur = nxt; nxt = tmp;
        int sn = (startB + len) & 1;
        if (sn == tside) for (int v = 0; v < A; v++) for (int l = 0; l < L; l++) tot[v] += cur[IX(sn, v, l)];
    }
#undef IX
    int ok = 1; for (int v = 0; v < A; v++) if (tot[v] < K) { ok = 0; break; }
    free(cur); free(nxt); free(tot); return ok;
}

int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage: abfilt DELTA D K d1 [d2 ...]\n"); return 2; }
    DELTA = atoi(argv[1]); D = atoi(argv[2]); K = atoll(argv[3]); na = argc - 4;
    for (int i = 0; i < na; i++) { dd[i] = atoi(argv[4 + i]); A *= dd[i]; }
    /* generic bound: S-bar = {0, e1, ..., e_{DELTA-1}} in Z^{DELTA-1} gives the most distinct walk images; every
       element of A must be an image, so A <= that count.  (BFS over integer vectors, coordinates in [-D, D].) */
    {
        int dim = DELTA - 1, R = D + 1, W = 2 * R + 1; long long cells = 1; for (int i = 0; i < dim; i++) cells *= W;
        if (cells <= 50000000LL) {
            char *seen[2]; seen[0] = calloc(cells, 1); seen[1] = calloc(cells, 1);
            long long *fr = malloc(sizeof(long long) * cells), *nf = malloc(sizeof(long long) * cells); long long nfr = 0, nnf;
            long long stride[8]; stride[0] = 1; for (int i = 1; i < dim; i++) stride[i] = stride[i - 1] * W;
            long long origin = 0; for (int i = 0; i < dim; i++) origin += R * stride[i];
            long long count[2] = {0, 0};
            for (int startB = 0; startB < 2; startB++) {
                memset(seen[0], 0, cells); memset(seen[1], 0, cells);
                int tside = (D % 2 == 0) ? !startB : startB;
                nfr = 0; fr[nfr++] = origin; seen[startB][origin] = 1; int side = startB;
                for (int len = 1; len <= D - 1; len++) {
                    nnf = 0;
                    for (long long t = 0; t < nfr; t++) {
                        long long v = fr[t];
                        for (int g = 0; g < DELTA; g++) {
                            long long w = v; if (g > 0) w += (side == 0 ? 1 : -1) * stride[g - 1];
                            if (!seen[1 - side][w]) { seen[1 - side][w] = 1; nf[nnf++] = w; }
                        }
                    }
                    long long *tmp = fr; fr = nf; nf = tmp; nfr = nnf; side = 1 - side;
                }
                for (long long c = 0; c < cells; c++) count[startB] += seen[tside][c];
                if (D % 2 == 0) { count[1] = count[0]; break; }
            }
            long long gen = count[0] < count[1] ? count[0] : count[1];
            free(seen[0]); free(seen[1]); free(fr); free(nf);
            if (A > gen) { printf("pass 0 of 0 (A = %d > generic image count %lld)\n", A, gen); return 1; }
        }
    }
    {   long long tuples = 1; for (int i = 0; i < DELTA - 1; i++) tuples *= A;
        if (tuples > 3000000LL || A > 4000) { printf("pass ? (A = %d, %lld tuples: not enumerated)\n", A, tuples); return 0; } }
    ADD = malloc(sizeof(int *) * A); SUB = malloc(sizeof(int *) * A);
    for (int x = 0; x < A; x++) { ADD[x] = malloc(sizeof(int) * A); SUB[x] = malloc(sizeof(int) * A);
        for (int v = 0; v < A; v++) { ADD[x][v] = add(v, x, 1); SUB[x][v] = add(v, x, -1); } }
    int m = DELTA - 1, x[8]; for (int i = 0; i < m; i++) x[i] = 0;
    long long T = 0, P = 0;
    for (;;) {
        int sb[9]; sb[0] = 0; for (int i = 0; i < m; i++) sb[i + 1] = x[i];
        T++;
        if (ok_dir(sb, 0) && (D % 2 == 0 || ok_dir(sb, 1))) P++;
        int i = m - 1; while (i >= 0 && x[i] == A - 1) i--;
        if (i < 0) break;
        x[i]++; for (int j = i + 1; j < m; j++) x[j] = x[i];
    }
    printf("pass %lld of %lld\n", P, T);
    return P > 0 ? 0 : 1;
}
