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
    if (A > 4000) { printf("pass ? (A = %d too large; not filtered)\n", A); return 0; }
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
