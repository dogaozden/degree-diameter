/* Exhaustive Haar search at (6,5) for one group, modulo automorphisms (job fresh-6-5).
 *
 * H(G,S), |S| = 6, has diameter <= 5 iff (S^-1 S)^2 = G and (S S^-1)^2 = G. H(G,S) = H(G,phi(S)) up to
 * isomorphism for phi in Aut(G), and H(G,S) = H(G,S g) for g in G, so WLOG e in S. Every such S is mapped by
 * an automorphism onto a set containing e, r, r2 with r an Aut-orbit representative on G\{e} and r2 a
 * Stab(r)-orbit representative on G\{e,r}; the input lists those pairs (from GAP, haarex.g). The program
 * then tries every 3-subset of the remaining elements: exhaustive.
 *
 * input file: N, then the N x N multiplication table (0-based, element 0 = identity), then the number of
 * (r, r2) pairs and the pairs.  usage: haarex FILE [PAIR_FROM PAIR_TO]
 * output: for every pair, the minimum A-side uncovered count; every S with both sides covered (VALID).
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

#define W 8   /* up to 512 elements */
static int N, *M, *INV;
static inline int mul(int a, int b) { return M[a * N + b]; }

static int cover_count(const int *Q, int nq) {
    uint64_t c[W] = {0};
    for (int i = 0; i < nq; i++) { const int *row = M + Q[i] * N; for (int j = 0; j < nq; j++) { int x = row[Q[j]]; c[x >> 6] |= 1ULL << (x & 63); } }
    int t = 0; for (int w = 0; w < W; w++) t += __builtin_popcountll(c[w]);
    return t;
}

int main(int argc, char **argv) {
    FILE *f = fopen(argv[1], "r"); if (!f) return 2;
    if (fscanf(f, "%d", &N) != 1 || N > 64 * W) return 2;
    M = malloc(sizeof(int) * N * N); INV = malloc(sizeof(int) * N);
    for (int i = 0; i < N * N; i++) if (fscanf(f, "%d", &M[i]) != 1) return 2;
    for (int a = 0; a < N; a++) for (int b = 0; b < N; b++) if (M[a * N + b] == 0) INV[a] = b;
    int np; if (fscanf(f, "%d", &np) != 1) return 2;
    int *pr = malloc(sizeof(int) * 2 * np);
    for (int i = 0; i < 2 * np; i++) if (fscanf(f, "%d", &pr[i]) != 1) return 2;
    fclose(f);
    int p0 = argc > 3 ? atoi(argv[2]) : 0, p1 = argc > 3 ? atoi(argv[3]) : np;
    long total = 0, nvalid = 0; int gmin = N;
    long hist[64] = {0};
    for (int p = p0; p < p1 && p < np; p++) {
        int S[6]; S[0] = 0; S[1] = pr[2 * p]; S[2] = pr[2 * p + 1];
        int pmin = N;
        for (int a = 1; a < N; a++) {
            if (a == S[1] || a == S[2]) continue;
            for (int b = a + 1; b < N; b++) {
                if (b == S[1] || b == S[2]) continue;
                S[3] = a; S[4] = b;
                /* Q5 = quotients s_i^-1 s_j among the first five, cover5 = Q5 Q5 */
                int Q5[32], n5 = 0;
                for (int i = 0; i < 5; i++) for (int j = 0; j < 5; j++) if (i != j) Q5[n5++] = mul(INV[S[i]], S[j]);
                Q5[n5++] = 0;
                uint64_t c5[W] = {0};
                for (int i = 0; i < n5; i++) { const int *row = M + Q5[i] * N; for (int j = 0; j < n5; j++) { int x = row[Q5[j]]; c5[x >> 6] |= 1ULL << (x & 63); } }
                for (int c = b + 1; c < N; c++) {
                    if (c == S[1] || c == S[2]) continue;
                    total++;
                    int Qn[10], nn = 0;
                    for (int i = 0; i < 5; i++) { Qn[nn++] = mul(INV[c], S[i]); Qn[nn++] = mul(INV[S[i]], c); }
                    uint64_t cv[W]; memcpy(cv, c5, sizeof cv);
                    for (int i = 0; i < nn; i++) {
                        const int *row = M + Qn[i] * N;
                        for (int j = 0; j < n5; j++) { int x = row[Q5[j]]; cv[x >> 6] |= 1ULL << (x & 63); }
                        for (int j = 0; j < nn; j++) { int x = row[Qn[j]]; cv[x >> 6] |= 1ULL << (x & 63); }
                    }
                    for (int i = 0; i < n5; i++) { const int *row = M + Q5[i] * N; for (int j = 0; j < nn; j++) { int x = row[Qn[j]]; cv[x >> 6] |= 1ULL << (x & 63); } }
                    int t = 0; for (int w = 0; w < W; w++) t += __builtin_popcountll(cv[w]);
                    int unc = N - t;
                    if (unc < pmin) pmin = unc;
                    hist[unc < 63 ? unc : 63]++;
                    if (unc == 0) {   /* A side covered: check the B side (S S^-1)^2 */
                        S[5] = c;
                        int P[32], npp = 0;
                        for (int i = 0; i < 6; i++) for (int j = 0; j < 6; j++) if (i != j) P[npp++] = mul(S[i], INV[S[j]]);
                        P[npp++] = 0;
                        int tb = cover_count(P, npp);
                        if (tb == N) {
                            nvalid++;
                            printf("VALID S = %d %d %d %d %d %d\n", S[0], S[1], S[2], S[3], S[4], S[5]); fflush(stdout);
                        } else printf("ASIDE S = %d %d %d %d %d %d Bunc=%d\n", S[0], S[1], S[2], S[3], S[4], S[5], N - tb);
                    }
                }
            }
        }
        if (pmin < gmin) gmin = pmin;
        printf("PAIR %d r=%d r2=%d minA=%d\n", p, S[1], S[2], pmin); fflush(stdout);
    }
    printf("DONE N=%d pairs=%d..%d sets=%ld valid=%ld minA=%d hist", N, p0, p1, total, nvalid, gmin);
    for (int c = 0; c < 64; c++) if (hist[c] && c < 12) printf(" %d:%ld", c, hist[c]);
    printf("\n");
    return 0;
}
