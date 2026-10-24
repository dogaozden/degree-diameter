/* Joint covering search for diag_exhaust3.py.  Input (stdin): needA needB; then for each letter s = 0..3:
   nA, nA masks; nB, nB masks; nR, nR pairs "iA iB" (the A-mask/B-mask pairs realised by some star collineation).
   Finds 4-tuples of A-masks covering needA (meet in the middle over letters {0,1} x {2,3}); for each, tests whether
   B-masks compatible with them (pairs in R_s) cover needB.  Prints counts and FOUND/NONE. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
typedef uint64_t u64;
int nA[4], nB[4], nR[4]; u64 *MA[4], *MB[4]; int *RA[4], *RB[4]; u64 needA, needB;
int *adjStart[4], *adjList[4];   /* for each letter, A-index -> list of compatible B-indices */
long tuplesA = 0, tested = 0; int found = 0; int sol[8];
static int bcover(int s, u64 got, const int *ia) {
    if (s == 4) return (needB & ~got) == 0;
    u64 miss = needB & ~got; int left = 4 - s;
    if (__builtin_popcountll(miss) > 9 * left) return 0;
    int a = ia[s];
    for (int t = adjStart[s][a]; t < adjStart[s][a + 1]; t++) { int jb = adjList[s][t];
        if (s == 3 && (miss & ~MB[3][jb])) continue;
        sol[4 + s] = jb;
        if (bcover(s + 1, got | MB[s][jb], ia)) return 1; }
    return 0; }
int main(void) {
    if (scanf("%lu %lu", &needA, &needB) != 2) return 2;
    for (int s = 0; s < 4; s++) {
        if (scanf("%d", &nA[s]) != 1) return 3; MA[s] = malloc(8 * nA[s]); for (int i = 0; i < nA[s]; i++) if (scanf("%lu", &MA[s][i]) != 1) return 3;
        if (scanf("%d", &nB[s]) != 1) return 3; MB[s] = malloc(8 * nB[s]); for (int i = 0; i < nB[s]; i++) if (scanf("%lu", &MB[s][i]) != 1) return 3;
        if (scanf("%d", &nR[s]) != 1) return 3; RA[s] = malloc(4 * nR[s]); RB[s] = malloc(4 * nR[s]);
        for (int i = 0; i < nR[s]; i++) if (scanf("%d %d", &RA[s][i], &RB[s][i]) != 2) return 3;
        adjStart[s] = calloc(nA[s] + 1, sizeof(int)); adjList[s] = malloc(4 * nR[s]);
        for (int i = 0; i < nR[s]; i++) adjStart[s][RA[s][i] + 1]++;
        for (int i = 0; i < nA[s]; i++) adjStart[s][i + 1] += adjStart[s][i];
        int *fill = calloc(nA[s], sizeof(int));
        for (int i = 0; i < nR[s]; i++) { int a = RA[s][i]; adjList[s][adjStart[s][a] + fill[a]++] = RB[s][i]; }
        free(fill); }
    /* right half: all (i2, i3) A-mask unions */
    long nRight = (long)nA[2] * nA[3]; u64 *RU = malloc(8 * nRight);
    for (int i = 0; i < nA[2]; i++) for (int j = 0; j < nA[3]; j++) RU[(long)i * nA[3] + j] = (MA[2][i] | MA[3][j]) & needA;
    int ia[4];
    for (int i0 = 0; i0 < nA[0] && !found; i0++) for (int i1 = 0; i1 < nA[1] && !found; i1++) {
        u64 L = (MA[0][i0] | MA[1][i1]) & needA, miss = needA & ~L;
        if (__builtin_popcountll(miss) > 18) continue;
        for (long r = 0; r < nRight; r++) { if (miss & ~RU[r]) continue;
            tuplesA++; ia[0] = i0; ia[1] = i1; ia[2] = (int)(r / nA[3]); ia[3] = (int)(r % nA[3]);
            tested++;
            if (bcover(0, 0, ia)) { found = 1; memcpy(sol, ia, sizeof ia); break; } } }
    if (found) printf("FOUND A-masks %d %d %d %d B-masks %d %d %d %d (A-covering tuples seen %ld)\n", sol[0], sol[1], sol[2], sol[3], sol[4], sol[5], sol[6], sol[7], tuplesA);
    else printf("NONE (A-covering tuples %ld, each tested for a compatible B-covering)\n", tuplesA);
    return 0; }
