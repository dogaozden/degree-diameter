/* 4-letter covering DFS for diag_exhaust2.py.  Input (stdin): needA needB, then for each of 4 letters: n, then n lines
   "mA mB" (64-bit masks).  Output: FOUND i0 i1 i2 i3 or NONE.  Pruning: letter j covers at most CAP points per side. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
int n[4]; uint64_t *A[4], *B[4], needA, needB; int CAP; long nodes = 0; int pick[4];
static int dfs(int j, uint64_t mA, uint64_t mB) {
    nodes++;
    uint64_t ma = needA & ~mA, mb = needB & ~mB;
    if (!ma && !mb) { for (int t = j; t < 4; t++) pick[t] = -1; return 1; }
    if (j == 4) return 0;
    int left = 4 - j;
    if (__builtin_popcountll(ma) > CAP * left || __builtin_popcountll(mb) > CAP * left) return 0;
    for (int i = 0; i < n[j]; i++) {
        if (j == 3 && ((ma & ~A[3][i]) || (mb & ~B[3][i]))) continue;
        pick[j] = i;
        if (dfs(j + 1, mA | A[j][i], mB | B[j][i])) return 1;
    }
    return 0;
}
int main(int argc, char **argv) {
    CAP = argc > 1 ? atoi(argv[1]) : 9;
    if (scanf("%lu %lu", &needA, &needB) != 2) return 2;
    for (int j = 0; j < 4; j++) { if (scanf("%d", &n[j]) != 1) return 3; A[j] = malloc(8 * (n[j] + 1)); B[j] = malloc(8 * (n[j] + 1));
        for (int i = 0; i < n[j]; i++) if (scanf("%lu %lu", &A[j][i], &B[j][i]) != 2) return 4; }
    int ok = dfs(0, 0, 0);
    if (ok) printf("FOUND %d %d %d %d nodes=%ld\n", pick[0], pick[1], pick[2], pick[3], nodes); else printf("NONE nodes=%ld\n", nodes);
    return 0;
}
