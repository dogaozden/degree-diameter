/* max over random/hill-climbed S (|S|=6) of the rotation part of (S^-1 S)^2 in D_m = Z_m : Z_2 (inversion) */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
static int m;
/* element (a, e): a in Z_m, e in {0,1}; (a,e)(b,f) = (a + (e ? -b : b), e ^ f) */
static void mul(int a, int e, int b, int f, int *c, int *g) { *c = ((a + (e ? -b : b)) % m + m) % m; *g = e ^ f; }
static void inv(int a, int e, int *c, int *g) { if (e) { *c = a; *g = 1; } else { *c = (m - a) % m; *g = 0; } }
static int rotcount(int *A, int *E) {
    static char seen[100000]; memset(seen, 0, m);
    int Qa[64], Qe[64], nq = 0;
    for (int i = 0; i < 6; i++) for (int j = 0; j < 6; j++) { int ia, ie; inv(A[i], E[i], &ia, &ie); mul(ia, ie, A[j], E[j], &Qa[nq], &Qe[nq]); nq++; }
    int cnt = 0;
    for (int i = 0; i < nq; i++) for (int j = 0; j < nq; j++) { int c, g; mul(Qa[i], Qe[i], Qa[j], Qe[j], &c, &g); if (!g && !seen[c]) { seen[c] = 1; cnt++; } }
    return cnt;
}
int main(int argc, char **argv) {
    m = atoi(argv[1]); long iters = atol(argv[2]); srand(atoi(argv[3]));
    int best = 0;
    for (int k = 1; k <= 5; k++) for (int rep = 0; rep < 20; rep++) {
        int A[6], E[6]; for (int i = 0; i < 6; i++) { A[i] = rand() % m; E[i] = i >= k; }
        int cur = rotcount(A, E);
        for (long t = 0; t < iters; t++) { int i = rand() % 6, old = A[i]; A[i] = rand() % m; int c = rotcount(A, E); if (c >= cur) cur = c; else A[i] = old; }
        if (cur > best) { best = cur; printf("k=%d new best rotation count %d\n", k, best); }
    }
    printf("m=%d max rotation count found %d (lemma: <= 131)\n", m, best);
}
