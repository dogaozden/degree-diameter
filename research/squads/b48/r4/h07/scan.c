/* Exhaustive (or sampled) scan of cubic Cayley graphs of a group given by its table.
   Generator sets: three distinct involutions (type A), or {a, a^-1, t} with a of order >= 3, t an involution (type B).
   Cost = number of vertices at distance > D from identity (vertex-transitive: equals far count per vertex).
   Only connected bipartite Cayley graphs count. Usage: scan TABFILE D LIMIT SEED */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int N, *T, *inv, *I, nI, *A, nA;
int *dist, *q;
static inline int prod(int x, int y) { return T[(long)x * N + y]; }
int D;
/* returns cost or -1 if disconnected/non-bipartite; diam in *dm */
int evalS(int *S, int k, int *dm) {
    for (int i = 0; i < N; i++) dist[i] = -1;
    int h = 0, t = 0; q[t++] = 0; dist[0] = 0;
    while (h < t) {
        int x = q[h++];
        for (int j = 0; j < k; j++) {
            int y = prod(x, S[j]);
            if (dist[y] < 0) { dist[y] = dist[x] + 1; q[t++] = y; }
        }
    }
    if (t != N) return -1;
    for (int x = 0; x < N; x++)
        for (int j = 0; j < k; j++)
            if (((dist[x] ^ dist[prod(x, S[j])]) & 1) == 0) return -1;
    int far = 0, mx = 0;
    for (int x = 0; x < N; x++) { if (dist[x] > D) far++; if (dist[x] > mx) mx = dist[x]; }
    *dm = mx;
    return far;
}
int main(int argc, char **argv) {
    FILE *f = fopen(argv[1], "r");
    D = atoi(argv[2]);
    long LIMIT = atol(argv[3]);
    srand(atoi(argv[4]));
    if (fscanf(f, "%d", &N) != 1) return 1;
    T = malloc(sizeof(int) * (long)N * N);
    for (long i = 0; i < (long)N * N; i++) if (fscanf(f, "%d", &T[i]) != 1) return 2;
    fclose(f);
    inv = malloc(sizeof(int) * N);
    for (int x = 0; x < N; x++) for (int y = 0; y < N; y++) if (prod(x, y) == 0) inv[x] = y;
    I = malloc(sizeof(int) * N); A = malloc(sizeof(int) * N); nI = nA = 0;
    for (int x = 1; x < N; x++) {
        if (inv[x] == x) I[nI++] = x; else A[nA++] = x;
    }
    dist = malloc(sizeof(int) * N); q = malloc(sizeof(int) * N);
    int best = 1 << 30, bestS[3], bestk = 0, bestdm = 0, bestType = 0;
    long nA_eval = 0, nB_eval = 0, ok = 0, zero = 0;
    /* type B */
    int S[3];
    for (int ai = 0; ai < nA; ai++) {
        int a = A[ai];
        if (inv[a] < a) continue; /* each pair once */
        for (int ti = 0; ti < nI; ti++) {
            S[0] = a; S[1] = inv[a]; S[2] = I[ti];
            int dm, c = evalS(S, 3, &dm); nB_eval++;
            if (c >= 0) { ok++; if (c < best || (c == best && dm < bestdm)) { best = c; bestk = 3; memcpy(bestS, S, sizeof S); bestdm = dm; bestType = 2; } if (c == 0) zero++; }
        }
    }
    /* type A */
    double tot = (double)nI * (nI - 1) * (nI - 2) / 6.0;
    if (tot <= LIMIT) {
        for (int i = 0; i < nI; i++) for (int j = i + 1; j < nI; j++) for (int k2 = j + 1; k2 < nI; k2++) {
            S[0] = I[i]; S[1] = I[j]; S[2] = I[k2];
            int dm, c = evalS(S, 3, &dm); nA_eval++;
            if (c >= 0) { ok++; if (c < best || (c == best && dm < bestdm)) { best = c; bestk = 3; memcpy(bestS, S, sizeof S); bestdm = dm; bestType = 1; } if (c == 0) zero++; }
        }
    } else {
        for (long r = 0; r < LIMIT; r++) {
            int i = rand() % nI, j = rand() % nI, k2 = rand() % nI;
            if (i == j || j == k2 || i == k2) { r--; continue; }
            S[0] = I[i]; S[1] = I[j]; S[2] = I[k2];
            int dm, c = evalS(S, 3, &dm); nA_eval++;
            if (c >= 0) { ok++; if (c < best || (c == best && dm < bestdm)) { best = c; bestk = 3; memcpy(bestS, S, sizeof S); bestdm = dm; bestType = 1; } if (c == 0) zero++; }
        }
    }
    printf("RES N=%d nInv=%d nNonInv=%d evalA=%ld evalB=%ld okBip=%ld zero=%ld best=%d diam=%d type=%s S=%d,%d,%d\n",
           N, nI, nA, nA_eval, nB_eval, ok, zero, best == (1 << 30) ? -1 : best, bestdm, bestType == 1 ? "A" : bestType == 2 ? "B" : "-",
           bestS[0], bestS[1], bestS[2]);
    return 0;
}
