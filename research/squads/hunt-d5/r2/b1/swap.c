/* swap.c TABLE.bin "s0 s1 ... s6" LIMIT : exhaustive 1-swap and 2-swap neighbourhood of S (s0 = 0 kept) for d-set Haar cost.
   Cost = uncovered of (S^-1 S)^2 plus uncovered of (S S^-1)^2, same as haar5. Prints min cost and all sets with cost <= LIMIT. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
static int N; static uint16_t *MT; static int INV[1024];
static uint32_t *stamp; static uint32_t ep = 0; static int T[128];
static int side(const int *S, int n, int sideB) {
    int nt = 0; ep++;
    for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) {
        int t = sideB ? MT[(size_t)S[i] * N + INV[S[j]]] : MT[(size_t)INV[S[i]] * N + S[j]];
        if (stamp[t] != ep) { stamp[t] = ep; T[nt++] = t; }
    }
    ep++; int cov = 0;
    for (int i = 0; i < nt; i++) for (int j = 0; j < nt; j++) {
        int g = MT[(size_t)T[i] * N + T[j]]; if (stamp[g] != ep) { stamp[g] = ep; cov++; }
    }
    return N - cov;
}
static int cost(const int *S, int n) { return side(S, n, 0) + side(S, n, 1); }
int main(int argc, char **argv) {
    FILE *f = fopen(argv[1], "rb"); int32_t nn; fread(&nn, 4, 1, f); N = nn;
    MT = malloc((size_t)N * N * 2); fread(MT, 2, (size_t)N * N, f); fclose(f);
    stamp = calloc(N + 1, 4);
    for (int a = 0; a < N; a++) for (int b = 0; b < N; b++) if (MT[(size_t)a * N + b] == 0) { INV[a] = b; break; }
    int S[16], n = 0; char *p = argv[2]; char *e;
    while (n < 16) { long v = strtol(p, &e, 10); if (e == p) break; S[n++] = (int)v; p = e; }
    int limit = atoi(argv[3]);
    int c0 = cost(S, n); printf("base cost %d n=%d\n", c0, n);
    int best = c0; long long cnt1 = 0, cnt2 = 0;
    int in[1024] = {0}; for (int i = 0; i < n; i++) in[S[i]] = 1;
    /* 1-swap: position i (1..n-1) to any value v not in S */
    for (int i = 1; i < n; i++) for (int v = 1; v < N; v++) if (!in[v]) {
        int R[16]; memcpy(R, S, sizeof(int) * n); R[i] = v; int c = cost(R, n); cnt1++;
        if (c < best) best = c;
        if (c <= limit) { printf("1swap cost %d:", c); for (int k = 0; k < n; k++) printf(" %d", R[k]); printf("\n"); }
    }
    printf("1-swap: evaluated %lld, best %d\n", cnt1, best); fflush(stdout);
    /* 2-swap: positions i<j (1..n-1), values v<w */
    for (int i = 1; i < n; i++) for (int j = i + 1; j < n; j++)
    for (int v = 1; v < N; v++) if (!in[v]) for (int w = v + 1; w < N; w++) if (!in[w]) {
        int R[16]; memcpy(R, S, sizeof(int) * n); R[i] = v; R[j] = w; int c = cost(R, n); cnt2++;
        if (c < best) { best = c; }
        if (c <= limit) { printf("2swap cost %d:", c); for (int k = 0; k < n; k++) printf(" %d", R[k]); printf("\n"); }
    }
    printf("2-swap: evaluated %lld, best %d\n", cnt2, best);
    return 0;
}
