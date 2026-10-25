/* triples.c: |S'_a ∩ S'_b ∩ S'_c| vs |S_a ∩ S_b ∩ S_c| for random triples of flags (cell-15-7 job). */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
static int q, N, Q1; static int32_t *LP, *PL;
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static void load(const char *fn) {
    FILE *f = fopen(fn, "rb"); int32_t h[3]; if (!f || fread(h, 4, 3, f) != 3) exit(1);
    q = h[0]; N = h[1]; Q1 = q + 1; LP = malloc(4L * N * Q1); if (fread(LP, 4, (size_t)N * Q1, f) != (size_t)N * Q1) exit(1); fclose(f);
    PL = malloc(4L * N * Q1); int *c = calloc(N, 4);
    for (int l = 0; l < N; l++) for (int t = 0; t < Q1; t++) { int p = LP[l * Q1 + t]; PL[p * Q1 + c[p]++] = l; }
}
static void hbfs(int x, int isline, uint8_t *hd) {
    memset(hd, 255, 2 * N); int *qq = malloc(sizeof(int) * 2 * N), h = 0, t = 0; int s = isline ? N + x : x; hd[s] = 0; qq[t++] = s;
    while (h < t) { int v = qq[h++];
        if (v < N) { for (int k = 0; k < Q1; k++) { int w = N + PL[v * Q1 + k]; if (hd[w] == 255) { hd[w] = hd[v] + 1; qq[t++] = w; } } }
        else { int l = v - N; for (int k = 0; k < Q1; k++) { int w = LP[l * Q1 + k]; if (hd[w] == 255) { hd[w] = hd[v] + 1; qq[t++] = w; } } } }
    free(qq);
}
int main(int argc, char **argv) {
    load(argv[1]); int S = atoi(argv[2]); rs ^= atoll(argv[3]) * 0x9E3779B97F4A7C15ULL;
    uint8_t *dp[3], *dl[3]; for (int i = 0; i < 3; i++) { dp[i] = malloc(2 * N); dl[i] = malloc(2 * N); }
    long hist[64] = {0};
    for (int s = 0; s < S; s++) {
        int P[3], L[3];
        for (int i = 0; i < 3; i++) { P[i] = rnd() % N; L[i] = PL[P[i] * Q1 + rnd() % Q1]; hbfs(P[i], 0, dp[i]); hbfs(L[i], 1, dl[i]); }
        long A = 0, B = 0, pa[3] = {0}, pb[3] = {0};
        for (int v = 0; v < N; v++) {
            int ia = 0, ib = 0;
            for (int i = 0; i < 3; i++) { if (dp[i][v] == 4 && dl[i][v] == 5) ia |= 1 << i; if (dl[i][N + v] == 4 && dp[i][N + v] == 5) ib |= 1 << i; }
            if (ia == 7) A++; if (ib == 7) B++;
        }
        int pos[3][4]; for (int i = 0; i < 3; i++) { int j = (i + 1) % 3; pos[i][0] = dp[i][P[j]]; pos[i][1] = dp[i][N + L[j]]; pos[i][2] = dl[i][P[j]]; pos[i][3] = dl[i][N + L[j]]; }
        printf("triple %d: |S'^3| = %ld  |S^3| = %ld  diff %+ld   pairs %d%d%d%d %d%d%d%d %d%d%d%d\n", s, A, B, A - B,
               pos[0][0], pos[0][1], pos[0][2], pos[0][3], pos[1][0], pos[1][1], pos[1][2], pos[1][3], pos[2][0], pos[2][1], pos[2][2], pos[2][3]);
    }
    return 0;
}
