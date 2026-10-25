/* cover4.c: greedy search for small sets X of pairwise opposite points of H(q) with every point within distance 4
   of X ("4-covering"); second-level hubs would need such column sets. cell-15-7 job. Usage: cover4 HEXBIN seed cand */
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
static void hbfs(int x, uint8_t *hd) {
    memset(hd, 255, 2 * N); int *qq = malloc(sizeof(int) * 2 * N), h = 0, t = 0; hd[x] = 0; qq[t++] = x;
    while (h < t) { int v = qq[h++];
        if (v < N) { for (int k = 0; k < Q1; k++) { int w = N + PL[v * Q1 + k]; if (hd[w] == 255) { hd[w] = hd[v] + 1; qq[t++] = w; } } }
        else { int l = v - N; for (int k = 0; k < Q1; k++) { int w = LP[l * Q1 + k]; if (hd[w] == 255) { hd[w] = hd[v] + 1; qq[t++] = w; } } } }
    free(qq);
}
int main(int argc, char **argv) {
    load(argv[1]); rs ^= atoll(argv[2]) * 0x9E3779B97F4A7C15ULL; int C = atoi(argv[3]);
    uint8_t *opp = malloc(N); memset(opp, 1, N);   /* opp[x] = 1 while x is opposite every chosen point */
    uint8_t *d = malloc(2 * N); int X[64], nx = 0;
    int p = rnd() % N; X[nx++] = p; hbfs(p, d); long left = 0; for (int x = 0; x < N; x++) { if (d[x] != 6) opp[x] = 0; left += opp[x]; }
    printf("size 1: %ld points opposite all\n", left);
    while (left > 0 && nx < 40) {
        int best = -1; long bl = left + 1; uint8_t *bd = malloc(2 * N);
        for (int c = 0; c < C; c++) {
            int cand; do { cand = rnd() % N; } while (!opp[cand]);   /* pairwise opposite: cand opposite all chosen */
            hbfs(cand, d); long l2 = 0; for (int x = 0; x < N; x++) if (opp[x] && d[x] == 6) l2++;
            if (l2 < bl) { bl = l2; best = cand; memcpy(bd, d, 2 * N); }
        }
        X[nx++] = best; for (int x = 0; x < N; x++) if (bd[x] != 6) opp[x] = 0; left = bl; free(bd);
        printf("size %d: %ld points opposite all\n", nx, left); fflush(stdout);
    }
    return 0;
}
