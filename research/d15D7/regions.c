/* regions.c: how well can one bijection M carry every freed pair's algebraic cover at once?
   For freed flags (p_a, l_a), p_a on l_a:  S'(p_a) = {points u: d(u,p_a)=4, d(u,l_a)=5},
   S(l_a) = {lines N: d(N,l_a)=4, d(N,p_a)=5}.  M must map S'(p_a) onto S(l_a) for every a; this is possible
   iff for every signature A (set of pairs) the number of points in exactly the S'(p_a), a in A, equals the number
   of lines in exactly the S(l_a), a in A. Prints the total deficit sum_A max(0, |R'_A| - |R_A|) (points that
   cannot keep all their covers), for K flags chosen with a given placement rule.
   Usage: regions HEXBIN K seed mode   (mode 0: points pairwise opposite, lines random through them;
                                        mode 1: flags pairwise opposite (points and lines);
                                        mode 2: no constraint) */
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
static int cmp(const void *a, const void *b) { uint64_t x = *(uint64_t *)a, y = *(uint64_t *)b; return x < y ? -1 : x > y; }
int main(int argc, char **argv) {
    load(argv[1]); int K = atoi(argv[2]); rs ^= atoll(argv[3]) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 20; i++) rnd();
    int mode = atoi(argv[4]);
    uint8_t **dp = malloc(sizeof(void *) * K), **dl = malloc(sizeof(void *) * K); int *P = malloc(4 * K), *L = malloc(4 * K);
    for (int a = 0; a < K; a++) {
        int ok = 0;
        for (int tr = 0; tr < 200000 && !ok; tr++) {
            int p = rnd() % N, l = PL[p * Q1 + rnd() % Q1]; ok = 1;
            static int ctr = -1, L0 = -1; if (ctr < 0) { ctr = rnd() % N; L0 = PL[ctr * Q1]; }
            if (mode == 3) { l = PL[ctr * Q1 + rnd() % Q1]; do { p = LP[l * Q1 + rnd() % Q1]; } while (p == ctr); }   /* star: l_a through a centre */
            if (mode == 4) { p = LP[L0 * Q1 + rnd() % Q1]; do { l = PL[p * Q1 + rnd() % Q1]; } while (l == L0); } /* points on one line L0 */
            for (int b = 0; b < a && ok; b++) if (P[b] == p || L[b] == l) ok = 0;
            for (int b = 0; b < a && ok; b++) {
                if (mode <= 1 && dp[b][p] != 6) ok = 0;
                if (mode == 1 && dl[b][N + l] != 6) ok = 0;
            }
            if (ok) { P[a] = p; L[a] = l; }
        }
        if (!ok) { printf("placed only %d\n", a); K = a; break; }
        dp[a] = malloc(2 * N); hbfs(P[a], 0, dp[a]); dl[a] = malloc(2 * N); hbfs(L[a], 1, dl[a]);
    }
    uint64_t *sp = calloc(N, 8), *sl = calloc(N, 8);
    for (int a = 0; a < K; a++) for (int v = 0; v < N; v++) {
        if (dp[a][v] == 4 && dl[a][v] == 5) sp[v] |= 1ULL << a;
        if (dl[a][N + v] == 4 && dp[a][N + v] == 5) sl[v] |= 1ULL << a;
    }
    qsort(sp, N, 8, cmp); qsort(sl, N, 8, cmp);
    long deficit = 0, multi = 0, nsig = 0; int i = 0, j = 0;
    while (i < N || j < N) {
        uint64_t s = (i < N && (j >= N || sp[i] <= sl[j])) ? sp[i] : sl[j];
        long ci = 0, cj = 0; while (i < N && sp[i] == s) { i++; ci++; } while (j < N && sl[j] == s) { j++; cj++; }
        if (s) { nsig++; if (ci > cj) deficit += ci - cj; if (__builtin_popcountll(s) >= 2) multi += ci; }
    }
    printf("K=%d mode=%d signatures=%ld points-in->=2-covers=%ld deficit=%ld (of %ld cover slots)\n", K, mode, nsig, multi, deficit, (long)K * q * q * q * q);
    return 0;
}
