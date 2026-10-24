/* pairs.c: overlaps of the exact covers of two freed flags, by relative position. cell-15-7 job.
   For flags F_a = (p_a,l_a), F_b: alpha = |S'(p_a) ∩ S'(p_b)| (points), beta = |S(l_a) ∩ S(l_b)| (lines).
   The relative position is recorded as (d(p_a,p_b), d(p_a,l_b), d(l_a,p_b), d(l_a,l_b)).
   Usage: pairs HEXBIN samples seed */
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
    uint8_t *dpa = malloc(2 * N), *dla = malloc(2 * N), *dpb = malloc(2 * N), *dlb = malloc(2 * N);
    int pa = rnd() % N, la = PL[pa * Q1]; hbfs(pa, 0, dpa); hbfs(la, 1, dla);
    /* seen positions: key = d1*1000+d2*100+d3*10+d4 */
    static long seen[10000]; static long al[10000], be[10000];
    for (int s = 0; s < S; s++) {
        int pb, lb;
        /* bias: half the samples near F_a (walk a few steps), half random */
        if (s % 2) { pb = rnd() % N; lb = PL[pb * Q1 + rnd() % Q1]; }
        else { int v = pa, isl = 0, steps = 1 + rnd() % 6;
            for (int t = 0; t < steps; t++) { if (!isl) { v = PL[v * Q1 + rnd() % Q1]; isl = 1; } else { v = LP[v * Q1 + rnd() % Q1]; isl = 0; } }
            if (isl) { lb = v; pb = LP[lb * Q1 + rnd() % Q1]; } else { pb = v; lb = PL[pb * Q1 + rnd() % Q1]; } }
        if (pb == pa && lb == la) continue;
        int key = dpa[pb] * 1000 + dpa[N + lb] * 100 + dla[pb] * 10 + dla[N + lb];
        if (seen[key] >= 3) continue;
        hbfs(pb, 0, dpb); hbfs(lb, 1, dlb);
        long A = 0, Bt = 0;
        for (int v = 0; v < N; v++) {
            if (dpa[v] == 4 && dla[v] == 5 && dpb[v] == 4 && dlb[v] == 5) A++;
            if (dla[N + v] == 4 && dpa[N + v] == 5 && dlb[N + v] == 4 && dpb[N + v] == 5) Bt++;
        }
        if (seen[key] && (al[key] != A || be[key] != Bt)) printf("position %04d not determined: %ld/%ld vs %ld/%ld\n", key, al[key], be[key], A, Bt);
        seen[key]++; al[key] = A; be[key] = Bt;
    }
    printf("d(pa,pb) d(pa,lb) d(la,pb) d(la,lb) : |S'∩S'| |S∩S|\n");
    for (int k = 0; k < 10000; k++) if (seen[k]) printf("%d %d %d %d : %ld %ld%s\n", k / 1000, k / 100 % 10, k / 10 % 10, k % 10, al[k], be[k], al[k] == be[k] ? "" : "   <- unbalanced");
    return 0;
}
