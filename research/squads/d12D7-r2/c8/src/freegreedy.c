/* freegreedy.c (card c8, q=3): greedily free matching edges of the 5-level H(3) cover while the main graph keeps
   diameter <= 7 (exact all-pairs check, bit-parallel BFS, 64 sources per block).
   BASE.txt: first line n, then lines "u v tag": tag = matching index 0..3639 or -1 (incidence edge).
     matching index m = (p*5 + i)*2 + (shift-1): edge (p,i) - (M(p), i+shift), p in 0..363 point, i level.
   Usage: freegreedy BASE.txt START.txt PASSES SEED OUT.txt   (START: indices already freed, may be empty) */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#define NV 3640
static int nE, EU[11000], EV[11000], ET[11000];
static char freed[3640];
static uint64_t rng_s;
static inline uint64_t rnd(void) { rng_s ^= rng_s << 13; rng_s ^= rng_s >> 7; rng_s ^= rng_s << 17; return rng_s; }
static int st[NV + 1], adjv[2 * 11000], pos[NV], deg[NV];
static uint64_t vis[NV], fr[NV], nx[NV];
static int diameter(void) {   /* -1 if disconnected; else the exact diameter (stops early above 7) */
    for (int v = 0; v < NV; v++) deg[v] = 0;
    for (int e = 0; e < nE; e++) if (ET[e] < 0 || !freed[ET[e]]) { deg[EU[e]]++; deg[EV[e]]++; }
    st[0] = 0; for (int v = 0; v < NV; v++) st[v + 1] = st[v] + deg[v];
    for (int v = 0; v < NV; v++) pos[v] = 0;
    for (int e = 0; e < nE; e++) if (ET[e] < 0 || !freed[ET[e]]) { adjv[st[EU[e]] + pos[EU[e]]++] = EV[e]; adjv[st[EV[e]] + pos[EV[e]]++] = EU[e]; }
    int diam = 0;
    for (int s0 = 0; s0 < NV; s0 += 64) {
        int ns = (NV - s0 < 64) ? NV - s0 : 64; uint64_t full = ns == 64 ? ~0ULL : ((1ULL << ns) - 1);
        memset(vis, 0, sizeof vis); memset(fr, 0, sizeof fr);
        for (int k = 0; k < ns; k++) { vis[s0 + k] |= 1ULL << k; fr[s0 + k] |= 1ULL << k; }
        int lev = 0;
        for (;;) {
            int any = 0;
            for (int x = 0; x < NV; x++) { uint64_t acc = 0; for (int i = st[x]; i < st[x + 1]; i++) acc |= fr[adjv[i]]; acc &= ~vis[x]; nx[x] = acc; if (acc) any = 1; }
            if (!any) break;
            lev++;
            for (int x = 0; x < NV; x++) { vis[x] |= nx[x]; fr[x] = nx[x]; }
            if (lev > 7) return 8;   /* more than 7 levels: diameter > 7 (or disconnected, checked below) */
        }
        for (int x = 0; x < NV; x++) if (vis[x] != full) return -1;
        if (lev > diam) diam = lev;
    }
    return diam;
}
int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: freegreedy BASE.txt START.txt PASSES SEED OUT.txt\n"); return 2; }
    FILE *f = fopen(argv[1], "r"); long n; if (!f || fscanf(f, "%ld", &n) != 1) return 1;
    nE = 0; int a, b, t; while (fscanf(f, "%d %d %d", &a, &b, &t) == 3) { EU[nE] = a; EV[nE] = b; ET[nE] = t; nE++; }
    fclose(f);
    FILE *g = fopen(argv[2], "r"); int nf = 0; if (g) { int x; while (fscanf(g, "%d", &x) == 1) { if (x >= 0 && x < 3640 && !freed[x]) { freed[x] = 1; nf++; } } fclose(g); }
    rng_s = 88172645463325252ULL ^ ((uint64_t)atol(argv[4]) * 2654435761ULL + 99991);
    int d0 = diameter(); fprintf(stderr, "base edges %d, start freed %d, start diameter %d\n", nE, nf, d0);
    if (d0 < 0 || d0 > 7) { fprintf(stderr, "start graph invalid\n"); return 1; }
    int passes = atoi(argv[3]);
    for (int pass = 0; pass < passes; pass++) {
        int added = 0; static int order[3640]; for (int m = 0; m < 3640; m++) order[m] = m;
        for (int k = 3639; k > 0; k--) { int r = rnd() % (k + 1); int tt = order[k]; order[k] = order[r]; order[r] = tt; }
        for (int k = 0; k < 3640; k++) { int m = order[k]; if (freed[m]) continue; freed[m] = 1;
            int d = diameter(); if (d >= 0 && d <= 7) added++; else freed[m] = 0; }
        int tot = 0; for (int m = 0; m < 3640; m++) tot += freed[m];
        fprintf(stderr, "pass %d added %d total freed %d\n", pass, added, tot);
        if (!added) break;
    }
    FILE *o = fopen(argv[5], "w"); int tot = 0; for (int m = 0; m < 3640; m++) if (freed[m]) { fprintf(o, "%d\n", m); tot++; } fclose(o);
    printf("freed matching edges %d\n", tot);
    return 0;
}
