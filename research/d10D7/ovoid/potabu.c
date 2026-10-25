/* potabu.c: largest set of pairwise opposite points of H(q), any q (hex bin from hexgen2).
   Conflict: hexagon point distance <= 4 (collinear, or collinear with a common point).
   k-fixed swap tabu (min conflicts), K grows whenever the set is conflict-free; restarts from the best set
   with a random perturbation when stalled.
   usage: potabu HEXBIN SEED SECONDS OUT [INIT] */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
static int q, N, *LP, *PL, *NB, DEG, *C, *INS, *S, *POS, K, F, *TT, *best, bestK;
static uint64_t rs;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static void add(int v) { INS[v] = 1; POS[v] = K; S[K++] = v; F += C[v]; for (int i = 0; i < DEG; i++) C[NB[(long)v * DEG + i]]++; }
static void rem(int v) { INS[v] = 0; int p = POS[v]; S[p] = S[--K]; POS[S[p]] = p; for (int i = 0; i < DEG; i++) C[NB[(long)v * DEG + i]]--; F -= C[v]; }
int main(int argc, char **argv) {
    FILE *f = fopen(argv[1], "rb"); int hd[3]; fread(hd, 4, 3, f); q = hd[0]; N = hd[1];
    LP = malloc(sizeof(int) * N * (q + 1)); fread(LP, 4, (long)N * (q + 1), f); fclose(f);
    PL = malloc(sizeof(int) * N * (q + 1)); int *pc = calloc(N, sizeof(int));
    for (int l = 0; l < N; l++) for (int j = 0; j <= q; j++) { int p = LP[l * (q + 1) + j]; PL[p * (q + 1) + pc[p]++] = l; }
    DEG = q * (q + 1) * (1 + q * q); NB = malloc(sizeof(int) * (long)N * DEG);
    int *mark = calloc(N, sizeof(int)), stamp = 0;
    for (int p = 0; p < N; p++) { stamp++; mark[p] = stamp; int d = 0; int lev1[2048]; int n1 = 0;
        for (int a = 0; a <= q; a++) { int l = PL[p * (q + 1) + a]; for (int b = 0; b <= q; b++) { int x = LP[l * (q + 1) + b]; if (mark[x] != stamp) { mark[x] = stamp; NB[(long)p * DEG + d++] = x; lev1[n1++] = x; } } }
        for (int i = 0; i < n1; i++) { int x = lev1[i]; for (int a = 0; a <= q; a++) { int l = PL[x * (q + 1) + a]; for (int b = 0; b <= q; b++) { int y = LP[l * (q + 1) + b]; if (mark[y] != stamp) { mark[y] = stamp; NB[(long)p * DEG + d++] = y; } } } }
        if (d != DEG) { fprintf(stderr, "deg %d != %d at %d\n", d, DEG, p); return 1; } }
    rs = 0x9E3779B97F4A7C15ULL ^ (uint64_t)atoi(argv[2]) * 0x2545F4914F6CDD1DULL; for (int i = 0; i < 10; i++) rnd();
    double T = atof(argv[3]); C = calloc(N, sizeof(int)); INS = calloc(N, sizeof(int)); S = malloc(sizeof(int) * N); POS = malloc(sizeof(int) * N);
    TT = calloc(N, sizeof(int)); best = malloc(sizeof(int) * N); bestK = 0; K = 0; F = 0;
    if (argc > 5) { FILE *g = fopen(argv[5], "r"); int v; while (fscanf(g, "%d", &v) == 1) add(v); fclose(g); }
    /* greedy fill */
    for (;;) { int bv = -1, nc = 0; for (int v = 0; v < N; v++) if (!INS[v] && C[v] == 0) { nc++; if (rnd() % nc == 0) bv = v; } if (bv < 0) break; add(bv); }
    if (F == 0) { bestK = K; memcpy(best, S, sizeof(int) * K); }
    clock_t t0 = clock(); long it = 0, lastimp = 0; int *cand = malloc(sizeof(int) * N);
    while ((double)(clock() - t0) / CLOCKS_PER_SEC < T) {
        it++;
        if (F == 0) { if (K > bestK) { bestK = K; memcpy(best, S, sizeof(int) * K); FILE *o = fopen(argv[4], "w"); for (int i = 0; i < K; i++) fprintf(o, "%d\n", S[i]); fclose(o);
                fprintf(stderr, "K=%d it=%ld t=%.1fs\n", K, it, (double)(clock() - t0) / CLOCKS_PER_SEC); }
            lastimp = it; int bv = -1, bc = 1 << 30, nc = 0; for (int v = 0; v < N; v++) if (!INS[v]) { if (C[v] < bc) { bc = C[v]; bv = v; nc = 1; } else if (C[v] == bc && rnd() % (++nc) == 0) bv = v; }
            add(bv); continue; }
        if (it - lastimp > 200000) { /* perturb from best */ while (K) rem(S[K - 1]); for (int i = 0; i < bestK; i++) add(best[i]);
            int r = 2 + rnd() % 6; for (int j = 0; j < r && K; j++) rem(S[rnd() % K]);
            for (int j = 0; j < r + 1; j++) { int bv = -1, bc = 1 << 30, nc = 0; for (int v = 0; v < N; v++) if (!INS[v]) { if (C[v] < bc) { bc = C[v]; bv = v; nc = 1; } else if (C[v] == bc && rnd() % (++nc) == 0) bv = v; } add(bv); }
            lastimp = it; continue; }
        /* pick u in S with max conflicts (non-tabu), v outside with min conflicts after removing u */
        int bu = -1, bcu = -1, nc = 0; for (int i = 0; i < K; i++) { int u = S[i]; if (C[u] == 0 || TT[u] > it) continue; if (C[u] > bcu) { bcu = C[u]; bu = u; nc = 1; } else if (C[u] == bcu && rnd() % (++nc) == 0) bu = u; }
        if (bu < 0) bu = S[rnd() % K];
        rem(bu); TT[bu] = it + 7 + rnd() % 10;
        int bv = -1, bc = 1 << 30; nc = 0; for (int v = 0; v < N; v++) if (!INS[v] && v != bu && TT[v] <= it) { if (C[v] < bc) { bc = C[v]; bv = v; nc = 1; } else if (C[v] == bc && rnd() % (++nc) == 0) bv = v; }
        if (bv < 0) bv = bu; add(bv); TT[bv] = it + 3 + rnd() % 5;
    }
    printf("q=%d best %d\n", q, bestK); return 0;
}
