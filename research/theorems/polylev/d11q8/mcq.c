/* mcq.c: exact maximum independent set of a small graph (CSR files PREFIX_n.bin, PREFIX_off.bin, PREFIX_nb.bin), as a
   maximum clique of the complement, by branch and bound with greedy colouring bounds (Tomita-Seki MCQ).
   polylev job (Opus), 2026-10-28. Used on orbit quotients of the collinearity graph of H(8) (an independent set of
   orbits = pairwise non-collinear points).
   Usage: mcq PREFIX SECONDS [LOWER]   prints the best independent set size found and whether the search finished. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>

#define MAXW 64
static int n, W; static uint64_t *cadj;   /* complement adjacency bitsets */
static int best = 0, *bestset, *cur, curn = 0; static long nodes = 0; static double t0, lim; static int timeout = 0;
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }

static void expand(uint64_t *P) {
    if (timeout) return;
    if ((++nodes & 1023) == 0 && now() - t0 > lim) { timeout = 1; return; }
    /* greedy colouring of P: order and colour bounds */
    int order[4096], col[4096], cnt = 0;
    uint64_t U[MAXW], Q[MAXW]; memcpy(U, P, W * 8);
    int c = 0;
    while (1) {
        int any = 0; for (int w = 0; w < W; w++) if (U[w]) { any = 1; break; }
        if (!any) break;
        c++; memcpy(Q, U, W * 8);
        for (int w = 0; w < W; w++) while (Q[w]) {
            int v = w * 64 + __builtin_ctzll(Q[w]);
            U[w] &= ~(1ULL << (v & 63));
            for (int x = 0; x < W; x++) Q[x] &= ~cadj[(size_t)v * W + x];
            Q[w] &= ~(1ULL << (v & 63));
            order[cnt] = v; col[cnt] = c; cnt++;
        }
    }
    for (int i = cnt - 1; i >= 0; i--) {
        if (curn + col[i] <= best) return;
        int v = order[i];
        cur[curn++] = v;
        uint64_t NP[MAXW]; int any = 0;
        for (int w = 0; w < W; w++) { NP[w] = P[w] & cadj[(size_t)v * W + w]; if (NP[w]) any = 1; }
        if (!any) { if (curn > best) { best = curn; memcpy(bestset, cur, sizeof(int) * curn); fprintf(stderr, "best %d (%.0fs, %ld nodes)\n", best, now() - t0, nodes); } }
        else expand(NP);
        curn--;
        P[v >> 6] &= ~(1ULL << (v & 63));
        if (timeout) return;
    }
}

int main(int argc, char **argv) {
    char fn[512]; FILE *f; int32_t nn;
    snprintf(fn, sizeof fn, "%s_n.bin", argv[1]); f = fopen(fn, "rb"); if (!f || fread(&nn, 4, 1, f) != 1) return 1; fclose(f); n = nn;
    int32_t *off = malloc(4 * (n + 1)); snprintf(fn, sizeof fn, "%s_off.bin", argv[1]); f = fopen(fn, "rb"); if (fread(off, 4, n + 1, f) != (size_t)n + 1) return 1; fclose(f);
    int32_t *nb = malloc(4 * (size_t)off[n]); snprintf(fn, sizeof fn, "%s_nb.bin", argv[1]); f = fopen(fn, "rb"); if (fread(nb, 4, off[n], f) != (size_t)off[n]) return 1; fclose(f);
    W = (n + 63) / 64; if (W > MAXW || n > 4096) { fprintf(stderr, "too big\n"); return 1; }
    lim = atof(argv[2]); best = argc > 3 ? atoi(argv[3]) - 1 : 0;
    cadj = calloc((size_t)n * W, 8);
    for (int v = 0; v < n; v++) { for (int u = 0; u < n; u++) if (u != v) cadj[(size_t)v * W + (u >> 6)] |= 1ULL << (u & 63);
        for (int j = off[v]; j < off[v + 1]; j++) { int u = nb[j]; cadj[(size_t)v * W + (u >> 6)] &= ~(1ULL << (u & 63)); } }
    bestset = malloc(sizeof(int) * n); cur = malloc(sizeof(int) * n);
    uint64_t P[MAXW] = {0}; for (int v = 0; v < n; v++) P[v >> 6] |= 1ULL << (v & 63);
    t0 = now(); expand(P);
    printf("n=%d edges=%d: best independent set %d; search %s (%ld nodes, %.0fs)\n", n, off[n] / 2, best, timeout ? "STOPPED (time limit), not a proof" : "COMPLETE (exact)", nodes, now() - t0);
    if (argc > 4) { f = fopen(argv[4], "w"); for (int i = 0; i < best; i++) fprintf(f, "%d\n", bestset[i]); fclose(f); }
    return 0;
}
