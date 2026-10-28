/* wmis.c: exact maximum-weight independent set of a small graph by branch and bound (weighted clique in the
   complement; bound = sum over greedy colour classes of the largest weight in the class).
   polylev job (Opus), 2026-10-28.
   Input file: n, then n weights, then m, then m edges "u v".  Usage: wmis FILE SECONDS [OUT]  */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>

#define MAXW 16
static int n, W; static uint64_t cadj[1024][MAXW]; static long wt[1024];
static long best = 0; static int bestset[1024], bestn = 0, cur[1024], curn = 0; static long curw = 0;
static long nodes = 0; static double t0, lim; static int stop = 0;
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }

static void expand(uint64_t *P) {
    if (stop) return;
    if ((++nodes & 4095) == 0 && now() - t0 > lim) { stop = 1; return; }
    int order[1024], cnt = 0; long bnd[1024];
    uint64_t U[MAXW], Q[MAXW]; memcpy(U, P, sizeof(uint64_t) * W);
    long acc = 0;
    while (1) {
        int any = 0; for (int w = 0; w < W; w++) if (U[w]) any = 1;
        if (!any) break;
        memcpy(Q, U, sizeof(uint64_t) * W); long mx = 0; int start = cnt;
        for (int w = 0; w < W; w++) while (Q[w]) {
            int v = w * 64 + __builtin_ctzll(Q[w]);
            Q[w] &= ~(1ULL << (v & 63)); U[w] &= ~(1ULL << (v & 63));
            for (int x = 0; x < W; x++) Q[x] &= ~cadj[v][x];
            order[cnt++] = v; if (wt[v] > mx) mx = wt[v];
        }
        acc += mx;
        for (int i = start; i < cnt; i++) bnd[i] = acc;
    }
    for (int i = cnt - 1; i >= 0; i--) {
        if (curw + bnd[i] <= best) return;
        int v = order[i];
        cur[curn++] = v; curw += wt[v];
        uint64_t NP[MAXW]; int any = 0;
        for (int w = 0; w < W; w++) { NP[w] = P[w] & cadj[v][w]; if (NP[w]) any = 1; }
        if (curw > best) { best = curw; bestn = curn; memcpy(bestset, cur, sizeof(int) * curn); fprintf(stderr, "best %ld (%d vertices, %.0fs)\n", best, curn, now() - t0); }
        if (any) expand(NP);
        curn--; curw -= wt[v];
        P[v >> 6] &= ~(1ULL << (v & 63));
        if (stop) return;
    }
}

int main(int argc, char **argv) {
    FILE *f = fopen(argv[1], "r"); if (!f || fscanf(f, "%d", &n) != 1 || n > 1024) return 1;
    for (int i = 0; i < n; i++) if (fscanf(f, "%ld", &wt[i]) != 1) return 1;
    int m; if (fscanf(f, "%d", &m) != 1) return 1;
    W = (n + 63) / 64;
    for (int v = 0; v < n; v++) for (int u = 0; u < n; u++) if (u != v) cadj[v][u >> 6] |= 1ULL << (u & 63);
    for (int e = 0; e < m; e++) { int a, b; if (fscanf(f, "%d %d", &a, &b) != 2) return 1; cadj[a][b >> 6] &= ~(1ULL << (b & 63)); cadj[b][a >> 6] &= ~(1ULL << (a & 63)); }
    fclose(f);
    lim = atof(argv[2]);
    uint64_t P[MAXW] = {0}; for (int v = 0; v < n; v++) P[v >> 6] |= 1ULL << (v & 63);
    t0 = now(); expand(P);
    printf("n=%d m=%d: maximum weight %ld (%d vertices); search %s (%ld nodes, %.0fs)\n", n, m, best, bestn,
           stop ? "STOPPED at the time limit (not a proof)" : "COMPLETE (exact)", nodes, now() - t0);
    if (argc > 3) { f = fopen(argv[3], "w"); for (int i = 0; i < bestn; i++) fprintf(f, "%d\n", bestset[i]); fclose(f); }
    return 0;
}
