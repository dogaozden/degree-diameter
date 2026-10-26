/* tabulift: tabu search over voltage lifts of cubic bipartite p+p bases (base edges and voltages both move).
   Usage: tabulift p GROUPS id seed seconds [K] [tenure] [START.sol] [out.sol]
   Each step samples K random moves (half voltage changes, half base edge switches with an optional new voltage),
   evaluates all of them exactly (same cost as salift: #(base vertex, lifted vertex) pairs at distance > 7, env D),
   and applies the best one whose touched edges are not tabu (a tabu move is allowed if it beats the best cost).
   Touched edges stay tabu for `tenure` steps.  Restarts from the best state after 2000 steps without progress.
   START.sol (optional, "-" for random): "N id p" then 3p lines "u v a" (salift / salift2 / requot.py format). */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
typedef unsigned __int128 u128;
static int p, k, N, D = 7, *mul, *inv, ne;
static int eu[512], ev[512], ea[512];
static u128 *R, *R2; static int *nbr;
static uint64_t rng = 88172645463325252ULL;
static inline uint64_t xr(void) { rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; return rng; }
static inline int pc(u128 x) { return __builtin_popcountll((uint64_t)x) + __builtin_popcountll((uint64_t)(x >> 64)); }
static long cost(void) {
    for (int e = 0; e < ne; e++) for (int f = e + 1; f < ne; f++)
        if (eu[e] == eu[f] && ev[e] == ev[f] && ea[e] == ea[f]) return 1L << 40;
    int n = k * N; static int dg[128], dv[128][3], da[128][3];
    memset(dg, 0, sizeof dg);
    for (int e = 0; e < ne; e++) { int u = eu[e], v = ev[e];
        dv[u][dg[u]] = v; da[u][dg[u]++] = ea[e]; dv[v][dg[v]] = u; da[v][dg[v]++] = inv[ea[e]]; }
    for (int u = 0; u < k; u++) for (int g = 0; g < N; g++) for (int j = 0; j < 3; j++)
        nbr[(u * N + g) * 3 + j] = dv[u][j] * N + mul[g * N + da[u][j]];
    memset(R, 0, sizeof(u128) * n);
    for (int u = 0; u < k; u++) R[u * N] = (u128)1 << u;
    for (int t = 0; t < D; t++) {
        for (int x = 0; x < n; x++) R2[x] = R[x] | R[nbr[3 * x]] | R[nbr[3 * x + 1]] | R[nbr[3 * x + 2]];
        u128 *tmp = R; R = R2; R2 = tmp;
    }
    u128 full = k == 128 ? ~(u128)0 : (((u128)1 << k) - 1); long c = 0;
    for (int x = 0; x < n; x++) c += pc(~R[x] & full);
    return c;
}
int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: tabulift p GROUPS id seed seconds [K] [tenure] [START.sol] [out.sol]\n"); return 2; }
    p = atoi(argv[1]); k = 2 * p; int want = atoi(argv[3]);
    rng ^= (uint64_t)atoll(argv[4]) * 0x9E3779B97F4A7C15ULL; xr(); xr();
    double secs = atof(argv[5]); int K = argc > 6 ? atoi(argv[6]) : 100, ten = argc > 7 ? atoi(argv[7]) : 10;
    const char *start = argc > 8 ? argv[8] : "-", *out = argc > 9 ? argv[9] : "best.sol";
    if (getenv("D")) D = atoi(getenv("D"));
    FILE *fg = fopen(argv[2], "r"); char tag[8], name[256]; int gid, found = 0;
    while (fscanf(fg, "%7s %d %d %255s", tag, &N, &gid, name) == 4) {
        mul = malloc(sizeof(int) * N * N);
        for (int i = 0; i < N * N; i++) if (fscanf(fg, "%d", &mul[i]) != 1) return 3;
        if (gid == want) { found = 1; break; } free(mul);
    }
    if (!found) { fprintf(stderr, "group not found\n"); return 2; }
    inv = malloc(sizeof(int) * N);
    for (int a = 0; a < N; a++) for (int b = 0; b < N; b++) if (mul[a * N + b] == 0) inv[a] = b;
    int n = k * N; R = malloc(sizeof(u128) * n); R2 = malloc(sizeof(u128) * n); nbr = malloc(sizeof(int) * 3 * n);
    ne = 3 * p;
    if (strcmp(start, "-")) { FILE *fs = fopen(start, "r"); int sn, sid, sp; if (fscanf(fs, "%d %d %d", &sn, &sid, &sp) != 3 || sp != p || sn != N) { fprintf(stderr, "bad start\n"); return 2; }
        for (int e = 0; e < ne; e++) if (fscanf(fs, "%d %d %d", &eu[e], &ev[e], &ea[e]) != 3) return 2; fclose(fs); }
    else for (int m = 0, c = 0; m < 3; m++) { int pm[64]; for (int i = 0; i < p; i++) pm[i] = i;
        for (int i = p - 1; i > 0; i--) { int j = xr() % (i + 1); int t = pm[i]; pm[i] = pm[j]; pm[j] = t; }
        for (int i = 0; i < p; i++, c++) { eu[c] = i; ev[c] = p + pm[i]; ea[c] = xr() % N; } }
    static long tabu[512]; long step = 0, c = cost(), best = c, lastimp = 0;
    int bu[512], bv[512], ba[512]; memcpy(bv, ev, sizeof ev); memcpy(ba, ea, sizeof ea); memcpy(bu, eu, sizeof eu);
    printf("group N=%d %s p=%d n=%d start %ld\n", N, name, p, n, c); fflush(stdout);
    clock_t st = clock();
    while ((double)(clock() - st) / CLOCKS_PER_SEC < secs) {
        long bc = 1L << 50; int mi = -1, mj = -1, mt = 0, mva = 0, mvb = 0;
        for (int s = 0; s < K; s++) {
            int i = xr() % ne, j = xr() % ne, type = xr() & 1, va = xr() % N, vb = ea[j];
            int sv[4] = {ev[i], ea[i], ev[j], ea[j]};
            if (type == 0) { if (va == ea[i]) continue; ea[i] = va; }
            else { if (i == j || ev[i] == ev[j]) continue; int t = ev[i]; ev[i] = ev[j]; ev[j] = t; if (xr() & 1) ea[i] = va; else va = ea[i]; }
            long c2 = cost();
            int istabu = tabu[i] > step || (type && tabu[j] > step);
            if ((!istabu || c2 < best) && c2 < bc) { bc = c2; mi = i; mj = j; mt = type; mva = ea[i]; mvb = ea[j]; }
            ev[i] = sv[0]; ea[i] = sv[1]; ev[j] = sv[2]; ea[j] = sv[3];
            (void)vb;
        }
        step++;
        if (mi < 0) continue;
        if (mt == 0) ea[mi] = mva; else { int t = ev[mi]; ev[mi] = ev[mj]; ev[mj] = t; ea[mi] = mva; ea[mj] = mvb; tabu[mj] = step + ten; }
        tabu[mi] = step + ten; c = bc;
        if (c < best) { best = c; lastimp = step; memcpy(bv, ev, sizeof ev); memcpy(ba, ea, sizeof ea); memcpy(bu, eu, sizeof eu);
            printf("t=%.1f step=%ld best %ld\n", (double)(clock() - st) / CLOCKS_PER_SEC, step, best); fflush(stdout);
            if (best == 0) { FILE *f = fopen(out, "w"); fprintf(f, "%d %d %d\n", N, gid, p);
                for (int e = 0; e < ne; e++) fprintf(f, "%d %d %d\n", eu[e], ev[e], ea[e]); fclose(f); printf("FOUND\n"); break; } }
        if (step - lastimp > 2000) { memcpy(ev, bv, sizeof ev); memcpy(ea, ba, sizeof ea); memcpy(eu, bu, sizeof eu);
            for (int r = 0; r < 3; r++) ea[xr() % ne] = xr() % N; c = cost(); lastimp = step; memset(tabu, 0, sizeof tabu); }
    }
    printf("end best %ld steps %ld\n", best, step);
    return 0;
}
