/* salift4 (own-small r2 card q1): degree-4 version of tools/salift_s.c.
   Joint simulated annealing over voltage lifts of 4-regular bipartite multigraphs on p+p base vertices
   (base = 4 perfect matchings, multi-edges allowed), base AND voltages free.
   Usage: salift4 p GROUPS id seed seconds [T0] [T1] [out.sol]
     GROUPS: text file of gap_export blocks ("G N id name" + N rows, row a col b = index of el[a]*el[b], identity 0);
     must contain order-N blocks; id = SmallGroup id inside it.
   Env: D (default 8), CYC (cooling cycle in CPU s, default 30), START=file.best (N id p cost + 4p lines "u v a").
   Lift: vertex (u,g) = u*N+g, whites u < p, blacks u >= p, base edge (u,v,a) gives (u,g) ~ (v, g*a); n = 2pN.
   Cost = #(base vertex u, lift vertex x) with dist((u,e),x) > D (same as salift_s / flift eval after v -> v^-1).
   Parallel base edges must carry different voltages (cost 1<<40 otherwise).
   Moves: 50% change one voltage; 50% switch the black ends of two base edges (keeps 4-regularity).
   Writes OUT.best whenever the best improves; OUT (N id p, 4p lines "u v a") at cost 0 and stops. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>

static int p, k, N, D = 8, *mul, *inv, ne;
static int eu[128], ev[128], ea[128];
static uint64_t *R, *R2; static int *nbr;
static uint64_t rng = 88172645463325252ULL;
static inline uint64_t xr(void) { rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; return rng; }
static inline double ur(void) { return (xr() >> 11) * (1.0 / 9007199254740992.0); }

static long cost(void) {
    for (int e = 0; e < ne; e++) for (int f = e + 1; f < ne; f++)
        if (eu[e] == eu[f] && ev[e] == ev[f] && ea[e] == ea[f]) return 1L << 40;
    int n = k * N, dg[64] = {0};
    static int dv[64][4], da[64][4];
    for (int e = 0; e < ne; e++) { int u = eu[e], v = ev[e];
        dv[u][dg[u]] = v; da[u][dg[u]++] = ea[e]; dv[v][dg[v]] = u; da[v][dg[v]++] = inv[ea[e]]; }
    for (int u = 0; u < k; u++) for (int g = 0; g < N; g++) for (int j = 0; j < 4; j++)
        nbr[(u * N + g) * 4 + j] = dv[u][j] * N + mul[g * N + da[u][j]];
    memset(R, 0, 8L * n);
    for (int u = 0; u < k; u++) R[u * N] = 1ULL << u;
    for (int t = 0; t < D; t++) {
        for (int x = 0; x < n; x++) { int *q = nbr + 4 * x;
            R2[x] = R[x] | R[q[0]] | R[q[1]] | R[q[2]] | R[q[3]]; }
        uint64_t *tmp = R; R = R2; R2 = tmp;
    }
    uint64_t full = (1ULL << k) - 1; long c = 0;
    for (int x = 0; x < n; x++) c += __builtin_popcountll(~R[x] & full);
    return c;
}

int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: salift4 p GROUPS id seed seconds [T0] [T1] [out.sol]\n"); return 2; }
    p = atoi(argv[1]); k = 2 * p; int want = atoi(argv[3]);
    rng ^= (uint64_t)atoll(argv[4]) * 0x9E3779B97F4A7C15ULL; xr(); xr();
    double secs = atof(argv[5]), T0 = argc > 6 ? atof(argv[6]) : 10.0, T1 = argc > 7 ? atof(argv[7]) : 0.3;
    const char *out = argc > 8 ? argv[8] : "best.sol";
    double cyc = getenv("CYC") ? atof(getenv("CYC")) : 30.0;
    if (getenv("D")) D = atoi(getenv("D"));
    FILE *fg = fopen(argv[2], "r"); char tag[8], name[256]; int gid, found = 0;
    while (fscanf(fg, "%7s %d %d %255s", tag, &N, &gid, name) == 4) {
        mul = malloc(sizeof(int) * N * N);
        for (int i = 0; i < N * N; i++) if (fscanf(fg, "%d", &mul[i]) != 1) return 3;
        if (gid == want) { found = 1; break; }
        free(mul);
    }
    if (!found) { fprintf(stderr, "group not found\n"); return 2; }
    inv = malloc(sizeof(int) * N);
    for (int a = 0; a < N; a++) for (int b = 0; b < N; b++) if (mul[a * N + b] == 0) inv[a] = b;
    int n = k * N; R = malloc(8L * n); R2 = malloc(8L * n); nbr = malloc(sizeof(int) * 4 * n);
    /* random base: four random perfect matchings white -> black, random voltages */
    ne = 0;
    for (int m = 0; m < 4; m++) { int pm[32]; for (int i = 0; i < p; i++) pm[i] = i;
        for (int i = p - 1; i > 0; i--) { int j = xr() % (i + 1); int t = pm[i]; pm[i] = pm[j]; pm[j] = t; }
        for (int i = 0; i < p; i++) { eu[ne] = i; ev[ne] = p + pm[i]; ea[ne] = xr() % N; ne++; } }
    if (getenv("START")) { FILE *fs = fopen(getenv("START"), "r"); int sN, sg, sp; long sc;
        if (!fs || fscanf(fs, "%d %d %d %ld", &sN, &sg, &sp, &sc) != 4 || sN != N || sp != p) { fprintf(stderr, "bad START\n"); return 2; }
        for (int e = 0; e < ne; e++) if (fscanf(fs, "%d %d %d", &eu[e], &ev[e], &ea[e]) != 3) { fprintf(stderr, "bad START\n"); return 2; }
        fclose(fs); }
    long c = cost(), best = c; clock_t st = clock(); long it = 0;
    printf("group N=%d id=%d %s p=%d n=%d D=%d start %ld\n", N, gid, name, p, n, D, c); fflush(stdout);
    for (;;) {
        double el = (double)(clock() - st) / CLOCKS_PER_SEC; if (el > secs) break;
        double T = T0 * pow(T1 / T0, fmod(el, cyc) / cyc);
        int i = xr() % ne, j = xr() % ne, sv[4] = {ev[i], ea[i], ev[j], ea[j]};
        if (xr() & 1) { ea[i] = xr() % N; }
        else { if (i == j || ev[i] == ev[j]) continue; int t = ev[i]; ev[i] = ev[j]; ev[j] = t; if (xr() & 1) ea[i] = xr() % N; }
        long c2 = cost(); it++;
        if (c2 <= c || ur() < exp((c - c2) / T)) {
            c = c2;
            if (c < best) { best = c; printf("t=%.1f it=%ld best %ld\n", el, it, best); fflush(stdout);
                { char bp[600]; snprintf(bp, sizeof bp, "%s.best", out); FILE *fb = fopen(bp, "w"); fprintf(fb, "%d %d %d %ld\n", N, gid, p, best);
                  for (int e = 0; e < ne; e++) fprintf(fb, "%d %d %d\n", eu[e], ev[e], ea[e]); fclose(fb); }
                if (best == 0) { FILE *f = fopen(out, "w"); fprintf(f, "%d %d %d\n", N, gid, p);
                    for (int e = 0; e < ne; e++) fprintf(f, "%d %d %d\n", eu[e], ev[e], ea[e]); fclose(f); printf("FOUND\n"); break; } }
        } else { ev[i] = sv[0]; ea[i] = sv[1]; ev[j] = sv[2]; ea[j] = sv[3]; }
    }
    printf("end best %ld its %ld\n", best, it);
    return 0;
}
