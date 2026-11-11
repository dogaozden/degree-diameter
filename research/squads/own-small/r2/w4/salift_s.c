/* salift_s: salift that also accepts env START=file.best (a previous OUT.best) as the start state, and writes OUT.best (same format as the cost-0 .sol, header "N id p cost") whenever
   the best cost improves (own-small job).
   salift: simulated annealing over voltage lifts of cubic bipartite p+p base multigraphs, base AND voltages free.
   Usage: salift p GROUPS id seed seconds [T0] [T1] [out.sol]
     GROUPS id : multiplication table file from gap_export.g and the SmallGroup id inside it (order N)
   Lift: vertex (u,g) = u*N+g (whites u < p, blacks u >= p), base edge (u,v,a) gives (u,g) ~ (v, g*a); n = 2pN.
   Left multiplication is a semiregular automorphism group, so a 2p-source BFS gives the exact cost:
   cost = #(base vertex u, lifted vertex x) with dist((u,1), x) > D (D = 7, env D overrides). Parallel base edges
   must carry different voltages (the lift is then simple).
   Moves: 50% change one voltage; 50% switch two base edges (u1 v1 a1, u2 v2 a2) -> (u1 v2 a1, u2 v1 a2).
   On cost 0 writes out.sol: "N id p" then the 3p lines "u v a"; liftedges.py turns it into an edge list. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>

static int p, k, N, D = 7, *mul, *inv, ne;
static int eu[96], ev[96], ea[96];
static uint64_t *R, *R2; static int *nbr;
static uint64_t rng = 88172645463325252ULL;
static inline uint64_t xr(void) { rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; return rng; }
static inline double ur(void) { return (xr() >> 11) * (1.0 / 9007199254740992.0); }

static long cost(void) {
    for (int e = 0; e < ne; e++) for (int f = e + 1; f < ne; f++)
        if (eu[e] == eu[f] && ev[e] == ev[f] && ea[e] == ea[f]) return 1L << 40;
    int n = k * N, dg[64] = {0};
    static int dv[64][3], da[64][3];
    for (int e = 0; e < ne; e++) { int u = eu[e], v = ev[e];
        dv[u][dg[u]] = v; da[u][dg[u]++] = ea[e]; dv[v][dg[v]] = u; da[v][dg[v]++] = inv[ea[e]]; }
    for (int u = 0; u < k; u++) for (int g = 0; g < N; g++) for (int j = 0; j < 3; j++)
        nbr[(u * N + g) * 3 + j] = dv[u][j] * N + mul[g * N + da[u][j]];
    memset(R, 0, 8L * n);
    for (int u = 0; u < k; u++) R[u * N] = 1ULL << u;
    for (int t = 0; t < D; t++) {
        for (int x = 0; x < n; x++) R2[x] = R[x] | R[nbr[3 * x]] | R[nbr[3 * x + 1]] | R[nbr[3 * x + 2]];
        uint64_t *tmp = R; R = R2; R2 = tmp;
    }
    uint64_t full = k == 64 ? ~0ULL : (1ULL << k) - 1; long c = 0;
    for (int x = 0; x < n; x++) c += __builtin_popcountll(~R[x] & full);
    return c;
}

int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: salift p GROUPS id seed seconds [T0] [T1] [out.sol]\n"); return 2; }
    p = atoi(argv[1]); k = 2 * p; int want = atoi(argv[3]);
    rng ^= (uint64_t)atoll(argv[4]) * 0x9E3779B97F4A7C15ULL; xr(); xr();
    double secs = atof(argv[5]), T0 = argc > 6 ? atof(argv[6]) : 10.0, T1 = argc > 7 ? atof(argv[7]) : 0.3;
    const char *out = argc > 8 ? argv[8] : "best.sol";
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
    int n = k * N; R = malloc(8L * n); R2 = malloc(8L * n); nbr = malloc(sizeof(int) * 3 * n);
    /* random base: three random perfect matchings white -> black, random voltages */
    ne = 0;
    for (int m = 0; m < 3; m++) { int pm[32]; for (int i = 0; i < p; i++) pm[i] = i;
        for (int i = p - 1; i > 0; i--) { int j = xr() % (i + 1); int t = pm[i]; pm[i] = pm[j]; pm[j] = t; }
        for (int i = 0; i < p; i++) { eu[ne] = i; ev[ne] = p + pm[i]; ea[ne] = xr() % N; ne++; } }
    if (getenv("START")) { FILE *fs = fopen(getenv("START"), "r"); int sN, sg, sp; long sc;
        if (!fs || fscanf(fs, "%d %d %d %ld", &sN, &sg, &sp, &sc) != 4 || sN != N || sp != p) { fprintf(stderr, "bad START\n"); return 2; }
        for (int e = 0; e < ne; e++) if (fscanf(fs, "%d %d %d", &eu[e], &ev[e], &ea[e]) != 3) { fprintf(stderr, "bad START\n"); return 2; }
        fclose(fs); }
    long c = cost(), best = c; clock_t st = clock(); double cyc = 30.0; long it = 0;
    printf("group N=%d id=%d %s p=%d n=%d start %ld\n", N, gid, name, p, n, c); fflush(stdout);
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
