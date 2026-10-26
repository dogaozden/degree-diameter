/* salift2 (c4): salift started from a given base+voltage file (the quotient of the 168 lift by H, plus a gadget).
   Usage: salift2 START.sol GROUPS id seed seconds [T0] [T1] [out.sol]
   START.sol: "N id p" then 3p lines "u v a" (white u < p, black v >= p, voltage a in the group table GROUPS id).
   Same cost and moves as salift (cost = #(base vertex, lifted vertex) pairs at distance > 7); bitsets are 128-bit,
   so up to 128 base vertices. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>

typedef unsigned __int128 u128;
static int p, k, N, D = 7, *mul, *inv, ne;
static int eu[512], ev[512], ea[512];
static u128 *R, *R2; static int *nbr;
static uint64_t rng = 88172645463325252ULL;
static inline uint64_t xr(void) { rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; return rng; }
static inline double ur(void) { return (xr() >> 11) * (1.0 / 9007199254740992.0); }
static inline int pc(u128 x) { return __builtin_popcountll((uint64_t)x) + __builtin_popcountll((uint64_t)(x >> 64)); }

static long cost(void) {
    for (int e = 0; e < ne; e++) for (int f = e + 1; f < ne; f++)
        if (eu[e] == eu[f] && ev[e] == ev[f] && ea[e] == ea[f]) return 1L << 40;
    int n = k * N, dg[128] = {0};
    static int dv[128][3], da[128][3];
    for (int e = 0; e < ne; e++) { int u = eu[e], v = ev[e];
        if (dg[u] >= 3 || dg[v] >= 3) return 1L << 40;
        dv[u][dg[u]] = v; da[u][dg[u]++] = ea[e]; dv[v][dg[v]] = u; da[v][dg[v]++] = inv[ea[e]]; }
    for (int u = 0; u < k; u++) if (dg[u] != 3) return 1L << 40;
    for (int u = 0; u < k; u++) for (int g = 0; g < N; g++) for (int j = 0; j < 3; j++)
        nbr[(u * N + g) * 3 + j] = dv[u][j] * N + mul[g * N + da[u][j]];
    memset(R, 0, sizeof(u128) * n);
    for (int u = 0; u < k; u++) R[u * N] = (u128)1 << u;
    for (int t = 0; t < D; t++) {
        for (int x = 0; x < n; x++) R2[x] = R[x] | R[nbr[3 * x]] | R[nbr[3 * x + 1]] | R[nbr[3 * x + 2]];
        u128 *tmp = R; R = R2; R2 = tmp;
    }
    u128 full = k == 128 ? ~(u128)0 : (((u128)1) << k) - 1; long c = 0;
    for (int x = 0; x < n; x++) c += pc(~R[x] & full);
    return c;
}

int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: salift2 START.sol GROUPS id seed seconds [T0] [T1] [out.sol]\n"); return 2; }
    int want = atoi(argv[3]);
    rng ^= (uint64_t)atoll(argv[4]) * 0x9E3779B97F4A7C15ULL; xr(); xr();
    double secs = atof(argv[5]), T0 = argc > 6 ? atof(argv[6]) : 10.0, T1 = argc > 7 ? atof(argv[7]) : 0.3;
    const char *out = argc > 8 ? argv[8] : "best.sol";
    if (getenv("D")) D = atoi(getenv("D"));
    FILE *fs = fopen(argv[1], "r"); int sid, sp;
    if (fscanf(fs, "%d %d %d", &N, &sid, &sp) != 3) return 3;
    p = sp; k = 2 * p; ne = 0;
    while (fscanf(fs, "%d %d %d", &eu[ne], &ev[ne], &ea[ne]) == 3) ne++;
    fclose(fs);
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
    int n = k * N; R = malloc(sizeof(u128) * n); R2 = malloc(sizeof(u128) * n); nbr = malloc(sizeof(int) * 3 * n);
    long c = cost(), best = c; clock_t st = clock(); double cyc = 30.0; long it = 0;
    printf("START N=%d p=%d n=%d ne=%d start %ld\n", N, p, n, ne, c); fflush(stdout);
    if (best == 0) goto found;
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
                if (best == 0) goto found; }
        } else { ev[i] = sv[0]; ea[i] = sv[1]; ev[j] = sv[2]; ea[j] = sv[3]; }
    }
    printf("end best %ld its %ld\n", best, it);
    return 0;
found: {
    FILE *f = fopen(out, "w"); fprintf(f, "%d %d %d\n", N, gid, p);
    for (int e = 0; e < ne; e++) fprintf(f, "%d %d %d\n", eu[e], ev[e], ea[e]); fclose(f);
    printf("FOUND it=%ld\n", it); return 0; }
}
