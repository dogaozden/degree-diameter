/* symlift (card c5): annealing over lifts with extra symmetry, derived from research/d3D7/salift.c.
   Usage: symlift p GROUPS id seed seconds [T0] [T1] [out.edges]
   Env: PHI=file of N ints = automorphism phi of the group (default identity), must have order dividing 3;
        D = diameter (default 7); CYC = length of one annealing cycle in seconds (default 30).
   Base: whites u < p, blacks p+v, with p = 3q. sigma maps block k -> k+1 (mod 3) on each side, same offset.
   Pattern: p edges (x, c, y, a): x, y in [0,q), c in {0,1,2}, a in Z_N. Its sigma-orbit gives the base edges
     (white k*q+x, black p+((c+k) mod 3)*q+y, phi^k(a))   for k = 0, 1, 2.
   Each x occurs in 3 pattern edges and each y in 3, so the base is cubic bipartite. Moves: change a voltage,
   change c, swap two y's, swap two x's (all keep the degrees and sigma-invariance).
   Lift: vertex (u,g) = u*N+g, base edge (u,v,a) gives (u,g) ~ (v, g*a). Lift is invariant under
   (u,g) -> (sigma u, phi g), so the cost is exactly as in salift: #(base vertex u, vertex x) with dist((u,1),x) > D.
   On cost 0 writes the lift as an edge list ("n", then "u v" per edge) and prints the pattern. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>

static int p, q, N, D = 7, *mul, *inv, *phi1, *phi2;
static int px[64], pc[64], py[64], pa[64];
static int eu[192], ev[192], ea[192], ne;
static uint64_t *R, *R2; static int *nbr;
static uint64_t rng = 88172645463325252ULL;
static inline uint64_t xr(void) { rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; return rng; }
static inline double ur(void) { return (xr() >> 11) * (1.0 / 9007199254740992.0); }

static void expand(void) {
    ne = 0;
    for (int i = 0; i < p; i++) for (int k = 0; k < 3; k++) {
        int a = k == 0 ? pa[i] : k == 1 ? phi1[pa[i]] : phi2[pa[i]];
        eu[ne] = k * q + px[i];
        ev[ne] = p + ((pc[i] + k) % 3) * q + py[i];
        ea[ne] = a; ne++;
    }
}

static long cost(void) {
    for (int e = 0; e < ne; e++) for (int f = e + 1; f < ne; f++)
        if (eu[e] == eu[f] && ev[e] == ev[f] && ea[e] == ea[f]) return 1L << 40;
    int n = 2 * p * N, dg[64] = {0};
    static int dv[64][3], da[64][3];
    for (int e = 0; e < ne; e++) { int u = eu[e], v = ev[e];
        if (dg[u] >= 3 || dg[v] >= 3) return 1L << 41;
        dv[u][dg[u]] = v; da[u][dg[u]++] = ea[e]; dv[v][dg[v]] = u; da[v][dg[v]++] = inv[ea[e]]; }
    for (int u = 0; u < 2 * p; u++) if (dg[u] != 3) return 1L << 41;
    for (int u = 0; u < 2 * p; u++) for (int g = 0; g < N; g++) for (int j = 0; j < 3; j++)
        nbr[(u * N + g) * 3 + j] = dv[u][j] * N + mul[g * N + da[u][j]];
    memset(R, 0, 8L * n);
    for (int u = 0; u < 2 * p; u++) R[u * N] = 1ULL << u;
    for (int t = 0; t < D; t++) {
        for (int x = 0; x < n; x++) R2[x] = R[x] | R[nbr[3 * x]] | R[nbr[3 * x + 1]] | R[nbr[3 * x + 2]];
        uint64_t *tmp = R; R = R2; R2 = tmp;
    }
    uint64_t full = (1ULL << (2 * p)) - 1; long c = 0;
    for (int x = 0; x < n; x++) c += __builtin_popcountll(~R[x] & full);
    return c;
}

static void write_lift(const char *out) {
    FILE *f = fopen(out, "w"); if (!f) return;
    fprintf(f, "%d\n", 2 * p * N);
    for (int e = 0; e < ne; e++) for (int g = 0; g < N; g++)
        fprintf(f, "%d %d\n", eu[e] * N + g, ev[e] * N + mul[g * N + ea[e]]);
    fclose(f);
}

int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: symlift p GROUPS id seed seconds [T0] [T1] [out.edges]\n"); return 2; }
    p = atoi(argv[1]); int want = atoi(argv[3]);
    if (p % 3 || p > 32) { fprintf(stderr, "p must be divisible by 3 and <= 32\n"); return 2; }
    q = p / 3;
    rng ^= (uint64_t)atoll(argv[4]) * 0x9E3779B97F4A7C15ULL; xr(); xr();
    double secs = atof(argv[5]), T0 = argc > 6 ? atof(argv[6]) : 10.0, T1 = argc > 7 ? atof(argv[7]) : 0.3;
    const char *out = argc > 8 ? argv[8] : "best.edges";
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
    /* phi: automorphism of order dividing 3 (identity unless PHI is set) */
    phi1 = malloc(sizeof(int) * N); phi2 = malloc(sizeof(int) * N);
    for (int a = 0; a < N; a++) phi1[a] = a;
    if (getenv("PHI")) {
        FILE *fp = fopen(getenv("PHI"), "r");
        for (int a = 0; a < N; a++) if (fscanf(fp, "%d", &phi1[a]) != 1) { fprintf(stderr, "bad PHI\n"); return 2; }
        fclose(fp);
    }
    for (int a = 0; a < N; a++) for (int b = 0; b < N; b++)
        if (mul[phi1[a] * N + phi1[b]] != phi1[mul[a * N + b]]) { fprintf(stderr, "PHI is not an automorphism\n"); return 2; }
    for (int a = 0; a < N; a++) { phi2[a] = phi1[phi1[a]]; if (phi1[phi2[a]] != a) { fprintf(stderr, "PHI^3 != id\n"); return 2; } }
    int n = 2 * p * N; R = malloc(8L * n); R2 = malloc(8L * n); nbr = malloc(sizeof(int) * 3 * n);
    /* random pattern: each x and each y three times */
    int xs[64], ys[64];
    for (int i = 0; i < p; i++) { xs[i] = i / 3; ys[i] = i / 3; }
    for (int i = p - 1; i > 0; i--) { int j = xr() % (i + 1), t = xs[i]; xs[i] = xs[j]; xs[j] = t;
                                       j = xr() % (i + 1); t = ys[i]; ys[i] = ys[j]; ys[j] = t; }
    for (int i = 0; i < p; i++) { px[i] = xs[i]; py[i] = ys[i]; pc[i] = xr() % 3; pa[i] = xr() % N; }
    expand();
    long c = cost(), best = c; clock_t st = clock(); long it = 0;
    printf("group N=%d id=%d %s p=%d q=%d n=%d phi=%s start %ld\n", N, gid, name, p, q, n,
           getenv("PHI") ? getenv("PHI") : "id", c); fflush(stdout);
    int bx[64], bc[64], by[64], ba[64];
    for (;;) {
        double el = (double)(clock() - st) / CLOCKS_PER_SEC; if (el > secs) break;
        double T = T0 * pow(T1 / T0, fmod(el, cyc) / cyc);
        memcpy(bx, px, sizeof px); memcpy(bc, pc, sizeof pc); memcpy(by, py, sizeof py); memcpy(ba, pa, sizeof pa);
        int mv = xr() % 4, i = xr() % p, j = xr() % p;
        if (mv == 0) pa[i] = xr() % N;
        else if (mv == 1) pc[i] = (pc[i] + 1 + xr() % 2) % 3;
        else if (mv == 2) { if (i == j) continue; int t = py[i]; py[i] = py[j]; py[j] = t; }
        else { if (i == j) continue; int t = px[i]; px[i] = px[j]; px[j] = t; }
        expand();
        long c2 = cost(); it++;
        if (c2 <= c || ur() < exp((c - c2) / T)) {
            c = c2;
            if (c < best) { best = c; printf("t=%.1f it=%ld best %ld\n", el, it, best); fflush(stdout);
                if (best == 0) {
                    write_lift(out);
                    for (int e = 0; e < p; e++) printf("pat x=%d c=%d y=%d a=%d\n", px[e], pc[e], py[e], pa[e]);
                    printf("FOUND\n"); break; } }
        } else {
            memcpy(px, bx, sizeof px); memcpy(pc, bc, sizeof pc); memcpy(py, by, sizeof py); memcpy(pa, ba, sizeof pa);
        }
    }
    printf("end best %ld its %ld\n", best, it);
    return 0;
}
