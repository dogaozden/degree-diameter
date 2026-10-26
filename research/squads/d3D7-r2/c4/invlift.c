/* invlift (card r2-c4): annealing over lifts of cubic bipartite p+p base multigraphs with an involution sigma that
   has F = f fixed points per side (q = (p-f)/2 swapped pairs), and an involutory automorphism phi of G (phi^2 = id).
   Base structure: the base is the union of 3 perfect matchings, each invariant under sigma. Whites 0..p-1 (pairs
   {2i,2i+1} for i<q, fixed 2q..p-1), blacks p..2p-1 (same pattern). Matching k: pair-class i of whites goes to
   pair-class rho[k][i] of blacks with orientation ori[k][i], voltage v[k][i] on 2i and phi(v) on 2i+1; fixed whites
   2q+j go to fixed blacks 2q+tau[k][j] (with p+ offset) with voltage w[k][j] in Fix(phi).
   The base is then sigma-invariant (edge (x,y,a) -> (sigma x, sigma y, phi a)) and cubic by construction.
   Lift: vertex (u,g) = u*N+g, base edge (u,v,a) gives (u,g) ~ (v, g a); n = 2pN. Left multiplication is semiregular,
   so the 2p-source BFS is exact: cost = #(base vertex u, x) with dist((u,0),x) > D, plus 1000 per parallel base edge.
   Usage: invlift p GROUPS id seed seconds [T0] [T1] [out.edges]
   Env: F = fixed points per side (p-F even), PHI = file of N ints (automorphism, phi^2 = id; default identity),
        D = diameter (default 7), CYC = annealing cycle seconds (default 30). On cost 0 writes the lift edge list. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>

#define MAXP 32
static int p, q, f, N, D = 7, *mul, *inv, *phi, *fixl, nfix;
static uint64_t *R, *R2; static int *nbr;
static uint64_t rng = 88172645463325252ULL;
static inline uint64_t xr(void) { rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; return rng; }
static inline double ur(void) { return (xr() >> 11) * (1.0 / 9007199254740992.0); }

typedef struct { int rho[3][MAXP], ori[3][MAXP], v[3][MAXP], tau[3][MAXP], w[3][MAXP]; } St;
static St S, BS;
static int perm[3][2 * MAXP], volt[3][2 * MAXP];

static void expand(void) {
    for (int k = 0; k < 3; k++) {
        for (int i = 0; i < q; i++) {
            int y = p + 2 * S.rho[k][i], o = S.ori[k][i];
            perm[k][2 * i] = y + o;         volt[k][2 * i] = S.v[k][i];
            perm[k][2 * i + 1] = y + 1 - o; volt[k][2 * i + 1] = phi[S.v[k][i]];
        }
        for (int j = 0; j < f; j++) { perm[k][2 * q + j] = p + 2 * q + S.tau[k][j]; volt[k][2 * q + j] = S.w[k][j]; }
    }
}

static long cost(void) {
    static int dv[2 * MAXP][3], da[2 * MAXP][3];
    expand();
    long pen = 0;
    for (int k = 0; k < 3; k++) for (int x = 0; x < p; x++) {
        int y = perm[k][x], a = volt[k][x];
        dv[x][k] = y; da[x][k] = a; dv[y][k] = x; da[y][k] = inv[a]; }
    for (int x = 0; x < p; x++) for (int k = 0; k < 3; k++) for (int k2 = k + 1; k2 < 3; k2++)
        if (dv[x][k] == dv[x][k2] && da[x][k] == da[x][k2]) pen += 1000;
    int n = 2 * p * N;
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
    return c + pen;
}

static void shuffle(int *a, int m) { for (int i = m - 1; i > 0; i--) { int j = xr() % (i + 1), t = a[i]; a[i] = a[j]; a[j] = t; } }

static void write_lift(const char *out) {
    FILE *fo = fopen(out, "w"); if (!fo) return;
    fprintf(fo, "%d\n", 2 * p * N);
    for (int k = 0; k < 3; k++) for (int x = 0; x < p; x++) for (int g = 0; g < N; g++)
        fprintf(fo, "%d %d\n", x * N + g, perm[k][x] * N + mul[g * N + volt[k][x]]);
    fclose(fo);
}

int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: invlift p GROUPS id seed seconds [T0] [T1] [out.edges]\n"); return 2; }
    p = atoi(argv[1]); int want = atoi(argv[3]);
    if (p > MAXP) return 2;
    f = getenv("F") ? atoi(getenv("F")) : (p % 2);
    if (f < 0 || f > p || (p - f) % 2) { fprintf(stderr, "bad F\n"); return 2; }
    q = (p - f) / 2;
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
    phi = malloc(sizeof(int) * N);
    for (int a = 0; a < N; a++) phi[a] = a;
    if (getenv("PHI")) {
        FILE *fp = fopen(getenv("PHI"), "r");
        for (int a = 0; a < N; a++) if (fscanf(fp, "%d", &phi[a]) != 1) { fprintf(stderr, "bad PHI\n"); return 2; }
        fclose(fp);
    }
    for (int a = 0; a < N; a++) for (int b = 0; b < N; b++)
        if (mul[phi[a] * N + phi[b]] != phi[mul[a * N + b]]) { fprintf(stderr, "PHI not an automorphism\n"); return 2; }
    for (int a = 0; a < N; a++) if (phi[phi[a]] != a) { fprintf(stderr, "PHI^2 != id\n"); return 2; }
    fixl = malloc(sizeof(int) * N); nfix = 0;
    for (int a = 0; a < N; a++) if (phi[a] == a) fixl[nfix++] = a;
    int n = 2 * p * N; R = malloc(8L * n); R2 = malloc(8L * n); nbr = malloc(sizeof(int) * 3 * n);
    /* random initial state */
    for (int k = 0; k < 3; k++) {
        int pr[MAXP], pt[MAXP];
        for (int i = 0; i < q; i++) pr[i] = i;
        shuffle(pr, q);
        for (int i = 0; i < q; i++) { S.rho[k][i] = pr[i]; S.ori[k][i] = xr() & 1; S.v[k][i] = xr() % N; }
        for (int j = 0; j < f; j++) pt[j] = j;
        shuffle(pt, f);
        for (int j = 0; j < f; j++) { S.tau[k][j] = pt[j]; S.w[k][j] = fixl[xr() % nfix]; }
    }
    long c = cost(), best = c; clock_t st = clock(); long it = 0;
    printf("group N=%d id=%d %s p=%d q=%d f=%d n=%d |Fix(phi)|=%d D=%d start %ld\n", N, want, name, p, q, f, n, nfix, D, c);
    fflush(stdout);
    for (;;) {
        double el = (double)(clock() - st) / CLOCKS_PER_SEC; if (el > secs) break;
        double T = T0 * pow(T1 / T0, fmod(el, cyc) / cyc);
        BS = S;
        int mv = xr() % 5, k = xr() % 3, i = xr() % (q > 0 ? q : 1), j = xr() % (f > 0 ? f : 1);
        if (mv == 0) { if (!q) continue; S.v[k][i] = xr() % N; }
        else if (mv == 1) { if (!q) continue; S.ori[k][i] ^= 1; }
        else if (mv == 2) { if (q < 2) continue; int i2 = xr() % q; if (i2 == i) continue;
            int t = S.rho[k][i]; S.rho[k][i] = S.rho[k][i2]; S.rho[k][i2] = t; }
        else if (mv == 3) { if (!f) continue; S.w[k][j] = fixl[xr() % nfix]; }
        else { if (f < 2) continue; int j2 = xr() % f; if (j2 == j) continue;
            int t = S.tau[k][j]; S.tau[k][j] = S.tau[k][j2]; S.tau[k][j2] = t; }
        long c2 = cost(); it++;
        if (c2 <= c || ur() < exp((c - c2) / T)) {
            c = c2;
            if (c < best) { best = c; printf("t=%.1f it=%ld best %ld\n", el, it, best); fflush(stdout);
                if (best == 0) { write_lift(out); printf("FOUND\n"); break; } }
        } else S = BS;
    }
    printf("end best %ld its %ld\n", best, it);
    return 0;
}
