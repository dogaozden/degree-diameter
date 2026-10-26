/* symlift2 (r2 card c3): lifts with an order-3 symmetry sigma that HAS FIXED POINTS.
   Derived from research/squads/d3D7-r1/c5/symlift.c (fixed-point-free case, f = 0).
   Usage: symlift2 p f GROUPS id seed seconds [T0] [T1] [out.edges]
     p = vertices per side of the base, f = fixed vertices per side (p - f = 3q, q >= 1, m = 3q - f >= 1).
   Env: PHI = file of N ints, an automorphism of the group of order dividing 3 (default identity),
        D = diameter (default 7), CYC = annealing cycle length in seconds (default 30).

   Base layout (same on both sides): index k*q + x (k = 0,1,2, x < q) are the moving vertices of sigma-block k;
   index 3q + i (i < f) are the fixed vertices. sigma: (k,x) -> (k+1 mod 3, x), fixes 3q+i.
   Base edge (u,v,a) present  =>  (sigma u, sigma v, phi a) present.
   Pattern types (each base orbit is listed by its representative):
     MM(x, c, y, a): white (0,x) ~ black (c,y), voltage a; orbit: (k,x) ~ ((c+k),y) with phi^k a  (3 edges).
     FM(i, y, a)   : fixed white 3q+i ~ black (k,y) with phi^k a for k = 0,1,2  (3 edges, fixes white i).
     MF(j, x, b)   : white (k,x) ~ fixed black 3q+j with phi^k b for k = 0,1,2  (3 edges, fixes black j).
   Degrees: every moving white rep x occurs in exactly 3 of {MM, MF}; every moving black rep y in exactly 3 of
   {MM, FM}; each fixed vertex has exactly one pattern (3 edges). Fixed-fixed edges are never used: they would
   split the graph (a fixed vertex with three fixed-fixed edges has no neighbour outside the fixed set), so
   connectivity needs m >= 1.
   Implementation: WS (3q slots, slot s < f is MF for fixed black s, slot s >= f is MM number s-f) holds the white
   reps; YS (3q slots, s < f is FM for fixed white s, s >= f is MM number s-f) holds the black reps. Moves permute
   WS or YS (keeps the multisets, hence the degrees), change voltages, or change c of an MM pattern.
   Lift: vertex (u,g) = u*N+g, base edge (u,v,a) gives (u,g) ~ (v, g*a). Lift automorphism (u,g) -> (sigma u, phi g);
   it is NOT semiregular (fixes (3q+i, g) with phi g = g). Cost = #(base vertex u, vertex x) with dist((u,1),x) > D,
   exactly as in salift. On cost 0 writes the lift as an edge list ("n", then "u v" per edge) and prints the pattern. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>

static int p, f, q, m, N, D = 7, *mul, *inv, *phi1, *phi2;
static int WS[64], YS[64], VA[64], VB[64], VM[64], CM[64];
static int eu[256], ev[256], ea[256], ne;
static uint64_t *R, *R2; static int *nbr;
static uint64_t rng = 88172645463325252ULL;
static inline uint64_t xr(void) { rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; return rng; }
static inline double ur(void) { return (xr() >> 11) * (1.0 / 9007199254740992.0); }

static inline int phik(int a, int k) { return k == 0 ? a : k == 1 ? phi1[a] : phi2[a]; }

static void expand(void) {
    ne = 0;
    for (int i = 0; i < f; i++) for (int k = 0; k < 3; k++) {          /* FM: fixed white 3q+i */
        eu[ne] = 3 * q + i; ev[ne] = p + k * q + YS[i]; ea[ne] = phik(VA[i], k); ne++; }
    for (int j = 0; j < f; j++) for (int k = 0; k < 3; k++) {          /* MF: fixed black 3q+j */
        eu[ne] = k * q + WS[j]; ev[ne] = p + 3 * q + j; ea[ne] = phik(VB[j], k); ne++; }
    for (int i = 0; i < m; i++) for (int k = 0; k < 3; k++) {          /* MM */
        int x = WS[f + i], y = YS[f + i], c = CM[i];
        eu[ne] = k * q + x; ev[ne] = p + ((c + k) % 3) * q + y; ea[ne] = phik(VM[i], k); ne++; }
}

static long cost(void) {
    for (int e = 0; e < ne; e++) for (int g = e + 1; g < ne; g++)
        if (eu[e] == eu[g] && ev[e] == ev[g] && ea[e] == ea[g]) return 1L << 40;
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
    FILE *fo = fopen(out, "w"); if (!fo) return;
    fprintf(fo, "%d\n", 2 * p * N);
    for (int e = 0; e < ne; e++) for (int g = 0; g < N; g++)
        fprintf(fo, "%d %d\n", eu[e] * N + g, ev[e] * N + mul[g * N + ea[e]]);
    fclose(fo);
}

typedef struct { int WS[64], YS[64], VA[64], VB[64], VM[64], CM[64]; } State;
static void save(State *s) { memcpy(s->WS, WS, sizeof WS); memcpy(s->YS, YS, sizeof YS);
    memcpy(s->VA, VA, sizeof VA); memcpy(s->VB, VB, sizeof VB); memcpy(s->VM, VM, sizeof VM); memcpy(s->CM, CM, sizeof CM); }
static void load_state(const State *s) { memcpy(WS, s->WS, sizeof WS); memcpy(YS, s->YS, sizeof YS);
    memcpy(VA, s->VA, sizeof VA); memcpy(VB, s->VB, sizeof VB); memcpy(VM, s->VM, sizeof VM); memcpy(CM, s->CM, sizeof CM); }

int main(int argc, char **argv) {
    if (argc < 7) { fprintf(stderr, "usage: symlift2 p f GROUPS id seed seconds [T0] [T1] [out.edges]\n"); return 2; }
    p = atoi(argv[1]); f = atoi(argv[2]); int want = atoi(argv[4]);
    if (p > 32 || f < 0 || (p - f) % 3 || p - f < 3) { fprintf(stderr, "need p<=32, p-f = 3q with q>=1\n"); return 2; }
    q = (p - f) / 3; m = 3 * q - f;
    if (m < 1) { fprintf(stderr, "need m = 3q - f >= 1 (else the graph is disconnected)\n"); return 2; }
    rng ^= (uint64_t)atoll(argv[5]) * 0x9E3779B97F4A7C15ULL; xr(); xr();
    double secs = atof(argv[6]), T0 = argc > 7 ? atof(argv[7]) : 10.0, T1 = argc > 8 ? atof(argv[8]) : 0.3;
    const char *out = argc > 9 ? argv[9] : "best.edges";
    double cyc = getenv("CYC") ? atof(getenv("CYC")) : 30.0;
    if (getenv("D")) D = atoi(getenv("D"));
    FILE *fg = fopen(argv[3], "r"); char tag[8], name[256]; int gid, found = 0;
    while (fscanf(fg, "%7s %d %d %255s", tag, &N, &gid, name) == 4) {
        mul = malloc(sizeof(int) * N * N);
        for (int i = 0; i < N * N; i++) if (fscanf(fg, "%d", &mul[i]) != 1) return 3;
        if (gid == want) { found = 1; break; }
        free(mul);
    }
    if (!found) { fprintf(stderr, "group not found\n"); return 2; }
    inv = malloc(sizeof(int) * N);
    for (int a = 0; a < N; a++) for (int b = 0; b < N; b++) if (mul[a * N + b] == 0) inv[a] = b;
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
    /* random initial state: each rep occurs 3 times on each side (3q slots), split into fixed and MM slots */
    for (int s = 0; s < 3 * q; s++) { WS[s] = s / 3; YS[s] = s / 3; }
    for (int i = 3 * q - 1; i > 0; i--) { int j = xr() % (i + 1), t = WS[i]; WS[i] = WS[j]; WS[j] = t;
                                           j = xr() % (i + 1); t = YS[i]; YS[i] = YS[j]; YS[j] = t; }
    for (int i = 0; i < f; i++) { VA[i] = xr() % N; VB[i] = xr() % N; }
    for (int i = 0; i < m; i++) { VM[i] = xr() % N; CM[i] = xr() % 3; }
    expand();
    long c = cost(), best = c; clock_t st = clock(); long it = 0;
    printf("group N=%d id=%d %s p=%d f=%d q=%d m=%d n=%d phi=%s start %ld\n", N, gid, name, p, f, q, m, n,
           getenv("PHI") ? getenv("PHI") : "id", c); fflush(stdout);
    State sv;
    for (;;) {
        double el = (double)(clock() - st) / CLOCKS_PER_SEC; if (el > secs) break;
        double T = T0 * pow(T1 / T0, fmod(el, cyc) / cyc);
        save(&sv);
        int mv = xr() % 4;
        if (mv == 0) {                                   /* change one voltage (FM, MF or MM) */
            int r = xr() % p;
            if (r < f) VA[r] = xr() % N; else if (r < 2 * f) VB[r - f] = xr() % N; else VM[r - 2 * f] = xr() % N;
        } else if (mv == 1) {                            /* change block offset c of an MM pattern */
            if (m == 0) continue;
            int i = xr() % m; CM[i] = (CM[i] + 1 + xr() % 2) % 3;
        } else {                                         /* permute white reps or black reps (keeps multisets) */
            int i = xr() % (3 * q), j = xr() % (3 * q); if (i == j) continue;
            if (mv == 2) { int t = WS[i]; WS[i] = WS[j]; WS[j] = t; }
            else { int t = YS[i]; YS[i] = YS[j]; YS[j] = t; }
        }
        expand();
        long c2 = cost(); it++;
        if (c2 <= c || ur() < exp((c - c2) / T)) {
            c = c2;
            if (c < best) { best = c; printf("t=%.1f it=%ld best %ld\n", el, it, best); fflush(stdout);
                if (best == 0) {
                    write_lift(out);
                    for (int i = 0; i < f; i++) printf("FM fixedwhite=%d y=%d a=%d\n", i, YS[i], VA[i]);
                    for (int j = 0; j < f; j++) printf("MF fixedblack=%d x=%d b=%d\n", j, WS[j], VB[j]);
                    for (int i = 0; i < m; i++) printf("MM x=%d c=%d y=%d a=%d\n", WS[f + i], CM[i], YS[f + i], VM[i]);
                    printf("FOUND\n"); break; } }
        } else {
            load_state(&sv); expand();
        }
    }
    printf("end best %ld its %ld\n", best, it);
    return 0;
}
