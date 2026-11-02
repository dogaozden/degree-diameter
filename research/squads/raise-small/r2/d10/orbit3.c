/* orbit3 (round-2 card d10, own work): orbit-constrained joint annealing of cubic bipartite 3+3 lifts.
   Base: whites 0,1,2, blacks 3,4,5. sigma = rotation: white w -> (w+1)%3, black 3+b -> 3+(b+1)%3.
   sigma has 3 edge orbits of size 3; orbit i has difference d_i in {0,1,2} and consists of the edges
   (w, 3+(w+d_i)%3) for w = 0,1,2, with voltage x(sigma^w e_i) = alpha^w(x_i), where x_i is the voltage of (0, 3+d_i).
   Group G = Z_m x|_r Z_k (index x = a*k + j, identity 0, product as gtab.py), alpha(a,j) = (t*a mod m, j), t^3 = 1, t != 1 mod m.
   Only 3 voltages x_i and 3 differences d_i are free (repeated d_i allowed: parallel base edges, distinct voltages).
   Cost exactly as salift_s: #(base root u, vertex x) with dist > D (env D, default 7); 0 = diameter <= D.
   Usage: orbit3 m k r t GROUPS id seed secs [T0 T1] OUT.sol   (env D, START=file.best)
   GROUPS: gtab.py file (one group, id as in file). Writes OUT.sol.best ("N id 3 cost" + 9 lines "u v x") on each
   improvement and OUT.sol (same format, cost 0) when found. Moves: change one x_i (50%), change one d_i (50%). */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>

static int m, k, r, t, N, D = 7, *mul, *inv, *al, *al2;
static int eu[9], ev[9], ea[9];
static int dd[3], xv[3];
static uint64_t *R, *R2; static int *nbr;
static uint64_t rng = 88172645463325252ULL;
static inline uint64_t xr(void) { rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; return rng; }
static inline double ur(void) { return (xr() >> 11) * (1.0 / 9007199254740992.0); }

static void build(void) {
    int ne = 0;
    for (int i = 0; i < 3; i++) for (int w = 0; w < 3; w++) {
        eu[ne] = w; ev[ne] = 3 + (w + dd[i]) % 3;
        ea[ne] = w == 0 ? xv[i] : (w == 1 ? al[xv[i]] : al2[xv[i]]);
        ne++;
    }
}

static long cost(void) {
    for (int e = 0; e < 9; e++) for (int f = e + 1; f < 9; f++)
        if (eu[e] == eu[f] && ev[e] == ev[f] && ea[e] == ea[f]) return 1L << 40;
    int n = 6 * N, dg[6] = {0};
    static int dv[6][3], da[6][3];
    for (int e = 0; e < 9; e++) { int u = eu[e], v = ev[e];
        dv[u][dg[u]] = v; da[u][dg[u]++] = ea[e]; dv[v][dg[v]] = u; da[v][dg[v]++] = inv[ea[e]]; }
    for (int u = 0; u < 6; u++) for (int g = 0; g < N; g++) for (int j = 0; j < 3; j++)
        nbr[(u * N + g) * 3 + j] = dv[u][j] * N + mul[g * N + da[u][j]];
    memset(R, 0, 8L * n);
    for (int u = 0; u < 6; u++) R[u * N] = 1ULL << u;
    for (int s = 0; s < D; s++) {
        for (int x = 0; x < n; x++) R2[x] = R[x] | R[nbr[3 * x]] | R[nbr[3 * x + 1]] | R[nbr[3 * x + 2]];
        uint64_t *tmp = R; R = R2; R2 = tmp;
    }
    uint64_t full = (1ULL << 6) - 1; long c = 0;
    for (int x = 0; x < n; x++) c += __builtin_popcountll(~R[x] & full);
    return c;
}

static void write_state(const char *path, long c, int gid) {
    FILE *f = fopen(path, "w"); if (!f) return;
    if (c >= 0) fprintf(f, "%d %d 3 %ld\n", N, gid, c); else fprintf(f, "%d %d 3\n", N, gid);
    for (int e = 0; e < 9; e++) fprintf(f, "%d %d %d\n", eu[e], ev[e], ea[e]);
    fclose(f);
}

int main(int argc, char **argv) {
    if (argc < 9) { fprintf(stderr, "usage: orbit3 m k r t GROUPS id seed secs [T0 T1] OUT.sol\n"); return 2; }
    m = atoi(argv[1]); k = atoi(argv[2]); r = atoi(argv[3]); t = atoi(argv[4]);
    int want = atoi(argv[6]);
    rng ^= (uint64_t)atoll(argv[7]) * 0x9E3779B97F4A7C15ULL; xr(); xr();
    double secs = atof(argv[8]), T0 = argc > 9 ? atof(argv[9]) : 6.0, T1 = argc > 10 ? atof(argv[10]) : 0.3;
    const char *out = argc > 11 ? argv[11] : "orbit.sol";
    if (getenv("D")) D = atoi(getenv("D"));
    if ((long)t * t % m * t % m != 1 % m || t % m == 1 % m) { fprintf(stderr, "t must satisfy t^3 = 1, t != 1 mod m\n"); return 2; }
    FILE *fg = fopen(argv[5], "r"); char tag[8], name[256]; int gid, found = 0;
    while (fscanf(fg, "%7s %d %d %255s", tag, &N, &gid, name) == 4) {
        mul = malloc(sizeof(int) * N * N);
        for (int i = 0; i < N * N; i++) if (fscanf(fg, "%d", &mul[i]) != 1) return 3;
        if (gid == want) { found = 1; break; }
        free(mul);
    }
    if (!found) { fprintf(stderr, "group not found\n"); return 2; }
    if (N != m * k) { fprintf(stderr, "N != m*k\n"); return 2; }
    inv = malloc(sizeof(int) * N); al = malloc(sizeof(int) * N); al2 = malloc(sizeof(int) * N);
    for (int a = 0; a < N; a++) for (int b = 0; b < N; b++) if (mul[a * N + b] == 0) inv[a] = b;
    for (int x = 0; x < N; x++) { int a = x / k, j = x % k; al[x] = (int)(((long)t * a) % m) * k + j; }
    for (int x = 0; x < N; x++) al2[x] = al[al[x]];
    /* check alpha is a group automorphism of the table, and has order 3 */
    for (int s = 0; s < 20000; s++) { int g = xr() % N, h = xr() % N;
        if (al[mul[g * N + h]] != mul[al[g] * N + al[h]]) { fprintf(stderr, "alpha not an automorphism\n"); return 2; } }
    for (int x = 0; x < N; x++) if (al[al2[x]] != x) { fprintf(stderr, "alpha^3 != 1\n"); return 2; }
    int n = 6 * N; R = malloc(8L * n); R2 = malloc(8L * n); nbr = malloc(sizeof(int) * 3 * n);
    if (getenv("START")) { FILE *fs = fopen(getenv("START"), "r"); int sN, sg, sp; char hl[256];
        if (!fs || !fgets(hl, sizeof hl, fs) || sscanf(hl, "%d %d %d", &sN, &sg, &sp) < 3 || sN != N || sp != 3) { fprintf(stderr, "bad START\n"); return 2; }
        for (int e = 0; e < 9; e++) { int u, v, x; if (fscanf(fs, "%d %d %d", &u, &v, &x) != 3) { fprintf(stderr, "bad START\n"); return 2; }
            if (e % 3 == 0) { dd[e / 3] = (v - 3 + 3) % 3; xv[e / 3] = x; } }
        fclose(fs); }
    else for (int i = 0; i < 3; i++) { dd[i] = xr() % 3; xv[i] = xr() % N; }
    build();
    long c = cost(), best = c; clock_t st = clock(); double cyc = getenv("CYC") ? atof(getenv("CYC")) : 30.0; long it = 0;
    char bp[600]; snprintf(bp, sizeof bp, "%s.best", out);
    printf("orbit group N=%d id=%d m=%d k=%d r=%d t=%d D=%d start %ld\n", N, want, m, k, r, t, D, c); fflush(stdout);
    for (;;) {
        double el = (double)(clock() - st) / CLOCKS_PER_SEC; if (el > secs) break;
        double T = T0 * pow(T1 / T0, fmod(el, cyc) / cyc);
        int sd[3], sx[3]; memcpy(sd, dd, sizeof sd); memcpy(sx, xv, sizeof sx);
        int i = xr() % 3;
        if (xr() & 1) xv[i] = xr() % N; else dd[i] = xr() % 3;
        build();
        long c2 = cost(); it++;
        if (c2 <= c || ur() < exp((c - c2) / T)) {
            c = c2;
            if (c < best) { best = c; printf("t=%.1f it=%ld best %ld  d=%d%d%d\n", el, it, best, dd[0], dd[1], dd[2]); fflush(stdout);
                write_state(bp, best, want);
                if (best == 0) { write_state(out, -1, want); printf("FOUND\n"); break; } }
        } else { memcpy(dd, sd, sizeof dd); memcpy(xv, sx, sizeof xv); }
    }
    printf("end best %ld its %ld\n", best, it);
    return 0;
}
