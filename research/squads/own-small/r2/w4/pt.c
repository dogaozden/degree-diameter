/* ptlift: salift_s (copied to w4/salift_s.c) + ONE idea: parallel tempering (own-small r2 card w4).
   M replicas of the same kind of state (base + voltages of a p+p cubic bipartite base over one group), each at a fixed
   temperature, geometric from PT_TLO to PT_THI. Each round, every replica makes PT_SW Metropolis moves at its own
   temperature (same moves, same cost as salift_s), then neighbouring replicas (alternating even/odd pairs) swap their
   states with probability min(1, exp((C_a - C_b) * (1/T_a - 1/T_b))). The best state over all replicas is written
   to OUT.best on each improvement, and OUT.sol at cost 0 (then the run stops), exactly as salift_s.
   Usage: ptlift p GROUPS id seed seconds [out.sol]
   env: D (default 10), START (a .best file: all replicas start from it), PT_M (6), PT_TLO (0.3), PT_THI (3.0),
   PT_SW (60 moves per replica per round). Lift convention and cost are those of salift_s.c. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>

#define MAXR 16
#define MAXE 96

static int p, k, N, D = 10, *mul, *inv, ne, gid;
static int eu[MAXE];
static int EV[MAXR][MAXE], EA[MAXR][MAXE];
static long C[MAXR];
static double TT[MAXR];
static uint64_t *R, *R2; static int *nbr;
static uint64_t rng = 88172645463325252ULL;
static inline uint64_t xr(void) { rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; return rng; }
static inline double ur(void) { return (xr() >> 11) * (1.0 / 9007199254740992.0); }

static long cost(const int *ev, const int *ea) {
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

/* random 3-matching base (white i -> black p + pi(i)), random voltages; eu is fixed */
static void rand_base(int *ev, int *ea) {
    for (int m = 0; m < 3; m++) {
        int pm[32];
        for (int i = 0; i < p; i++) pm[i] = i;
        for (int i = p - 1; i > 0; i--) { int j = xr() % (i + 1); int t = pm[i]; pm[i] = pm[j]; pm[j] = t; }
        for (int i = 0; i < p; i++) { ev[m * p + i] = p + pm[i]; ea[m * p + i] = xr() % N; }
    }
}

static void save_state(const char *path, const int *ev, const int *ea, long c) {
    char bp[600]; snprintf(bp, sizeof bp, "%s.best", path);
    FILE *fb = fopen(bp, "w"); fprintf(fb, "%d %d %d %ld\n", N, gid, p, c);
    for (int e = 0; e < ne; e++) fprintf(fb, "%d %d %d\n", eu[e], ev[e], ea[e]);
    fclose(fb);
}

int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: ptlift p GROUPS id seed seconds [out.sol]\n"); return 2; }
    p = atoi(argv[1]); k = 2 * p; int want = atoi(argv[3]);
    rng ^= (uint64_t)atoll(argv[4]) * 0x9E3779B97F4A7C15ULL; xr(); xr();
    double secs = atof(argv[5]);
    const char *out = argc > 6 ? argv[6] : "pt.sol";
    if (getenv("D")) D = atoi(getenv("D"));
    int M = getenv("PT_M") ? atoi(getenv("PT_M")) : 6;
    double Tlo = getenv("PT_TLO") ? atof(getenv("PT_TLO")) : 0.3;
    double Thi = getenv("PT_THI") ? atof(getenv("PT_THI")) : 3.0;
    int SW = getenv("PT_SW") ? atoi(getenv("PT_SW")) : 60;
    if (M < 1 || M > MAXR) { fprintf(stderr, "bad PT_M\n"); return 2; }

    FILE *fg = fopen(argv[2], "r"); char tag[8], name[256]; int found = 0;
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

    ne = 3 * p;
    for (int m = 0; m < 3; m++) for (int i = 0; i < p; i++) eu[m * p + i] = i;
    for (int r = 0; r < M; r++) TT[r] = M > 1 ? Tlo * pow(Thi / Tlo, (double)r / (M - 1)) : Tlo;

    if (getenv("START")) {
        FILE *fs = fopen(getenv("START"), "r"); int sN, sg, sp; long sc;
        if (!fs || fscanf(fs, "%d %d %d %ld", &sN, &sg, &sp, &sc) != 4 || sN != N || sp != p) { fprintf(stderr, "bad START\n"); return 2; }
        int tev[MAXE], tea[MAXE];
        for (int e = 0; e < ne; e++) { int u; if (fscanf(fs, "%d %d %d", &u, &tev[e], &tea[e]) != 3) { fprintf(stderr, "bad START\n"); return 2; } }
        fclose(fs);
        for (int r = 0; r < M; r++) for (int e = 0; e < ne; e++) { EV[r][e] = tev[e]; EA[r][e] = tea[e]; }
    } else {
        for (int r = 0; r < M; r++) rand_base(EV[r], EA[r]);
    }
    long best = 1L << 41; int bestr = 0;
    for (int r = 0; r < M; r++) { C[r] = cost(EV[r], EA[r]); if (C[r] < best) { best = C[r]; bestr = r; } }
    save_state(out, EV[bestr], EA[bestr], best);
    printf("group N=%d id=%d %s p=%d n=%d M=%d T=[%.2f..%.2f] SW=%d start %ld\n", N, gid, name, p, n, M, Tlo, Thi, SW, best);
    fflush(stdout);

    clock_t st = clock(); long it = 0; int round = 0, done = 0;
    for (;;) {
        double el = (double)(clock() - st) / CLOCKS_PER_SEC; if (el > secs) break;
        for (int r = 0; r < M && !done; r++) {
            double T = TT[r]; int *ev = EV[r], *ea = EA[r];
            for (int s = 0; s < SW; s++) {
                int i = xr() % ne, j = xr() % ne, sv[4] = {ev[i], ea[i], ev[j], ea[j]};
                if (xr() & 1) { ea[i] = xr() % N; }
                else { if (i == j || ev[i] == ev[j]) continue; int t = ev[i]; ev[i] = ev[j]; ev[j] = t; if (xr() & 1) ea[i] = xr() % N; }
                long c2 = cost(ev, ea); it++;
                if (c2 <= C[r] || ur() < exp((C[r] - c2) / T)) {
                    C[r] = c2;
                    if (c2 < best) {
                        best = c2; bestr = r;
                        el = (double)(clock() - st) / CLOCKS_PER_SEC;
                        printf("t=%.1f it=%ld best %ld replica %d T=%.2f\n", el, it, best, r, T); fflush(stdout);
                        save_state(out, ev, ea, best);
                        if (best == 0) {
                            FILE *f = fopen(out, "w"); fprintf(f, "%d %d %d\n", N, gid, p);
                            for (int e = 0; e < ne; e++) fprintf(f, "%d %d %d\n", eu[e], ev[e], ea[e]);
                            fclose(f); printf("FOUND\n"); done = 1; break;
                        }
                    }
                } else { ev[i] = sv[0]; ea[i] = sv[1]; ev[j] = sv[2]; ea[j] = sv[3]; }
            }
        }
        if (done) break;
        /* replica exchange between neighbouring temperatures, alternating even/odd pairs */
        for (int a = round & 1; a + 1 < M; a += 2) {
            int b = a + 1;
            double d = ((double)C[a] - (double)C[b]) * (1.0 / TT[a] - 1.0 / TT[b]);
            if (d >= 0 || ur() < exp(d)) {
                for (int e = 0; e < ne; e++) {
                    int t = EV[a][e]; EV[a][e] = EV[b][e]; EV[b][e] = t;
                    t = EA[a][e]; EA[a][e] = EA[b][e]; EA[b][e] = t;
                }
                long tc = C[a]; C[a] = C[b]; C[b] = tc;
            }
        }
        round++;
    }
    printf("end best %ld its %ld rounds %d costs", best, it, round);
    for (int r = 0; r < M; r++) printf(" %ld", C[r]);
    printf("\n");
    return 0;
}
