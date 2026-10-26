/* pt: parallel tempering over voltage lifts of cubic bipartite p+p base multigraphs (same model as research/d3D7/salift.c:
   base edges and voltages both free, lift vertex (u,g) = u*N+g, base edge (u,v,a) gives (u,g) ~ (v, g*a)).
   Usage: pt p GROUPS id seed seconds [Tmin=0.3] [Tmax=20] [out.sol=best.sol]
   env: NREP  replicas (default 8), temperatures geometric from Tmin (slot 0) to Tmax
        SWEEP moves per replica between swap rounds (default 100)
        ALPHA energy = c7 + ALPHA*c8 (default 0 = plain salift cost). c7 = #(base vertex u, vertex x) with dist > D,
              c8 = the same with dist > D+1 (a gradient on the plateau: pairs at distance 9+ count extra).
        D    diameter bound (default 7).
   The reported cost is always c7 (0 = valid). Output on cost 0: "N id p" then 3p lines "u v a" (liftedges.py format).
   Moves as in salift: change one voltage, or switch two base edges (and maybe re-draw a voltage). */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>
#include <limits.h>

#define MAXE 96
#define BIGE 1e9
#define HUGE_C (1L << 40)

static int p, k, N, D = 7, *mul, *inv, ne, n, NREP = 8, SWEEP = 100;
static double ALPHA = 0.0;
static int eu[MAXE];
static uint64_t *Ra, *Rb; static int *nbr;
static uint64_t rng = 88172645463325252ULL;
static inline uint64_t xr(void) { rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; return rng; }
static inline double ur(void) { return (xr() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) { struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts); return ts.tv_sec + 1e-9 * ts.tv_nsec; }

/* c7 = #(base vertex, vertex) pairs at distance > D; c8 = same for > D+1. Bit-parallel BFS from the 2p white-side
   sources (u,1); by left-multiplication symmetry this is the exact all-pairs count. */
static void evalcost(const int *ev, const int *ea, long *c7, long *c8) {
    for (int e = 0; e < ne; e++) for (int f = e + 1; f < ne; f++)
        if (eu[e] == eu[f] && ev[e] == ev[f] && ea[e] == ea[f]) { *c7 = HUGE_C; *c8 = 0; return; }
    int dg[64] = {0}; static int dv[64][3], da[64][3];
    for (int e = 0; e < ne; e++) { int u = eu[e], v = ev[e];
        dv[u][dg[u]] = v; da[u][dg[u]++] = ea[e]; dv[v][dg[v]] = u; da[v][dg[v]++] = inv[ea[e]]; }
    for (int u = 0; u < k; u++) for (int g = 0; g < N; g++) for (int j = 0; j < 3; j++)
        nbr[(u * N + g) * 3 + j] = dv[u][j] * N + mul[g * N + da[u][j]];
    uint64_t *A = Ra, *B = Rb;
    memset(A, 0, 8L * n);
    for (int u = 0; u < k; u++) A[u * N] = 1ULL << u;
    for (int t = 0; t < D; t++) {
        for (int x = 0; x < n; x++) B[x] = A[x] | A[nbr[3 * x]] | A[nbr[3 * x + 1]] | A[nbr[3 * x + 2]];
        uint64_t *tmp = A; A = B; B = tmp;
    }
    uint64_t full = (1ULL << k) - 1; long c = 0;
    for (int x = 0; x < n; x++) c += __builtin_popcountll(~A[x] & full);
    *c7 = c;
    for (int x = 0; x < n; x++) B[x] = A[x] | A[nbr[3 * x]] | A[nbr[3 * x + 1]] | A[nbr[3 * x + 2]];
    c = 0;
    for (int x = 0; x < n; x++) c += __builtin_popcountll(~B[x] & full);
    *c8 = c;
}

typedef struct { int ev[MAXE], ea[MAXE]; double E; long c7, c8; } St;

static void write_sol(const char *out, const int *ev, const int *ea, int gid) {
    FILE *f = fopen(out, "w"); fprintf(f, "%d %d %d\n", N, gid, p);
    for (int e = 0; e < ne; e++) fprintf(f, "%d %d %d\n", eu[e], ev[e], ea[e]);
    fclose(f);
}

int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: pt p GROUPS id seed seconds [Tmin] [Tmax] [out.sol]\n"); return 2; }
    p = atoi(argv[1]); k = 2 * p; int want = atoi(argv[3]);
    if (k > 63) { fprintf(stderr, "p too big\n"); return 2; }
    rng ^= (uint64_t)atoll(argv[4]) * 0x9E3779B97F4A7C15ULL; xr(); xr();
    double secs = atof(argv[5]), Tmin = argc > 6 ? atof(argv[6]) : 0.3, Tmax = argc > 7 ? atof(argv[7]) : 20.0;
    const char *out = argc > 8 ? argv[8] : "best.sol";
    if (getenv("D")) D = atoi(getenv("D"));
    if (getenv("NREP")) NREP = atoi(getenv("NREP"));
    if (getenv("SWEEP")) SWEEP = atoi(getenv("SWEEP"));
    if (getenv("ALPHA")) ALPHA = atof(getenv("ALPHA"));
    if (NREP < 1 || NREP > 64) NREP = 8;

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
    n = k * N; Ra = malloc(8L * n); Rb = malloc(8L * n); nbr = malloc(sizeof(int) * 3 * n);

    /* base skeleton: three perfect matchings white -> black (eu fixed), ev and ea start random */
    ne = 3 * p;
    for (int m = 0; m < 3; m++) for (int i = 0; i < p; i++) eu[m * p + i] = i;

    St *S = malloc(sizeof(St) * NREP); int *slot = malloc(sizeof(int) * NREP);
    double *Tt = malloc(sizeof(double) * NREP);
    for (int r = 0; r < NREP; r++) {
        St *s = &S[r];
        for (int m = 0; m < 3; m++) { int pm[32]; for (int i = 0; i < p; i++) pm[i] = i;
            for (int i = p - 1; i > 0; i--) { int j = xr() % (i + 1); int t = pm[i]; pm[i] = pm[j]; pm[j] = t; }
            for (int i = 0; i < p; i++) { s->ev[m * p + i] = p + pm[i]; s->ea[m * p + i] = xr() % N; } }
        evalcost(s->ev, s->ea, &s->c7, &s->c8);
        s->E = s->c7 >= HUGE_C ? BIGE : s->c7 + ALPHA * s->c8;
        slot[r] = r;
    }
    for (int t = 0; t < NREP; t++) Tt[t] = NREP > 1 ? Tmin * pow(Tmax / Tmin, t / (NREP - 1.0)) : Tmin;

    long best = LONG_MAX; long it = 0; double st = now(), lastp = 0, el = 0; int done = 0;
    printf("pt group N=%d id=%d p=%d n=%d reps=%d T=[%.2f,%.2f] alpha=%.3f D=%d\n", N, want, p, n, NREP, Tmin, Tmax, ALPHA, D);
    fflush(stdout);
    while (!done) {
        for (int t = 0; t < NREP && !done; t++) {
            St *s = &S[slot[t]]; double T = Tt[t];
            for (int sw = 0; sw < SWEEP; sw++) {
                int i = xr() % ne, j = xr() % ne;
                int si_v = s->ev[i], si_a = s->ea[i], sj_v = s->ev[j], sj_a = s->ea[j];
                if (xr() & 1) { s->ea[i] = xr() % N; }
                else { if (i == j || s->ev[i] == s->ev[j]) continue;
                    int tv = s->ev[i]; s->ev[i] = s->ev[j]; s->ev[j] = tv; if (xr() & 1) s->ea[i] = xr() % N; }
                long c7, c8; evalcost(s->ev, s->ea, &c7, &c8); it++;
                double E2 = c7 >= HUGE_C ? BIGE : c7 + ALPHA * c8;
                if (E2 <= s->E || ur() < exp((s->E - E2) / T)) {
                    s->E = E2; s->c7 = c7; s->c8 = c8;
                    if (c7 < best) { best = c7; el = now() - st;
                        printf("t=%.1f it=%ld best %ld (T=%.2f)\n", el, it, best, T); fflush(stdout);
                        if (best == 0) { write_sol(out, s->ev, s->ea, want); printf("FOUND\n"); done = 1; break; } }
                } else { s->ev[i] = si_v; s->ea[i] = si_a; s->ev[j] = sj_v; s->ea[j] = sj_a; }
            }
        }
        if (done) break;
        for (int t = 0; t + 1 < NREP; t++) {
            St *a = &S[slot[t]], *b = &S[slot[t + 1]];
            double d = (1.0 / Tt[t] - 1.0 / Tt[t + 1]) * (a->E - b->E);
            if (d >= 0 || ur() < exp(d)) { int tmp = slot[t]; slot[t] = slot[t + 1]; slot[t + 1] = tmp; }
        }
        el = now() - st;
        if (el - lastp >= 20) { lastp = el;
            printf("t=%.0f it=%ld best %ld | c7 by temperature:", el, it, best);
            for (int t = 0; t < NREP; t++) printf(" %ld", S[slot[t]].c7);
            printf("\n"); fflush(stdout); }
        if (el > secs) break;
    }
    printf("end best %ld its %ld time %.1f\n", best, it, now() - st);
    return 0;
}
