/* lift4 (d08, job beyond-d14 r2): simulated annealing over 4-regular bipartite voltage lifts of a p+p base multigraph,
   base AND voltages free, over the metacyclic group G = Z_m x|_r Z_k (order N = m k) given by formula.
   Group element index a*k+j <-> (a,j); (a,j)(b,l) = (a + r^j b mod m, j+l mod k); identity = index 0.
   Base: whites 0..p-1, blacks p..2p-1, 4p base edges (eu,ev,ea), ea = group index of the voltage.
   Lift: vertex u*N+g; (u,g) ~ (v, g*a) for base edge (u,v,a); from the black side (v,h) ~ (u, h*a^-1).
   Left multiplication is semiregular, so BFS from the 2p roots (u,e) gives the exact cost:
   cost = #(root, vertex) pairs at distance > D (D env, default 14). Lift is simple iff no two base edges share (u,v,a).
   Usage: lift4 p m k r seconds seed OUT [T0 T1]
   env: D (14), START=file (header "m k r p cost", then 4p lines "eu ev ea"), IDLE (restart from best after this many
   non-improving moves, default 4000), EVAL=file (print cost of that file and exit).
   Writes OUT.best on each improvement, OUT (header "m k r p 0") on cost 0.  Build: gcc -O3 -march=native -o lift4 lift4.c -lm */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#define P2MAX 8
#define DG 5
#include <string.h>
#include <math.h>
#include <time.h>

static int p, P2, m, k, r, N, D = 14, IDLE = 4000;
static int eu[16], ev[16], ea[16], ne;
static int bu[16], bv[16], ba[16];
static uint8_t *R, *R2;
static int *nbr, *gA, *gJ, *Rj, *Ri;
static int dv[16][DG], da[16][DG];
static uint64_t rng = 88172645463325252ULL;
static inline uint64_t xr(void) { rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; return rng; }
static inline double ur(void) { return (xr() >> 11) * (1.0 / 9007199254740992.0); }

static inline int ginv(int g) {
    int a = gA[g], j = gJ[g], jj = (k - j) % k;
    int64_t c = ((int64_t)(m - a) % m) * (int64_t)Rj[jj] % m;
    return (int)c * k + jj;
}

static long cost(void) {
    for (int e = 0; e < ne; e++) for (int f = e + 1; f < ne; f++)
        if (eu[e] == eu[f] && ev[e] == ev[f] && ea[e] == ea[f]) return 1L << 40;
    int n = P2 * N, dg[16] = {0};
    for (int e = 0; e < ne; e++) {
        int u = eu[e], v = ev[e];
        dv[u][dg[u]] = v; da[u][dg[u]++] = ea[e];
        dv[v][dg[v]] = u; da[v][dg[v]++] = ginv(ea[e]);
    }
    /* (u,g) ~ (v, g*c) with c = (b,i): g*c = ((a + r^j b) mod m, (j+i) mod k) for g = (a,j) */
    static int T[4096], S[4096];
    for (int u = 0; u < P2; u++) for (int t = 0; t < DG; t++) {
        int c = da[u][t], b = gA[c], i = gJ[c], v = dv[u][t];
        for (int j = 0; j < k; j++) { T[j] = (int)((int64_t)Rj[j] * b % m); S[j] = (j + i) % k; }
        int *out = nbr + (long)u * N * DG + t;
        for (int a = 0; a < m; a++) for (int j = 0; j < k; j++) {
            int x = a + T[j]; if (x >= m) x -= m;
            *out = v * N + x * k + S[j]; out += DG;
        }
    }
    memset(R, 0, (size_t)n);
    for (int u = 0; u < P2; u++) R[u * N] = (uint8_t)(1u << u);
    for (int t = 0; t < D; t++) {
        for (int x = 0; x < n; x++) {
            const int *q = nbr + DG * (long)x;
            R2[x] = R[x] | R[q[0]] | R[q[1]] | R[q[2]] | R[q[3]] | R[q[4]];
        }
        uint8_t *tmp = R; R = R2; R2 = tmp;
    }
    uint8_t full = (uint8_t)((1u << P2) - 1); long c = 0;
    for (int x = 0; x < n; x++) c += __builtin_popcount((unsigned)(uint8_t)(~R[x] & full));
    return c;
}

static void writefile(const char *fn, long c, int *U, int *V, int *A) {
    FILE *f = fopen(fn, "w"); if (!f) return;
    fprintf(f, "%d %d %d %d %ld\n", m, k, r, p, c);
    for (int e = 0; e < ne; e++) fprintf(f, "%d %d %d\n", U[e], V[e], A[e]);
    fclose(f);
}

int main(int argc, char **argv) {
    if (argc < 8) { fprintf(stderr, "usage: lift4 p m k r seconds seed OUT [T0 T1]\n"); return 2; }
    p = atoi(argv[1]); P2 = 2 * p; m = atoi(argv[2]); k = atoi(argv[3]); r = atoi(argv[4]);
    double secs = atof(argv[5]); rng ^= (uint64_t)atoll(argv[6]) * 0x9E3779B97F4A7C15ULL; xr(); xr();
    const char *out = argv[7];
    double T0 = argc > 8 ? atof(argv[8]) : 8.0, T1 = argc > 9 ? atof(argv[9]) : 1.0;
    if (getenv("D")) D = atoi(getenv("D"));
    if (getenv("IDLE")) IDLE = atoi(getenv("IDLE"));
    N = m * k; ne = DG * p;
    if (k > 4096 || P2 > P2MAX || 1L * m * k > 2000000000L) return 2;
    Rj = malloc(sizeof(int) * k); Ri = malloc(sizeof(int) * k);
    { int64_t x = 1 % m; for (int j = 0; j < k; j++) { Rj[j] = (int)x; x = x * r % m; } }
    if (((int64_t)Rj[0] * 1) != 1 % m || (int64_t)Rj[0] != 1 % m) return 2;
    { int64_t x = 1 % m; for (int j = 0; j < k; j++) x = x * r % m; if (x != 1 % m) { fprintf(stderr, "r^k != 1 mod m\n"); return 2; } }
    gA = malloc(sizeof(int) * N); gJ = malloc(sizeof(int) * N);
    for (int g = 0; g < N; g++) { gA[g] = g / k; gJ[g] = g % k; }
    int n = P2 * N; R = malloc((size_t)n); R2 = malloc((size_t)n); nbr = malloc(sizeof(int) * (long)DG * n);
    if (getenv("EVAL")) {
        FILE *fs = fopen(getenv("EVAL"), "r"); int hm, hk, hr, hp; long hc;
        if (!fs || fscanf(fs, "%d %d %d %d %ld", &hm, &hk, &hr, &hp, &hc) != 5 || hm != m || hk != k || hp != p) { fprintf(stderr, "bad EVAL\n"); return 2; }
        for (int e = 0; e < ne; e++) if (fscanf(fs, "%d %d %d", &eu[e], &ev[e], &ea[e]) != 3) return 2;
        fclose(fs); printf("EVAL cost %ld\n", cost()); return 0;
    }
    /* initial state: 4 random perfect matchings of whites to blacks, random voltages (no duplicate edges) */
    if (getenv("START")) {
        FILE *fs = fopen(getenv("START"), "r"); int hm, hk, hr, hp; long hc;
        if (!fs || fscanf(fs, "%d %d %d %d %ld", &hm, &hk, &hr, &hp, &hc) != 5 || hm != m || hk != k || hp != p) { fprintf(stderr, "bad START\n"); return 2; }
        for (int e = 0; e < ne; e++) if (fscanf(fs, "%d %d %d", &eu[e], &ev[e], &ea[e]) != 3) { fprintf(stderr, "bad START\n"); return 2; }
        fclose(fs);
    } else {
        for (;;) {
            int e = 0;
            for (int mm = 0; mm < DG; mm++) {
                int pm[16]; for (int i = 0; i < p; i++) pm[i] = p + i;
                for (int i = p - 1; i > 0; i--) { int j = xr() % (i + 1); int t = pm[i]; pm[i] = pm[j]; pm[j] = t; }
                for (int i = 0; i < p; i++) { eu[e] = i; ev[e] = pm[i]; ea[e] = xr() % N; e++; }
            }
            if (cost() < (1L << 40)) break;
        }
    }
    long c = cost(), best = c;
    if (c == 0) { writefile(out, 0, eu, ev, ea); printf("FOUND at start\n"); }
    int bestU[16], bestV[16], bestA[16];
    memcpy(bestU, eu, sizeof eu); memcpy(bestV, ev, sizeof ev); memcpy(bestA, ea, sizeof ea);
    clock_t st = clock(); double cyc = 30.0; long it = 0, idle = 0;
    if (c == 0) { printf("end best 0 its 0\n"); return 0; }
    printf("lift4 p=%d m=%d k=%d r=%d N=%d n=%d D=%d start %ld\n", p, m, k, r, N, n, D, c); fflush(stdout);
    for (;;) {
        double el = (double)(clock() - st) / CLOCKS_PER_SEC; if (el > secs) break;
        double T = T0 * pow(T1 / T0, fmod(el, cyc) / cyc);
        int i = xr() % ne, j = xr() % ne;
        int si_v = ev[i], si_a = ea[i], sj_v = ev[j], sj_a = ea[j];
        if (xr() & 1) { ea[i] = xr() % N; }
        else {
            if (i == j || ev[i] == ev[j]) continue;
            int t = ev[i]; ev[i] = ev[j]; ev[j] = t;
            if (xr() & 1) ea[i] = xr() % N;
        }
        long c2 = cost(); it++; idle++;
        if (c2 <= c || ur() < exp((double)(c - c2) / T)) {
            c = c2;
            if (c < best) {
                best = c; idle = 0;
                printf("t=%.1f it=%ld best %ld\n", el, it, best); fflush(stdout);
                memcpy(bestU, eu, sizeof eu); memcpy(bestV, ev, sizeof ev); memcpy(bestA, ea, sizeof ea);
                char bp[600]; snprintf(bp, sizeof bp, "%s.best", out); writefile(bp, best, eu, ev, ea);
                if (best == 0) { writefile(out, 0, eu, ev, ea); printf("FOUND\n"); break; }
            }
        } else { ev[i] = si_v; ea[i] = si_a; ev[j] = sj_v; ea[j] = sj_a; }
        if (idle > IDLE) { /* restart from best */
            memcpy(eu, bestU, sizeof eu); memcpy(ev, bestV, sizeof ev); memcpy(ea, bestA, sizeof ea);
            c = best; idle = 0;
        }
    }
    printf("end best %ld its %ld\n", best, it);
    return 0;
}
