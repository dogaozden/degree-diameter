/* saliftt: salift_s (own-small) plus TARGETED voltage moves (job raise-small-d, director).
   Joint simulated annealing of a p+p cubic bipartite base multigraph and its voltages in a group G (table from gtab.py).
   Lift: vertex (u,g) = u*N + g; base edge e = (u,v,a), u white (< p), v black: (u,g) ~ (v, g*a).
   Cost (as salift_s) = #(root u, lifted vertex x) with dist((u,e), x) > D; left multiplication by G is a semiregular
   automorphism group with the fibres as orbits, so 0 means diameter <= D.
   Moves: plain (as salift_s: new random voltage on one edge, or swap the black ends of two edges) and, with
   probability TARGP %, a targeted move: take a far pair (u, x = (w,h)) of the current state, draw a random
   non-backtracking base walk u -> w of length L in {D, D-1} (the parity of the side change), choose a position i whose
   edge occurs once in the walk, and set that edge's voltage so the lifted walk from (u,e) ends exactly at x:
     s_1 ... s_L = h  =>  s_i = (s_1...s_{i-1})^-1 h (s_{i+1}...s_L)^-1   (s_j = a_e or a_e^-1 by direction).
   Metropolis on the exact cost for every move. Writes OUT.best on every improvement ("N id p cost" + 3p lines
   "u v a"), OUT at cost 0. Usage: saliftt p TAB id seed SECONDS [T0] [T1] [OUT]
   env: D (default 13), TARGP (default 30), START=file.best, CYC (cooling cycle in CPU s, default 30).
   Build: gcc -O3 -march=native -o saliftt saliftt.c -lm */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>

static int p, k, N, D = 13, *mul, *inv, ne;
static int eu[96], ev[96], ea[96];
static uint64_t *R, *R2; static int *nbr;
static uint64_t rng = 88172645463325252ULL;
static inline uint64_t xr(void) { rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; return rng; }
static inline double ur(void) { return (xr() >> 11) * (1.0 / 9007199254740992.0); }
static int *farU, *farX, nfar; static int maxfar = 4096;

static long cost(void) {
    for (int e = 0; e < ne; e++) for (int f = e + 1; f < ne; f++)
        if (eu[e] == eu[f] && ev[e] == ev[f] && ea[e] == ea[f]) return 1L << 40;
    int n = k * N, dg[64] = {0};
    static int dv[64][3], da[64][3];
    for (int e = 0; e < ne; e++) { int u = eu[e], v = ev[e];
        dv[u][dg[u]] = v; da[u][dg[u]++] = ea[e]; dv[v][dg[v]] = u; da[v][dg[v]++] = inv[ea[e]]; }
    for (int u = 0; u < k; u++) for (int g = 0; g < N; g++) for (int j = 0; j < 3; j++)
        nbr[(u * N + g) * 3 + j] = dv[u][j] * N + mul[(long)g * N + da[u][j]];
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
/* far pairs of the state whose cost() ran last (R holds its reach sets) */
static void collect_far(void) {
    int n = k * N; uint64_t full = k == 64 ? ~0ULL : (1ULL << k) - 1; nfar = 0;
    for (int x = 0; x < n && nfar < maxfar; x++) { uint64_t m = ~R[x] & full;
        while (m && nfar < maxfar) { int u = __builtin_ctzll(m); m &= m - 1; farU[nfar] = u; farX[nfar] = x; nfar++; } }
}
/* targeted move; returns 1 if a voltage was changed (old value in *se, *sa) */
static int targeted(int *se, int *sa) {
    if (nfar == 0) return 0;
    int t = xr() % nfar, u = farU[t], x = farX[t], w = x / N, h = x % N;
    int sameside = (u < p) == (w < p);
    int L = D; if ((L % 2 == 0) != sameside) L--;
    if (L < 1) return 0;
    /* incidence lists of the base */
    int inc[64][3], dir[64][3], dg[64] = {0};
    for (int e = 0; e < ne; e++) { inc[eu[e]][dg[eu[e]]] = e; dir[eu[e]][dg[eu[e]]++] = 0;
                                   inc[ev[e]][dg[ev[e]]] = e; dir[ev[e]][dg[ev[e]]++] = 1; }
    int we[64], wd[64];
    for (int tries = 0; tries < 200; tries++) {
        int cur = u, last = -1, ok = 1;
        for (int j = 0; j < L; j++) {
            int c, tt = 0;
            do { c = xr() % 3; tt++; } while (inc[cur][c] == last && tt < 20);
            if (inc[cur][c] == last) { ok = 0; break; }
            int e = inc[cur][c]; we[j] = e; wd[j] = dir[cur][c]; last = e;
            cur = dir[cur][c] == 0 ? ev[e] : eu[e];
        }
        if (!ok || cur != w) continue;
        int pos[64], np = 0;
        for (int j = 0; j < L; j++) { int cnt = 0; for (int l = 0; l < L; l++) cnt += we[l] == we[j]; if (cnt == 1) pos[np++] = j; }
        if (!np) continue;
        int i = pos[xr() % np];
        int pre = 0; for (int j = 0; j < i; j++) { int s = wd[j] == 0 ? ea[we[j]] : inv[ea[we[j]]]; pre = mul[(long)pre * N + s]; }
        int suf = 0; for (int j = i + 1; j < L; j++) { int s = wd[j] == 0 ? ea[we[j]] : inv[ea[we[j]]]; suf = mul[(long)suf * N + s]; }
        int si = mul[(long)mul[(long)inv[pre] * N + h] * N + inv[suf]];
        int e = we[i]; *se = e; *sa = ea[e];
        ea[e] = wd[i] == 0 ? si : inv[si];
        return ea[e] != *sa;
    }
    return 0;
}
int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: saliftt p TAB id seed SECONDS [T0] [T1] [OUT]\n"); return 2; }
    p = atoi(argv[1]); k = 2 * p; int want = atoi(argv[3]);
    rng ^= (uint64_t)atoll(argv[4]) * 0x9E3779B97F4A7C15ULL; xr(); xr();
    double secs = atof(argv[5]), T0 = argc > 6 ? atof(argv[6]) : 10.0, T1 = argc > 7 ? atof(argv[7]) : 0.3;
    const char *out = argc > 8 ? argv[8] : "best.sol";
    if (getenv("D")) D = atoi(getenv("D"));
    int targp = getenv("TARGP") ? atoi(getenv("TARGP")) : 30;
    double cyc = getenv("CYC") ? atof(getenv("CYC")) : 30.0;
    FILE *fg = fopen(argv[2], "r"); char tag[8], name[256]; int gid, found = 0;
    while (fscanf(fg, "%7s %d %d %255s", tag, &N, &gid, name) == 4) {
        mul = malloc(sizeof(int) * (long)N * N);
        for (long i = 0; i < (long)N * N; i++) if (fscanf(fg, "%d", &mul[i]) != 1) return 3;
        if (gid == want) { found = 1; break; }
        free(mul);
    }
    if (!found) { fprintf(stderr, "group not found\n"); return 2; }
    inv = malloc(sizeof(int) * N);
    for (int a = 0; a < N; a++) for (int b = 0; b < N; b++) if (mul[(long)a * N + b] == 0) inv[a] = b;
    int n = k * N; R = malloc(8L * n); R2 = malloc(8L * n); nbr = malloc(sizeof(int) * 3 * n);
    farU = malloc(sizeof(int) * maxfar); farX = malloc(sizeof(int) * maxfar);
    ne = 0;
    for (int m = 0; m < 3; m++) { int pm[32]; for (int i = 0; i < p; i++) pm[i] = i;
        for (int i = p - 1; i > 0; i--) { int j = xr() % (i + 1); int t = pm[i]; pm[i] = pm[j]; pm[j] = t; }
        for (int i = 0; i < p; i++) { eu[ne] = i; ev[ne] = p + pm[i]; ea[ne] = xr() % N; ne++; } }
    if (getenv("START")) { FILE *fs = fopen(getenv("START"), "r"); int sN, sg, sp; char hl[256];
        if (!fs || !fgets(hl, sizeof hl, fs) || sscanf(hl, "%d %d %d", &sN, &sg, &sp) < 3 || sN != N || sp != p) { fprintf(stderr, "bad START\n"); return 2; }
        for (int e = 0; e < ne; e++) if (fscanf(fs, "%d %d %d", &eu[e], &ev[e], &ea[e]) != 3) { fprintf(stderr, "bad START\n"); return 2; }
        fclose(fs); }
    long c = cost(), best = c; collect_far(); clock_t st = clock(); long it = 0, nt = 0, at = 0;
    printf("group N=%d id=%d %s p=%d n=%d D=%d start %ld\n", N, gid, name, p, n, D, c); fflush(stdout);
    char bp[600]; snprintf(bp, sizeof bp, "%s.best", out);
    for (;;) {
        double el = (double)(clock() - st) / CLOCKS_PER_SEC; if (el > secs) break;
        double T = T0 * pow(T1 / T0, fmod(el, cyc) / cyc);
        int i = xr() % ne, j = xr() % ne, sv[4] = {ev[i], ea[i], ev[j], ea[j]}, ist = 0, te = -1, ta = 0;
        if ((int)(xr() % 100) < targp) { ist = targeted(&te, &ta); if (!ist) continue; nt++; }
        else if (xr() & 1) { ea[i] = xr() % N; }
        else { if (i == j || ev[i] == ev[j]) continue; int t = ev[i]; ev[i] = ev[j]; ev[j] = t; if (xr() & 1) ea[i] = xr() % N; }
        long c2 = cost(); it++;
        if (c2 <= c || ur() < exp((c - c2) / T)) {
            if (ist) at++;
            c = c2; collect_far();
            if (c < best) { best = c; printf("t=%.1f it=%ld best %ld (targeted %ld/%ld)\n", el, it, best, at, nt); fflush(stdout);
                FILE *fb = fopen(bp, "w"); fprintf(fb, "%d %d %d %ld\n", N, gid, p, best);
                for (int e = 0; e < ne; e++) fprintf(fb, "%d %d %d\n", eu[e], ev[e], ea[e]); fclose(fb);
                if (best == 0) { FILE *f = fopen(out, "w"); fprintf(f, "%d %d %d\n", N, gid, p);
                    for (int e = 0; e < ne; e++) fprintf(f, "%d %d %d\n", eu[e], ev[e], ea[e]); fclose(f); printf("FOUND\n"); break; } }
        } else if (ist) { ea[te] = ta; }
        else { ev[i] = sv[0]; ea[i] = sv[1]; ev[j] = sv[2]; ea[j] = sv[3]; }
    }
    printf("end best %ld its %ld targeted %ld accepted %ld\n", best, it, nt, at);
    return 0;
}
