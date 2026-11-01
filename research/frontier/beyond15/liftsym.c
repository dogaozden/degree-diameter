/* liftsym.c — symmetric cyclic voltage lifts (job beyond-d15, director, 2026-11-01).
 *
 * Base B: bipartite cubic (or any regular degree <= 8) graph, sides 0..h-1 and h..2h-1 (lift.c format: first line the
 * number of vertices, then "u v" lines).  rho: an automorphism of B preserving the sides (permutation file: the images
 * of 0..b-1 on one or more lines), of order k.  lambda: a unit mod n with lambda^k = 1 (mod n).
 * Voltages x_e in Z_n are EQUIVARIANT: x_{rho(e)} = lambda x_e (with a sign when rho reverses the stored orientation),
 * so the lift B x_x Z_n has the automorphisms (v,g) -> (v,g+c) and (v,g) -> (rho v, lambda g), a group Z_n x|_lambda Z_k
 * acting with b/k vertex orbits (lambda = 1: Z_n x Z_k).  One free voltage per rho-orbit of edges: the orbit idea
 * (S closed under an automorphism) moved to lifts.  Heawood with rho of order 7 gives exactly the Haar graphs of
 * Z_n x|_lambda Z_7; GP(10,3) with rho = rotation by 2 (order 5) gives 4-orbit graphs of Z_n x|_lambda Z_5.
 * Cost = sum over rho-orbit representatives s of #{lift vertices at distance > D from (s,0)} (0 iff diameter <= D).
 * Search: Metropolis over orbit voltages (one orbit voltage re-drawn per move; T from T0 to T1 over L evaluations,
 * reheats to T0 after REHEAT evaluations without gain), and with SCAN=1 an exhaustive 1-opt sweep over all orbit
 * voltages (all n values each) whenever the anneal has stalled, taking the best move (tabu on the last 4 orbits).
 * Usage: liftsym BASE PERM n lambda D seconds seed OUTPREFIX     env T0 (2) T1 (0.05) L (2000) REHEAT (4000) SCAN (1)
 *        START=<voltage file "e x" lines, full edge list as written by this program>
 * Output: OUTPREFIX.best (voltages of all edges, "e x"), OUTPREFIX.edges when cost 0 (first line N, then "u v").
 * Check: research/lifts/coordinator_check/apsp.c on the .edges file.
 * Build: gcc -O3 -march=native -o liftsym liftsym.c -lm */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>
#define MAXE 2048
#define MAXV 512
#define MAXDEG 8
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }
static int b, E, n, D, deg; static long N;
static int eu[MAXE], ev[MAXE], volt[MAXE];
static int inc[MAXV][MAXDEG], sgn[MAXV][MAXDEG], dg[MAXV];
static int perm[MAXV], kord;
static long lam;
/* edge orbits */
static int norb, orbrep[MAXE], orbof[MAXE];
static long coef[MAXE];        /* volt[e] = coef[e] * x_{orb(e)} mod n (coef = +-lambda^i) */
static int ox[MAXE];           /* orbit voltages */
static int nsrc, src[MAXV];    /* rho-orbit representatives of vertices */
static int *vis, stamp = 0, *qu;
static int find_edge(int u, int w, int *s) {
    for (int e = 0; e < E; e++) { if (eu[e] == u && ev[e] == w) { *s = 1; return e; } if (eu[e] == w && ev[e] == u) { *s = -1; return e; } }
    return -1;
}
static void apply(void) { for (int e = 0; e < E; e++) volt[e] = (int)(((coef[e] % n + n) % n) * ox[orbof[e]] % n); }
static long cost_one(int s, long stopat) {
    stamp++; int head = 0, tail = 0; long x0 = (long)s * n;
    vis[x0] = stamp; qu[tail++] = (int)x0;
    for (int lev = 0; lev < D && head < tail; lev++) {
        int end = tail;
        for (; head < end; head++) {
            long x = qu[head]; int w0 = (int)(x / n), g = (int)(x % n);
            for (int kk = 0; kk < dg[w0]; kk++) {
                int e = inc[w0][kk], sg = sgn[w0][kk];
                int w = sg > 0 ? ev[e] : eu[e];
                int sh = sg > 0 ? volt[e] : (n - volt[e]) % n;
                int gg = g + sh; if (gg >= n) gg -= n;
                long y = (long)w * n + gg;
                if (vis[y] != stamp) { vis[y] = stamp; qu[tail++] = (int)y; }
            }
        }
    }
    (void)stopat;
    return N - tail;
}
static long cost(long stopat) {
    apply(); long t = 0;
    for (int i = 0; i < nsrc; i++) { t += cost_one(src[i], stopat); if (t > stopat) return t; }
    return t;
}
static void save(const char *pre, const char *suf) {
    char fn[512]; snprintf(fn, sizeof fn, "%s%s", pre, suf); FILE *f = fopen(fn, "w");
    for (int e = 0; e < E; e++) fprintf(f, "%d %d\n", e, volt[e]); fclose(f);
}
static void save_edges(const char *pre) {
    char fn[512]; snprintf(fn, sizeof fn, "%s.edges", pre); FILE *f = fopen(fn, "w");
    fprintf(f, "%ld\n", N);
    for (int e = 0; e < E; e++) for (int g = 0; g < n; g++) fprintf(f, "%ld %ld\n", (long)eu[e] * n + g, (long)ev[e] * n + (g + volt[e]) % n);
    fclose(f);
}
int main(int argc, char **argv) {
    if (argc < 9) { fprintf(stderr, "usage: liftsym BASE PERM n lambda D seconds seed OUTPREFIX\n"); return 1; }
    FILE *f = fopen(argv[1], "r"); if (!f || fscanf(f, "%d", &b) != 1) { fprintf(stderr, "bad base\n"); return 1; }
    int u, w; E = 0; while (fscanf(f, "%d %d", &u, &w) == 2) { eu[E] = u < w ? u : w; ev[E] = u < w ? w : u; E++; } fclose(f);
    int h = b / 2;
    for (int e = 0; e < E; e++) if (!(eu[e] < h && ev[e] >= h)) { fprintf(stderr, "edge %d not across sides 0..%d / %d..%d\n", e, h - 1, h, b - 1); return 1; }
    for (int v = 0; v < b; v++) dg[v] = 0;
    for (int e = 0; e < E; e++) { inc[eu[e]][dg[eu[e]]] = e; sgn[eu[e]][dg[eu[e]]++] = 1; inc[ev[e]][dg[ev[e]]] = e; sgn[ev[e]][dg[ev[e]]++] = -1; }
    deg = dg[0]; for (int v = 0; v < b; v++) if (dg[v] != deg) { fprintf(stderr, "base not regular\n"); return 1; }
    f = fopen(argv[2], "r"); for (int v = 0; v < b; v++) if (!f || fscanf(f, "%d", &perm[v]) != 1) { fprintf(stderr, "bad perm\n"); return 1; } fclose(f);
    n = atoi(argv[3]); lam = atol(argv[4]); D = atoi(argv[5]); double secs = atof(argv[6]); rs ^= (uint64_t)atoll(argv[7]) * 0x9E3779B97F4A7C15ULL; const char *pre = argv[8];
    for (int i = 0; i < 10; i++) rnd();
    N = (long)b * n;
    /* rho: check automorphism + side preserving, order */
    for (int v = 0; v < b; v++) if ((v < h) != (perm[v] < h)) { fprintf(stderr, "rho does not preserve sides\n"); return 1; }
    for (int e = 0; e < E; e++) { int s; if (find_edge(perm[eu[e]], perm[ev[e]], &s) < 0) { fprintf(stderr, "rho is not an automorphism\n"); return 1; } }
    { int cur[MAXV]; for (int v = 0; v < b; v++) cur[v] = v; kord = 0;
      do { for (int v = 0; v < b; v++) cur[v] = perm[cur[v]]; kord++; int id = 1; for (int v = 0; v < b; v++) if (cur[v] != v) id = 0; if (id) break; } while (kord < 10000); }
    { long p = 1; for (int i = 0; i < kord; i++) p = p * lam % n; if (p != 1 % n) { fprintf(stderr, "lambda^%d != 1 mod %d\n", kord, n); return 1; } }
    /* edge orbits with coefficients */
    for (int e = 0; e < E; e++) orbof[e] = -1;
    norb = 0;
    for (int e = 0; e < E; e++) if (orbof[e] < 0) {
        int o = norb++; orbrep[o] = e; orbof[e] = o; coef[e] = 1;
        int cu = eu[e], cw = ev[e]; long c = 1;   /* current oriented edge (cu -> cw) carries c * x */
        for (int i = 1; i <= kord; i++) {
            cu = perm[cu]; cw = perm[cw]; c = c * lam % n; int s; int e2 = find_edge(cu, cw, &s);
            long cc = s > 0 ? c : (n - c) % n;
            if (orbof[e2] < 0) { orbof[e2] = o; coef[e2] = cc; }
            else if (orbof[e2] == o && coef[e2] != cc) {   /* orbit closes inconsistently: x must satisfy (coef - cc) x = 0 */
                fprintf(stderr, "edge orbit %d is short and forces a relation; not supported (choose another rho)\n", o); return 1;
            }
        }
    }
    /* vertex orbit representatives */
    { int seen[MAXV] = {0}; nsrc = 0;
      for (int v = 0; v < b; v++) if (!seen[v]) { src[nsrc++] = v; int x = v; do { seen[x] = 1; x = perm[x]; } while (x != v); } }
    vis = calloc(N, sizeof(int)); qu = malloc(sizeof(int) * N);
    double T0 = getenv("T0") ? atof(getenv("T0")) : 2.0, T1 = getenv("T1") ? atof(getenv("T1")) : 0.05;
    long L = getenv("L") ? atol(getenv("L")) : 2000, REHEAT = getenv("REHEAT") ? atol(getenv("REHEAT")) : 4000;
    int SCAN = getenv("SCAN") ? atoi(getenv("SCAN")) : 1;
    for (int o = 0; o < norb; o++) ox[o] = (int)(rnd() % n);
    if (getenv("START")) {
        FILE *s = fopen(getenv("START"), "r"); int e, x; int got[MAXE] = {0};
        while (s && fscanf(s, "%d %d", &e, &x) == 2) if (e >= 0 && e < E && e == orbrep[orbof[e]]) { ox[orbof[e]] = ((x % n) + n) % n; got[orbof[e]] = 1; }
        if (s) fclose(s);
    }
    if (getenv("GTEST")) {
        int va[MAXV], vi[MAXV]; for (int a = 0; a < nsrc; a++) { int x = src[a]; for (int i = 0; i < kord; i++) { va[x] = a; vi[x] = i; x = perm[x]; } }
        long lp[64]; lp[0] = 1 % n; for (int i = 1; i < 64; i++) lp[i] = lp[i - 1] * lam % n;
        for (int t = 0; t < 5; t++) {
            for (int o = 0; o < norb; o++) ox[o] = (int)(rnd() % n); long c0 = cost(1L << 60);
            long cc[MAXV]; for (int a = 0; a < nsrc; a++) cc[a] = rnd() % n; long u = 1 + rnd() % (n - 1);
            for (int o = 0; o < norb; o++) { int e = orbrep[o]; long cw = lp[vi[ev[e]]] * cc[va[ev[e]]] % n, cu = lp[vi[eu[e]]] * cc[va[eu[e]]] % n;
                ox[o] = (int)(((ox[o] + cw - cu) % n + n) % n * u % n); }
            long c1 = cost(1L << 60); fprintf(stderr, "GTEST %d: cost %ld after gauge+scaling %ld %s\n", t, c0, c1, c0 == c1 ? "ok" : "MISMATCH");
        }
        return 0;
    }
    if (getenv("EXH")) {   /* exhaustive over gauge classes: zero a maximal gauge-independent set of edge orbits, scale */
        /* vertex v = rho^i(src[a]): find (a, i) */
        int va[MAXV], vi[MAXV];
        for (int a = 0; a < nsrc; a++) { int x = src[a]; for (int i = 0; i < kord; i++) { va[x] = a; vi[x] = i; x = perm[x]; } }
        long lp[64]; lp[0] = 1 % n; for (int i = 1; i < 64; i++) lp[i] = lp[i - 1] * lam % n;
        /* gauge matrix rows: edge orbit o (rep edge u->w): c_w - c_u, with c_v = lambda^i c_a */
        static long M[MAXE][MAXV]; int piv[MAXE] = {0}, rank = 0; static long R[MAXV][MAXV + 1]; (void)R;
        for (int o = 0; o < norb; o++) { int e = orbrep[o]; for (int a = 0; a < nsrc; a++) M[o][a] = 0;
            M[o][va[ev[e]]] = (M[o][va[ev[e]]] + lp[vi[ev[e]]]) % n; M[o][va[eu[e]]] = (M[o][va[eu[e]]] + n - lp[vi[eu[e]]]) % n; }
        /* greedy row selection by elimination mod n (n prime assumed) */
        static long B[MAXE][MAXV]; int nb = 0;
        for (int o = 0; o < norb && rank < nsrc; o++) {
            long row[MAXV]; for (int a = 0; a < nsrc; a++) row[a] = M[o][a];
            for (int t = 0; t < nb; t++) { int pc = -1; for (int a = 0; a < nsrc; a++) if (B[t][a]) { pc = a; break; }
                if (pc >= 0 && row[pc]) { long f = row[pc]; for (int a = 0; a < nsrc; a++) row[a] = ((row[a] - f * B[t][a]) % n + n) % n; } }
            int pc = -1; for (int a = 0; a < nsrc; a++) if (row[a]) { pc = a; break; }
            if (pc < 0) continue;
            long iv = 1, bb = row[pc], ee = n - 2; while (ee) { if (ee & 1) iv = iv * bb % n; bb = bb * bb % n; ee >>= 1; }
            for (int a = 0; a < nsrc; a++) row[a] = row[a] * iv % n;
            /* keep B in reduced form so later rows reduce correctly */
            for (int t = 0; t < nb; t++) if (B[t][pc]) { long f = B[t][pc]; for (int a = 0; a < nsrc; a++) B[t][a] = ((B[t][a] - f * row[a]) % n + n) % n; }
            for (int a = 0; a < nsrc; a++) B[nb][a] = row[a]; nb++; piv[o] = 1; rank++;
        }
        int fr[MAXE], nf = 0; for (int o = 0; o < norb; o++) if (!piv[o]) fr[nf++] = o;
        fprintf(stderr, "EXH: %d edge orbits, gauge rank %d, %d free orbit voltages (first nonzero scaled to 1)\n", norb, rank, nf);
        for (int o = 0; o < norb; o++) ox[o] = 0;
        long bestc = 1L << 60, cnt = 0, nsol = 0; int bxx[MAXE]; double te = now();
        /* enumerate tuples over free orbits whose first nonzero entry is 1 */
        for (int lead = 0; lead < nf; lead++) {
            for (int o = 0; o < nf; o++) ox[fr[o]] = 0; ox[fr[lead]] = 1;
            int rest = nf - lead - 1; long tot = 1; for (int t = 0; t < rest; t++) tot *= n;
            for (long code = 0; code < tot; code++) {
                long c2 = code; for (int t = 0; t < rest; t++) { ox[fr[lead + 1 + t]] = (int)(c2 % n); c2 /= n; }
                long c = cost(bestc == 0 ? 0 : bestc); cnt++;
                if (c < bestc || c == 0) { if (c < bestc) { bestc = c; memcpy(bxx, ox, sizeof(int) * norb); }
                    if (c == 0) { nsol++; if (nsol == 1) { apply(); save(pre, ".best"); save_edges(pre); } } }
            }
        }
        memcpy(ox, bxx, sizeof(int) * norb); apply(); if (bestc > 0) save(pre, ".best");
        printf("EXHRESULT b=%d k=%d lambda=%ld n=%d N=%ld D=%d free=%d evals=%ld min_cost=%ld solutions=%ld secs=%.1f\n", b, kord, lam, n, N, D, nf, cnt, bestc, nsol, now() - te);
        return 0;
    }
    long cur = cost(1L << 60), best = cur; int bx[MAXE]; memcpy(bx, ox, sizeof(int) * norb);
    fprintf(stderr, "b=%d E=%d k=%d lambda=%ld n=%d N=%ld D=%d orbits: %d edge, %d vertex; start cost %ld\n", b, E, kord, lam, n, N, D, norb, nsrc, cur);
    save(pre, ".best");
    double t0 = now(); long evals = 1, since = 0; int tabu[4] = {-1, -1, -1, -1}, tp = 0;
    while (best > 0 && now() - t0 < secs) {
        double fr = (double)(since % L) / L; double T = T0 * pow(T1 / T0, fr);
        int o = (int)(rnd() % norb), old = ox[o]; ox[o] = (int)(rnd() % n);
        long c = cost(cur + (long)(T * 30) + 50); evals++; since++;
        if (c <= cur || exp((cur - c) / (T * (1 + cur * 0.02))) * 4294967296.0 > (double)(rnd() & 0xffffffffULL)) cur = c; else ox[o] = old;
        if (cur < best) { best = cur; memcpy(bx, ox, sizeof(int) * norb); since = 0; apply(); save(pre, ".best");
                          fprintf(stderr, "t=%.1f evals=%ld best=%ld\n", now() - t0, evals, best); }
        if (SCAN && since >= L) {   /* exhaustive 1-opt sweep from the best */
            memcpy(ox, bx, sizeof(int) * norb); long bc = best; int bo = -1, bv = -1;
            for (int oo = 0; oo < norb && now() - t0 < secs; oo++) {
                int skip = 0; for (int t = 0; t < 4; t++) if (tabu[t] == oo) skip = 1; if (skip) continue;
                int keep = ox[oo];
                for (int v = 0; v < n; v++) { if (v == keep) continue; ox[oo] = v; long c2 = cost(bc); evals++;
                    if (c2 < bc || (bo < 0 && c2 == bc && (rnd() & 7) == 0)) { bc = c2; bo = oo; bv = v; } }
                ox[oo] = keep;
            }
            if (bo >= 0) { ox[bo] = bv; tabu[tp++ & 3] = bo; cur = cost(1L << 60); evals++;
                           if (cur < best) { best = cur; memcpy(bx, ox, sizeof(int) * norb); apply(); save(pre, ".best");
                                             fprintf(stderr, "t=%.1f evals=%ld best=%ld (scan)\n", now() - t0, evals, best); } }
            since = 0;
            if (REHEAT && evals % REHEAT == 0) memcpy(ox, bx, sizeof(int) * norb);
        }
    }
    memcpy(ox, bx, sizeof(int) * norb); long fin = cost(1L << 60); apply(); save(pre, ".best");
    if (fin == 0) save_edges(pre);
    printf("RESULT b=%d k=%d lambda=%ld n=%d N=%ld D=%d best=%ld evals=%ld secs=%.1f\n", b, kord, lam, n, N, D, fin, evals, now() - t0);
    return 0;
}
