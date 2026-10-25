/* lift_anneal.c (card c7): cyclic voltage lifts of a bipartite base graph B to diameter <= D.
 * Base B: vertices 0..NB-1, side 0 = points (vertex 0 is a point), side 1 = lines; edges "u v tree" (u point).
 * Lift vertex (x,g), g in Z_m.  Base edge p->L with voltage w: (p,g) ~ (L,g+w), i.e. L->p carries -w.
 * Translation g -> g+h is an automorphism acting semiregularly, so the lift diameter is exactly
 *   max over base x of ecc((x,0))  (transitivity check; all-pairs check is done separately by verify_lift.c).
 * Cost = number of ordered pairs (source (x,0), target (y,g)) at distance > D, computed by bit-parallel BFS
 * (64 base sources per batch, one bit per source; frontier/visited arrays of NB*m words).
 * Tree edges are fixed to voltage 0 (WLOG for abelian groups).  Simulated annealing on non-tree voltages.
 * usage: lift_anneal base.txt m D iters T0 T1 seed out.sol [in.sol]
 * out.sol: first line "m D", then one voltage per base edge (base file order).
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>

static int NB, E, m, D;
static int *eu, *ev, *et, *w, *side, *adjStart, *adjY, *adjE, *nontree, nnt;
static uint64_t *A, *B, *V;
static size_t TOT;
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline double urand(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static long long evaluate(void) {
    long long total = 0;
    for (int b0 = 0; b0 < NB; b0 += 64) {
        int ns = NB - b0 < 64 ? NB - b0 : 64;
        uint64_t lanemask = ns == 64 ? ~0ULL : ((1ULL << ns) - 1);
        memset(V, 0, TOT * 8);
        memset(A, 0, TOT * 8);
        for (int k = 0; k < ns; k++) { size_t idx = (size_t)(b0 + k) * m; V[idx] |= 1ULL << k; A[idx] |= 1ULL << k; }
        uint64_t *fr = A, *nx = B;
        for (int lev = 1; lev <= D; lev++) {
            memset(nx, 0, TOT * 8);
            for (int x = 0; x < NB; x++) {
                uint64_t *dst = nx + (size_t)x * m;
                for (int k = adjStart[x]; k < adjStart[x + 1]; k++) {
                    int y = adjY[k];
                    int s = (side[x] == 0) ? w[adjE[k]] : (m - w[adjE[k]]) % m;   /* dst[g] |= fr_y[g+s] */
                    const uint64_t *src = fr + (size_t)y * m;
                    int lim = m - s;
                    for (int g = 0; g < lim; g++) dst[g] |= src[g + s];
                    for (int g = lim; g < m; g++) dst[g] |= src[g + s - m];
                }
            }
            uint64_t any = 0;
            for (size_t i = 0; i < TOT; i++) { uint64_t a = nx[i] & ~V[i]; nx[i] = a; V[i] |= a; any |= a; }
            uint64_t *t = fr; fr = nx; nx = t;
            if (!any) break;
        }
        for (size_t i = 0; i < TOT; i++) total += ns - __builtin_popcountll(V[i] & lanemask);
    }
    return total;
}

static void save(const char *path, long long cost) {
    FILE *f = fopen(path, "w");
    fprintf(f, "%d %d\n", m, D);
    for (int e = 0; e < E; e++) fprintf(f, "%d\n", w[e]);
    fprintf(f, "# cost %lld\n", cost);
    fclose(f);
}

int main(int argc, char **argv) {
    if (argc < 9) { fprintf(stderr, "usage: lift_anneal base.txt m D iters T0 T1 seed out.sol [in.sol]\n"); return 1; }
    FILE *f = fopen(argv[1], "r");
    if (fscanf(f, "%d %d", &NB, &E) != 2) return 2;
    eu = malloc(E * sizeof(int)); ev = malloc(E * sizeof(int)); et = malloc(E * sizeof(int));
    for (int e = 0; e < E; e++) if (fscanf(f, "%d %d %d", &eu[e], &ev[e], &et[e]) != 3) return 2;
    fclose(f);
    m = atoi(argv[2]); D = atoi(argv[3]);
    long long iters = atoll(argv[4]); double T0 = atof(argv[5]), T1 = atof(argv[6]);
    rs ^= (uint64_t)atoll(argv[7]) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 20; i++) rnd();
    const char *outp = argv[8];
    /* 2-colouring: side[0] = 0, neighbours get the opposite colour */
    side = malloc(NB * sizeof(int)); for (int x = 0; x < NB; x++) side[x] = -1;
    int *deg = calloc(NB, sizeof(int));
    for (int e = 0; e < E; e++) { deg[eu[e]]++; deg[ev[e]]++; }
    adjStart = malloc((NB + 1) * sizeof(int)); adjStart[0] = 0;
    for (int x = 0; x < NB; x++) adjStart[x + 1] = adjStart[x] + deg[x];
    adjY = malloc(2 * E * sizeof(int)); adjE = malloc(2 * E * sizeof(int));
    int *fill = calloc(NB, sizeof(int));
    for (int e = 0; e < E; e++) {
        int u = eu[e], v = ev[e];
        adjY[adjStart[u] + fill[u]] = v; adjE[adjStart[u] + fill[u]] = e; fill[u]++;
        adjY[adjStart[v] + fill[v]] = u; adjE[adjStart[v] + fill[v]] = e; fill[v]++;
    }
    int *q = malloc(NB * sizeof(int)); int qh = 0, qt = 0; side[0] = 0; q[qt++] = 0;
    while (qh < qt) { int x = q[qh++]; for (int k = adjStart[x]; k < adjStart[x + 1]; k++) { int y = adjY[k]; if (side[y] < 0) { side[y] = 1 - side[x]; q[qt++] = y; } } }
    for (int e = 0; e < E; e++) if (side[eu[e]] != 0 || side[ev[e]] != 1) { fprintf(stderr, "base not bipartite with u=point\n"); return 3; }
    nontree = malloc(E * sizeof(int)); nnt = 0;
    for (int e = 0; e < E; e++) if (!et[e]) nontree[nnt++] = e;
    w = calloc(E, sizeof(int));
    if (argc >= 10) {
        FILE *g = fopen(argv[9], "r"); int mm, dd; if (fscanf(g, "%d %d", &mm, &dd) != 2 || mm != m) { fprintf(stderr, "bad in.sol\n"); return 4; }
        for (int e = 0; e < E; e++) if (fscanf(g, "%d", &w[e]) != 1) return 4;
        fclose(g);
    } else {
        for (int i = 0; i < nnt; i++) w[nontree[i]] = (int)(rnd() % m);
    }
    for (int e = 0; e < E; e++) if (et[e]) w[e] = 0;
    TOT = (size_t)NB * m;
    A = malloc(TOT * 8); B = malloc(TOT * 8); V = malloc(TOT * 8);
    long long cur = evaluate(), best = cur;
    fprintf(stderr, "m=%d n=%lld D=%d nontree=%d start cost=%lld\n", m, (long long)NB * m, D, nnt, cur);
    save(outp, best);
    for (long long it = 0; it < iters && best > 0; it++) {
        double T = T0 * pow(T1 / T0, (double)it / (double)iters);
        int e = nontree[rnd() % nnt];
        int old = w[e];
        int nw = (int)(rnd() % (m - 1)); if (nw >= old) nw++;   /* different value */
        w[e] = nw;
        long long c = evaluate();
        long long d = c - cur;
        if (d <= 0 || urand() < exp(-(double)d / T)) {
            cur = c;
            if (cur < best) { best = cur; save(outp, best); }
        } else w[e] = old;
        if (it % 500 == 0) fprintf(stderr, "it=%lld T=%.3f cur=%lld best=%lld\n", it, T, cur, best);
    }
    save(outp, best);
    printf("m=%d n=%lld D=%d final best cost=%lld (%s)\n", m, (long long)NB * m, D, best, best == 0 ? "ALL PAIRS WITHIN D" : "not yet");
    return 0;
}
