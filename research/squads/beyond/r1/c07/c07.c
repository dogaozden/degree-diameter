/* c07: Z_K lift of the incidence graph of W(q) (q=13) with two doubled matchings sigma, tau (degree q+1+4 = 18).
   Vertices: base 0..N-1 points, N..2N-1 lines; lift vertex = base*K + h.
   Base multigraph: every incidence (p,l) with voltage g (walk p->l adds g), plus for each point p two copies of
   {p, N+sigma(p)} and two copies of {p, N+tau(p)} with their own voltages (copies of one pair differ mod K).
   Lift diameter <= 5 iff for every base source s and every base vertex u, the voltages of walks of length <= 5
   from s to u cover Z_K (lift is a regular Z_K-cover, so sources (s,0) suffice).
   Cost = sum over sampled sources s, all u, of (K - popcount(U_s(u))).  Simulated annealing on single voltages.
   usage: c07 gq/gq_q13.bin K    env: SECS SEED NS T0 T1 OUT EMIT(=1 writes lift edge list to LIFT) */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>

static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline double urand(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int q, N, Q1, V, K, NE, ND;
static int *eu, *ev, *eg, *partner;          /* undirected base edges: point eu, line ev, voltage eg */
static int *dfrom, *dto, *dg;                /* directed edges 2e (u->v, g) and 2e+1 (v->u, -g) */
static uint64_t FULL;
static uint64_t *cur, *nxt, *U;

static inline uint64_t rot(uint64_t s, int g) {
    if (!g) return s;
    return ((s << g) | (s >> (K - g))) & FULL;
}
static inline void setv(int e, int g) {
    eg[e] = g; dg[2 * e] = g; dg[2 * e + 1] = (K - g) % K;
}

/* sum over sampled sources of uncovered (vertex, residue) pairs at lift distance <= 5 */
static long cost_src(const int *srcs, int ns, int *worst) {
    long total = 0;
    for (int si = 0; si < ns; si++) {
        int s = srcs[si];
        memset(cur, 0, sizeof(uint64_t) * V); memset(U, 0, sizeof(uint64_t) * V);
        cur[s] = 1; U[s] = 1;
        for (int step = 1; step <= 5; step++) {
            memset(nxt, 0, sizeof(uint64_t) * V);
            for (int d = 0; d < ND; d++) {
                uint64_t c = cur[dfrom[d]];
                if (c) nxt[dto[d]] |= rot(c, dg[d]);
            }
            uint64_t *t = cur; cur = nxt; nxt = t;
            for (int x = 0; x < V; x++) U[x] |= cur[x];
        }
        for (int x = 0; x < V; x++) {
            int miss = K - __builtin_popcountll(U[x]);
            total += miss;
        }
        (void)worst;
    }
    return total;
}

static int load_gq(const char *fn) {
    FILE *f = fopen(fn, "rb"); if (!f) { perror("gq"); return 0; }
    int32_t h[3]; if (fread(h, 4, 3, f) != 3) return 0;
    q = h[0]; N = h[1]; int L = h[2]; Q1 = q + 1;
    int32_t *lines = malloc(4L * L * Q1); if (fread(lines, 4, (size_t)L * Q1, f) != (size_t)L * Q1) return 0;
    fclose(f);
    if (L != N) return 0;
    V = 2 * N;
    NE = N * Q1 + 4 * N;                       /* incidences + 2 doubled matchings (2 copies each) */
    ND = 2 * NE;
    eu = malloc(sizeof(int) * NE); ev = malloc(sizeof(int) * NE); eg = malloc(sizeof(int) * NE); partner = malloc(sizeof(int) * NE);
    dfrom = malloc(sizeof(int) * ND); dto = malloc(sizeof(int) * ND); dg = malloc(sizeof(int) * ND);
    int e = 0;
    for (int l = 0; l < N; l++) for (int s = 0; s < Q1; s++) {
        int p = lines[l * Q1 + s];
        eu[e] = p; ev[e] = N + l; partner[e] = -1; e++;
    }
    free(lines);
    /* two random permutations sigma, tau : points -> lines, avoiding incidences and sigma(p)=tau(p) */
    int *inc = calloc((size_t)N * N, sizeof(int));
    {
        /* recover incidences from the edges already listed */
        for (int i = 0; i < N * Q1; i++) inc[(size_t)eu[i] * N + (ev[i] - N)] = 1;
    }
    int *sig = malloc(sizeof(int) * N), *tau = malloc(sizeof(int) * N);
    for (int p = 0; p < N; p++) sig[p] = p;
    for (int p = N - 1; p > 0; p--) { int j = rnd() % (p + 1); int t = sig[p]; sig[p] = sig[j]; sig[j] = t; }
    for (int p = 0; p < N; p++) if (inc[(size_t)p * N + sig[p]]) {
        for (int it = 0; it < 1000000; it++) { int p2 = rnd() % N; int a = sig[p], b = sig[p2];
            if (!inc[(size_t)p * N + b] && !inc[(size_t)p2 * N + a]) { sig[p] = b; sig[p2] = a; break; } }
    }
    for (int p = 0; p < N; p++) tau[p] = sig[p];
    for (int p = N - 1; p > 0; p--) { int j = rnd() % (p + 1); int t = tau[p]; tau[p] = tau[j]; tau[j] = t; }
    for (;;) {
        int bad = 0;
        for (int p = 0; p < N; p++) if (inc[(size_t)p * N + tau[p]] || tau[p] == sig[p]) {
            bad = 1;
            for (int it = 0; it < 1000000; it++) { int p2 = rnd() % N; int a = tau[p], b = tau[p2];
                if (!inc[(size_t)p * N + b] && !inc[(size_t)p2 * N + a] && b != sig[p] && a != sig[p2]) { tau[p] = b; tau[p2] = a; break; } }
        }
        if (!bad) break;
    }
    for (int p = 0; p < N; p++) {
        for (int c = 0; c < 2; c++) {
            int *m = c ? tau : sig; int ce = e;
            eu[e] = p; ev[e] = N + m[p]; partner[e] = -1; e++;
            eu[e] = p; ev[e] = N + m[p]; partner[e] = ce; partner[ce] = e; e++;
        }
    }
    /* (partner links set above: first copy of each doubled pair points to the second and vice versa) */
    for (int i = 0; i < NE; i++) {
        dfrom[2 * i] = eu[i]; dto[2 * i] = ev[i]; dfrom[2 * i + 1] = ev[i]; dto[2 * i + 1] = eu[i];
    }
    free(inc); free(sig); free(tau);
    FULL = (K >= 64) ? ~0ULL : ((1ULL << K) - 1);
    cur = malloc(8 * V); nxt = malloc(8 * V); U = malloc(8 * V);
    return 1;
}

static void dump_edges(const char *fn) {
    FILE *f = fopen(fn, "w");
    fprintf(f, "%d\n", V * K);
    for (int e = 0; e < NE; e++) for (int h = 0; h < K; h++)
        fprintf(f, "%d %d\n", eu[e] * K + h, ev[e] * K + (h + eg[e]) % K);
    fclose(f);
}

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: c07 gq.bin K\n"); return 1; }
    K = atoi(argv[2]);
    if (K < 2 || K > 63) return 1;
    if (!load_gq(argv[1])) { fprintf(stderr, "load fail\n"); return 1; }
    char *env;
    double secs = (env = getenv("SECS")) ? atof(env) : 300;
    rs ^= (env = getenv("SEED")) ? (uint64_t)atoll(env) * 0x9E3779B97F4A7C15ULL : 0;
    if (!rs) rs = 1;
    int ns = (env = getenv("NS")) ? atoi(env) : 40;
    double T0 = (env = getenv("T0")) ? atof(env) : 3.0;
    double T1 = (env = getenv("T1")) ? atof(env) : 0.05;
    const char *out = (env = getenv("OUT")) ? env : "best.txt";

    /* random initial voltages, copies of one doubled pair distinct */
    for (int e = 0; e < NE; e++) {
        int g = rnd() % K;
        if (partner[e] >= 0 && partner[e] < e) { while (g == eg[partner[e]]) g = rnd() % K; }
        setv(e, g);
    }
    /* sample sources */
    int *srcs = malloc(sizeof(int) * ns);
    for (int i = 0; i < ns; i++) srcs[i] = rnd() % V;
    long cost = cost_src(srcs, ns, NULL), best = cost;
    fprintf(stderr, "K=%d V=%d NE=%d ns=%d init cost %ld\n", K, V, NE, ns, cost);
    clock_t t0 = clock();
    long it = 0, acc = 0;
    int *bestg = malloc(sizeof(int) * NE); memcpy(bestg, eg, sizeof(int) * NE);
    double el = 0;
    for (;;) {
        if ((it & 255) == 0) {
            el = (double)(clock() - t0) / CLOCKS_PER_SEC;
            if (el > secs) break;
            double fr = el / secs;
            fprintf(stderr, "it %ld t=%.0f cur %ld best %ld acc %ld\n", it, el, cost, best, acc);
        }
        it++;
        double T = T0 * pow(T1 / T0, (double)(clock() - t0) / CLOCKS_PER_SEC / secs);
        int e = rnd() % NE;
        int og = eg[e], g = rnd() % K;
        if (g == og) continue;
        if (partner[e] >= 0 && eg[partner[e]] == g) continue;
        setv(e, g);
        long nc = cost_src(srcs, ns, NULL);
        if (nc <= cost || urand() < exp(-(double)(nc - cost) / T)) {
            cost = nc; acc++;
            if (cost < best) { best = cost; memcpy(bestg, eg, sizeof(int) * NE); }
            if (cost == 0) break;
        } else setv(e, og);
    }
    /* restore best and check on all sources */
    for (int e = 0; e < NE; e++) setv(e, bestg[e]);
    int *all = malloc(sizeof(int) * V); for (int i = 0; i < V; i++) all[i] = i;
    long full = cost_src(all, V, NULL);
    fprintf(stderr, "done it=%ld best(sample)=%ld full-cost(all %d sources)=%ld\n", it, best, V, full);
    FILE *f = fopen(out, "w");
    fprintf(f, "q %d K %d N %d NE %d full_uncovered %ld\n", q, K, N, NE, full);
    for (int e = 0; e < NE; e++) fprintf(f, "%d %d %d\n", eu[e], ev[e], eg[e]);
    fclose(f);
    printf("RESULT K=%d n_lift=%d full_uncovered=%ld sample_best=%ld\n", K, V * K, full, best);
    if (full == 0 && getenv("EMIT")) { dump_edges(getenv("LIFT")); printf("LIFT written\n"); }
    return 0;
}
