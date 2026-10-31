/* c13 symsa.c: simulated annealing over 2-switches of a bipartite 6-regular graph that is invariant under a
 * fixed-point-free automorphism pi (given as a permutation file, order K = ORD). Each proposal is an orbit move:
 * the 2-switch (e1,e2) and its pi-images are applied together, so the graph stays pi-invariant.
 * Cost = number of unordered vertex pairs at distance > 5 (bit-parallel BFS, full recomputation per evaluated move).
 * env: INFILE (edge list: n then "u v"), PERMFILE (n ints, pi(v) for each vertex; identity if unset), ORD (orbit
 *      length of pi, default 1), SEED (1), ITERS (per round, 300000), T0 (1.5), T1 (0.1), ROUNDS (1), SECS (600),
 *      PG (probability of a guided e1 at an endpoint of a far pair, 0.5), OUT.
 * Prints "best b cur c secs s" lines. Writes OUT whenever the best improves and at the end. */
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 1024
#define W 16
#define MAXE 4096
typedef uint64_t u64;

static int n, nw, ne, K;
static int side[MAXN], perm[MAXN];
static int adj[MAXN][6], deg[MAXN];
static int EA[MAXE], EB[MAXE];
static int idx[MAXN][MAXN];
static u64 LA[MAXN][W], LB[MAXN][W], L4[MAXN][W];
static u64 (*cur)[W] = LA, (*nxt)[W] = LB;
static uint64_t rs = 88172645463325252ULL;
static int farv[MAXN], nfar;

static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline double urand(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }

static void rep(int v, int old, int nw_) {
    for (int k = 0; k < deg[v]; k++) if (adj[v][k] == old) { adj[v][k] = nw_; return; }
    fprintf(stderr, "rep failed\n"); exit(1);
}
/* 2-switch on edge slots i and k: (a1,b1),(a2,b2) -> (a1,b2),(a2,b1). Self-inverse. */
static void swap_slots(int i, int k) {
    int a1 = EA[i], b1 = EB[i], a2 = EA[k], b2 = EB[k];
    rep(a1, b1, b2); rep(b1, a1, a2); rep(a2, b2, b1); rep(b2, a2, a1);
    idx[a1][b1] = -1; idx[a2][b2] = -1;
    EB[i] = b2; EB[k] = b1;
    idx[a1][b2] = i; idx[a2][b1] = k;
}
static int valid_pair(int i, int k) {
    int a1 = EA[i], b1 = EB[i], a2 = EA[k], b2 = EB[k];
    if (i == k || a1 == a2 || b1 == b2) return 0;
    if (idx[a1][b2] >= 0 || idx[a2][b1] >= 0) return 0;
    return 1;
}
static long cost_full(void) {
    for (int v = 0; v < n; v++) {
        memset(cur[v], 0, nw * 8);
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int k = 0; k < 5; k++) {
        for (int v = 0; v < n; v++) {
            u64 *d = nxt[v];
            memcpy(d, cur[v], nw * 8);
            for (int t = 0; t < deg[v]; t++) {
                u64 *s = cur[adj[v][t]];
                for (int w = 0; w < nw; w++) d[w] |= s[w];
            }
        }
        u64 (*tmp)[W] = cur; cur = nxt; nxt = tmp;
    }
    long bad = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < nw; w++) c += __builtin_popcountll(cur[v][w]);
        bad += n - c;
    }
    return bad / 2;
}
static void compute_far(void) {
    nfar = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < nw; w++) c += __builtin_popcountll(cur[v][w]);
        if (c < n) farv[nfar++] = v;
    }
}
static void write_edges(const char *fn) {
    FILE *f = fopen(fn, "w"); if (!f) return;
    fprintf(f, "%d\n", n);
    for (int i = 0; i < ne; i++) fprintf(f, "%d %d\n", EA[i], EB[i]);
    fclose(f);
}

static int BEA[MAXE], BEB[MAXE];
static void save_best(void) { memcpy(BEA, EA, sizeof(int) * ne); memcpy(BEB, EB, sizeof(int) * ne); }
static void load_state(const int *A, const int *B) {
    for (int i = 0; i < ne; i++) idx[EA[i]][EB[i]] = -1;
    memset(deg, 0, sizeof deg);
    for (int i = 0; i < ne; i++) { EA[i] = A[i]; EB[i] = B[i]; idx[EA[i]][EB[i]] = i; }
    for (int i = 0; i < ne; i++) { adj[EA[i]][deg[EA[i]]++] = EB[i]; adj[EB[i]][deg[EB[i]]++] = EA[i]; }
}
int main(void) {
    const char *in = getenv("INFILE"), *out = getenv("OUT") ? getenv("OUT") : "symsa_best.edges";
    if (!in) { fprintf(stderr, "INFILE needed\n"); return 2; }
    double SECS = getenv("SECS") ? atof(getenv("SECS")) : 600;
    long ITERS = getenv("ITERS") ? atol(getenv("ITERS")) : 300000;
    double T0 = getenv("T0") ? atof(getenv("T0")) : 1.5, T1 = getenv("T1") ? atof(getenv("T1")) : 0.1;
    int ROUNDS = getenv("ROUNDS") ? atoi(getenv("ROUNDS")) : 1;
    double PG = getenv("PG") ? atof(getenv("PG")) : 0.5;
    if (getenv("SEED")) rs ^= (uint64_t)atoll(getenv("SEED")) * 0x9E3779B97F4A7C15ULL;
    for (int i = 0; i < 20; i++) rnd();
    K = getenv("ORD") ? atoi(getenv("ORD")) : 1;

    FILE *f = fopen(in, "r");
    if (!f || fscanf(f, "%d", &n) != 1) { fprintf(stderr, "bad infile\n"); return 2; }
    nw = (n + 63) / 64; if (nw > W) { fprintf(stderr, "n too big\n"); return 2; }
    static int U[MAXE], V[MAXE];
    int m = 0; while (fscanf(f, "%d %d", &U[m], &V[m]) == 2) m++;
    fclose(f);
    /* sides by BFS */
    static int col[MAXN], q[MAXN], dg[MAXN];
    for (int v = 0; v < n; v++) { col[v] = -1; dg[v] = 0; }
    for (int i = 0; i < m; i++) { dg[U[i]]++; dg[V[i]]++; }
    static int st[MAXN + 1], al[2 * MAXE], fill[MAXN];
    st[0] = 0; for (int v = 0; v < n; v++) st[v + 1] = st[v] + dg[v];
    for (int v = 0; v < n; v++) fill[v] = 0;
    for (int i = 0; i < m; i++) { al[st[U[i]] + fill[U[i]]++] = V[i]; al[st[V[i]] + fill[V[i]]++] = U[i]; }
    int h = 0, t = 0;
    for (int s = 0; s < n; s++) if (col[s] < 0) {
        col[s] = 0; q[t++] = s;
        while (h < t) { int x = q[h++]; for (int k = st[x]; k < st[x + 1]; k++) { int y = al[k]; if (col[y] < 0) { col[y] = 1 - col[x]; q[t++] = y; } else if (col[y] == col[x]) { fprintf(stderr, "not bipartite\n"); return 2; } } }
    }
    for (int v = 0; v < n; v++) side[v] = col[v];
    ne = 0;
    for (int v = 0; v < n; v++) for (int a = 0; a < n; a++) idx[v][a] = -1;
    for (int i = 0; i < m; i++) {
        int a = U[i], b = V[i];
        if (side[a] == 1) { int tmp = a; a = b; b = tmp; }
        EA[ne] = a; EB[ne] = b; idx[a][b] = ne; ne++;
    }
    for (int v = 0; v < n; v++) perm[v] = v;
    if (getenv("PERMFILE")) {
        FILE *pf = fopen(getenv("PERMFILE"), "r");
        for (int v = 0; v < n; v++) if (fscanf(pf, "%d", &perm[v]) != 1) { fprintf(stderr, "bad perm\n"); return 2; }
        fclose(pf);
    }
    memset(deg, 0, sizeof deg);
    for (int i = 0; i < ne; i++) { adj[EA[i]][deg[EA[i]]++] = EB[i]; adj[EB[i]][deg[EB[i]]++] = EA[i]; }
    for (int v = 0; v < n; v++) if (deg[v] != 6) { fprintf(stderr, "degree %d at %d\n", deg[v], v); return 2; }
    /* checks: perm is an automorphism and has order K */
    for (int i = 0; i < ne; i++) if (idx[perm[EA[i]]][perm[EB[i]]] < 0) { fprintf(stderr, "perm not an automorphism\n"); return 2; }

    long cur_bad = cost_full();
    long best = cur_bad;
    compute_far();
    write_edges(out);
    printf("start bad %ld n %d edges %d ORD %d\n", cur_bad, n, ne, K); fflush(stdout);
    double t_start = now();
    long total = 0;
    int ei_g[MAXE];
    save_best();
    for (int round = 0; round < ROUNDS && now() - t_start < SECS; round++) {
        if (round > 0) {
            load_state(BEA, BEB); cur_bad = cost_full(); compute_far();
            int KICK = getenv("KICK") ? atoi(getenv("KICK")) : 0;
            for (int kk = 0, tries = 0; kk < KICK && tries < 100000; tries++) {
                int i1 = rnd() % ne, i2 = rnd() % ne;
                if (!valid_pair(i1, i2)) continue;
                swap_slots(i1, i2); kk++;
            }
            if (KICK > 0) { cur_bad = cost_full(); compute_far(); }
        }
        for (long it = 0; it < ITERS && now() - t_start < SECS; it++, total++) {
            double frac = (double)it / ITERS;
            double T = T0 * pow(T1 / T0, frac);
            int e1, e2;
            if (nfar > 0 && urand() < PG) {
                int v = farv[rnd() % nfar];
                int d = deg[v]; int w = adj[v][rnd() % d];
                e1 = idx[v][w] >= 0 ? idx[v][w] : idx[w][v];
            } else e1 = rnd() % ne;
            e2 = rnd() % ne;
            /* orbit of e1 and e2 */
            int ia[64], ka[64];
            int ok = 1, a = e1, k2 = e2;
            (void)ei_g;
            for (int j = 0; j < K && ok; j++) {
                ia[j] = a; ka[j] = k2;
                /* edge images: pi applied to edge a */
                int pa = perm[EA[a]], pb = perm[EB[a]];
                int na = idx[pa][pb] >= 0 ? idx[pa][pb] : -1;
                int pa2 = perm[EA[k2]], pb2 = perm[EB[k2]];
                int nk = idx[pa2][pb2] >= 0 ? idx[pa2][pb2] : -1;
                if (na < 0 || nk < 0) { ok = 0; break; }
                a = na; k2 = nk;
            }
            if (!ok) continue;
            /* e2 must not be in the orbit of e1 */
            for (int j = 0; j < K && ok; j++) if (ka[0] == ia[j] || ia[0] == ka[j]) ok = 0;
            if (!ok) continue;
            /* apply switches sequentially with validity */
            int done = 0;
            for (int j = 0; j < K; j++) {
                if (!valid_pair(ia[j], ka[j])) break;
                swap_slots(ia[j], ka[j]); done++;
            }
            if (done < K) {
                for (int j = done - 1; j >= 0; j--) swap_slots(ia[j], ka[j]);
                continue;
            }
            long nb = cost_full();
            int acc = 0;
            if (nb <= cur_bad) acc = 1;
            else if (urand() < exp(-(double)(nb - cur_bad) / T)) acc = 1;
            if (acc) {
                cur_bad = nb;
                compute_far();
                if (cur_bad < best) {
                    best = cur_bad; save_best(); write_edges(out);
                    printf("best %ld it %ld T %.3f secs %.1f\n", best, total, T, now() - t_start); fflush(stdout);
                    if (best == 0) { printf("ZERO FOUND n=%d\n", n); fflush(stdout); return 0; }
                }
            } else {
                for (int j = K - 1; j >= 0; j--) swap_slots(ia[j], ka[j]);


            }
            if (total % 20000 == 0) { printf("it %ld cur %ld best %ld T %.3f secs %.0f\n", total, cur_bad, best, T, now() - t_start); fflush(stdout); }
        }
    }
    write_edges(out);
    printf("final best %ld cur %ld iters %ld secs %.1f\n", best, cur_bad, total, now() - t_start);
    return 0;
}
