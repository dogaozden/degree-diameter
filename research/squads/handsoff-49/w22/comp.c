/* w22: compound of K copies of the H(3) incidence graph (728 vertices, girth 12, diameter 6).
   Copy k loses a perfect matching M_k (its inner graph is 3-regular); the 4th edge of each vertex is a cross edge.
   Cross edges form a bijection pi: A-side (points of all copies) -> B-side (lines of all copies).
   Copies are not a covering (cross edges are arbitrary), so the fibre/girth argument of w4 does not apply.
   Cost = unordered vertex pairs at distance > D (bit-parallel BFS, 64 sources per batch).
   Usage: comp BASE K SECONDS SEED T0 T1 OUTPREFIX
   Writes OUTPREFIX.best.edges whenever the best cost improves (edge list, n = K*728). */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>

#define NB 728
#define HP 364
#define DEGB 4
#define D 9
#define MAXK 8
#define MAXN (NB*MAXK)

static int K, N;
static int badj[NB][DEGB];
static int mate[MAXK][NB];       /* removed matching M_k (base partner), -1 if none */
static int adj[MAXN][4], degc[MAXN];
static int pi[MAXK*HP];          /* A index i -> B index pi[i] */
static uint64_t rng_s;
static uint64_t *reach, *fra, *nwa;

static uint64_t rnd(void) { rng_s ^= rng_s << 13; rng_s ^= rng_s >> 7; rng_s ^= rng_s << 17; return rng_s; }
static double urand(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
static int ga(int i) { return (i / HP) * NB + i % HP; }
static int gb(int j) { return (j / HP) * NB + HP + j % HP; }

static int base_adjacent(int u, int v) {
    for (int t = 0; t < DEGB; t++) if (badj[u][t] == v) return 1;
    return 0;
}
/* pair (a, b) may carry a cross edge iff it is not an inner edge of their common copy */
static int valid_pair(int a, int b) {
    if (a / NB != b / NB) return 1;
    int k = a / NB, u = a % NB, v = b % NB;
    if (!base_adjacent(u, v)) return 1;
    return mate[k][u] == v;
}

static void build_adj(void) {
    for (int g = 0; g < N; g++) degc[g] = 0;
    for (int k = 0; k < K; k++)
        for (int u = 0; u < NB; u++)
            for (int t = 0; t < DEGB; t++) {
                int v = badj[u][t];
                if (u < v && mate[k][u] != v) {
                    int a = k*NB + u, b = k*NB + v;
                    adj[a][degc[a]++] = b; adj[b][degc[b]++] = a;
                }
            }
    for (int i = 0; i < K*HP; i++) {
        int a = ga(i), b = gb(pi[i]);
        adj[a][degc[a]++] = b; adj[b][degc[b]++] = a;
    }
}

/* far pairs: unordered pairs at distance > D (unreachable included) */
static long cost_full(void) {
    build_adj();
    long far = 0;
    for (int s0 = 0; s0 < N; s0 += 64) {
        int cnt = N - s0 < 64 ? N - s0 : 64;
        uint64_t mask = cnt == 64 ? ~0ULL : ((1ULL << cnt) - 1);
        for (int v = 0; v < N; v++) reach[v] = 0;
        for (int i = 0; i < cnt; i++) reach[s0 + i] |= 1ULL << i;
        memcpy(fra, reach, sizeof(uint64_t) * N);
        uint64_t *fr = fra, *nw = nwa;
        for (int lv = 1; lv <= D; lv++) {
            for (int v = 0; v < N; v++) {
                uint64_t x = 0;
                for (int t = 0; t < degc[v]; t++) x |= fr[adj[v][t]];
                nw[v] = x & ~reach[v];
            }
            for (int v = 0; v < N; v++) reach[v] |= nw[v];
            uint64_t *tmp = fr; fr = nw; nw = tmp;
        }
        for (int v = 0; v < N; v++) far += __builtin_popcountll(mask & ~reach[v]);
    }
    return far / 2;
}

static void write_edges(const char *fn) {
    build_adj();
    FILE *f = fopen(fn, "w");
    fprintf(f, "%d\n", N);
    for (int g = 0; g < N; g++)
        for (int t = 0; t < degc[g]; t++) if (adj[g][t] > g) fprintf(f, "%d %d\n", g, adj[g][t]);
    fclose(f);
}

/* Kuhn augmenting paths for a perfect matching of the base (points 0..363 to lines 364..727) */
static int matchL[NB], matchP[NB], visL[NB], vis_stamp;
static int kuhn(int p) {
    int order[DEGB]; for (int t = 0; t < DEGB; t++) order[t] = t;
    for (int t = DEGB - 1; t > 0; t--) { int r = rnd() % (t + 1); int x = order[t]; order[t] = order[r]; order[r] = x; }
    for (int tt = 0; tt < DEGB; tt++) {
        int l = badj[p][order[tt]];
        if (visL[l] == vis_stamp) continue;
        visL[l] = vis_stamp;
        if (matchL[l] < 0 || kuhn(matchL[l])) { matchL[l] = p; matchP[p] = l; return 1; }
    }
    return 0;
}

static int try_switch(int i1, int i2, int *o1, int *o2) {
    int j1 = pi[i1], j2 = pi[i2];
    if (!valid_pair(ga(i1), gb(j2)) || !valid_pair(ga(i2), gb(j1))) return 0;
    *o1 = j2; *o2 = j1; return 1;
}

int main(int argc, char **argv) {
    if (argc < 8) { fprintf(stderr, "usage: comp BASE K SECONDS SEED T0 T1 OUTPREFIX\n"); return 2; }
    K = atoi(argv[2]); N = K * NB;
    double secs = atof(argv[3]);
    rng_s = strtoull(argv[4], 0, 10) * 2654435761ULL + 88172645463325252ULL;
    double T0 = atof(argv[5]), T1 = atof(argv[6]);
    const char *outp = argv[7];
    reach = malloc(sizeof(uint64_t) * N); fra = malloc(sizeof(uint64_t) * N); nwa = malloc(sizeof(uint64_t) * N);

    FILE *f = fopen(argv[1], "r");
    int n, a, b, eu[2000], ev[2000], ne = 0, degs[NB];
    if (fscanf(f, "%d", &n) != 1 || n != NB) { fprintf(stderr, "base must have 728 vertices\n"); return 2; }
    while (fscanf(f, "%d %d", &a, &b) == 2) { eu[ne] = a; ev[ne] = b; ne++; }
    fclose(f);
    memset(degs, 0, sizeof degs);
    for (int e = 0; e < ne; e++) { int u = eu[e], v = ev[e]; badj[u][degs[u]++] = v; badj[v][degs[v]++] = u; }
    for (int u = 0; u < NB; u++) if (degs[u] != DEGB) { fprintf(stderr, "base not 4-regular\n"); return 2; }

    /* random perfect matchings M_k */
    for (int k = 0; k < K; k++) {
        for (int u = 0; u < NB; u++) { matchL[u] = -1; matchP[u] = -1; visL[u] = 0; }
        vis_stamp = 0;
        int order[HP]; for (int p = 0; p < HP; p++) order[p] = p;
        for (int p = HP - 1; p > 0; p--) { int r = rnd() % (p + 1); int x = order[p]; order[p] = order[r]; order[r] = x; }
        for (int oi = 0; oi < HP; oi++) {
            vis_stamp++;
            if (!kuhn(order[oi])) { fprintf(stderr, "no perfect matching\n"); return 2; }
        }
        for (int u = 0; u < NB; u++) mate[k][u] = -1;
        for (int p = 0; p < HP; p++) { mate[k][p] = matchP[p]; mate[k][matchP[p]] = p; }
    }

    /* random initial cross bijection, repaired so that no cross pair is an inner edge */
    for (int i = 0; i < K*HP; i++) pi[i] = i;
    for (int i = K*HP - 1; i > 0; i--) { int r = rnd() % (i + 1); int x = pi[i]; pi[i] = pi[r]; pi[r] = x; }
    for (int pass = 0; pass < 1000000; pass++) {
        int bad = 0;
        for (int i = 0; i < K*HP; i++) if (!valid_pair(ga(i), gb(pi[i]))) {
            int i2 = rnd() % (K*HP), o1, o2;
            if (try_switch(i, i2, &o1, &o2)) { pi[i] = o1; pi[i2] = o2; }
            bad = 1;
        }
        if (!bad) break;
    }
    for (int i = 0; i < K*HP; i++) if (!valid_pair(ga(i), gb(pi[i]))) { fprintf(stderr, "repair failed\n"); return 2; }

    long cur = cost_full(), best = cur;
    fprintf(stderr, "init far=%ld\n", cur);
    char fn[512]; snprintf(fn, sizeof fn, "%s.best.edges", outp);
    write_edges(fn);
    time_t t0 = time(NULL); long it = 0, acc = 0;
    while (difftime(time(NULL), t0) < secs) {
        double frac = difftime(time(NULL), t0) / secs;
        double T = T0 * pow(T1 / T0, frac);
        int i1 = rnd() % (K*HP), i2 = rnd() % (K*HP);
        if (i1 == i2) continue;
        int j1 = pi[i1], j2 = pi[i2], o1, o2;
        if (!try_switch(i1, i2, &o1, &o2)) continue;
        pi[i1] = o1; pi[i2] = o2;
        long c = cost_full(); it++;
        long d = c - cur;
        if (d <= 0 || urand() < exp(-d / T)) {
            cur = c; acc++;
            if (c < best) {
                best = c; write_edges(fn);
                fprintf(stderr, "it=%ld T=%.3f best=%ld\n", it, T, best);
                if (best == 0) { fprintf(stderr, "FOUND far=0\n"); break; }
            }
        } else { pi[i1] = j1; pi[i2] = j2; }
    }
    fprintf(stderr, "done it=%ld acc=%ld cur=%ld best=%ld\n", it, acc, cur, best);
    printf("RESULT n=%d best_far=%ld\n", N, best);
    return 0;
}
