/* c3sa: simulated annealing over G-invariant bipartite graphs on n <= 192 vertices with prescribed degrees.
 * deep-37 round 1, card c3 (n = 169: A = 0..NA-1, B = NA..n-1; target degrees from DEGFILE).
 * Moves: pick edges (a,b), (c,d) with a,c in A; form the switch (a,d),(c,b); apply to the whole G-orbit of both
 * edges (removed set R = G{ab} u G{cd}, added set Ad = G{ad} u G{cb}, both deduplicated). Accept the move only if
 * Ad is disjoint from the current edge set and every vertex has the same degree change in R and Ad (so the result is
 * simple, G-invariant and has the prescribed degrees).
 * Cost: far = number of unordered pairs at distance > 7 (bit-parallel BFS to depth 7 from all vertices).
 * Usage: c3sa GROUPFILE DEGFILE SECONDS T0 T1 SEED OUTPREFIX
 *   GROUPFILE: "n order", then order permutations (n ints each), then a colour line (ignored; A = 0..NA-1).
 *   DEGFILE:   "n NA", then n target degrees.
 * Writes OUTPREFIX_best.edges whenever the best far improves (edge list, apsp format), and prints progress.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdint.h>
#include <time.h>

#define MAXN 192
#define MAXG 64
typedef uint64_t u64;

int n, NA, ng;
int G[MAXG][MAXN];
int adj[MAXN][3], deg[MAXN], tgt[MAXN];

typedef struct { int p, q; } pr;

static u64 rs = 88172645463325252ULL;
static u64 rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndint(int m) { return (int)(rnd64() % (u64)m); }
static double rnd01(void) { return (rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int has_edge(int a, int b) {
    for (int i = 0; i < deg[a]; i++) if (adj[a][i] == b) return 1;
    return 0;
}
static void add_edge(int a, int b) { adj[a][deg[a]++] = b; adj[b][deg[b]++] = a; }
static void rem_edge(int a, int b) {
    for (int i = 0; i < deg[a]; i++) if (adj[a][i] == b) { adj[a][i] = adj[a][--deg[a]]; break; }
    for (int i = 0; i < deg[b]; i++) if (adj[b][i] == a) { adj[b][i] = adj[b][--deg[b]]; break; }
}

int last_far7 = 0;
static u64 farm[MAXN][3], farm_cur[MAXN][3];
static u64 sidem[2][3];
static int COSTK = 1;
static double PT = 0.0; /* cost = sum_{r=7}^{6+COSTK} far_r, far_r = pairs at distance > r; score = far_7 */
static int far_eval(void) {
    static u64 M1[MAXN][3], M2[MAXN][3];
    u64 (*M)[3] = M1, (*NM)[3] = M2;
    for (int v = 0; v < n; v++) {
        M[v][0] = M[v][1] = M[v][2] = 0;
        M[v][v >> 6] |= 1ULL << (v & 63);
    }
    int cost = 0;
    for (int k = 1; k <= 6 + COSTK; k++) {
        for (int v = 0; v < n; v++) {
            u64 x0 = M[v][0], x1 = M[v][1], x2 = M[v][2];
            for (int i = 0; i < deg[v]; i++) {
                int u = adj[v][i];
                x0 |= M[u][0]; x1 |= M[u][1]; x2 |= M[u][2];
            }
            NM[v][0] = x0; NM[v][1] = x1; NM[v][2] = x2;
        }
        u64 (*t)[3] = M; M = NM; NM = t;
        if (k >= 7) {
            long far2 = 0;
            for (int v = 0; v < n; v++) {
                int pc = __builtin_popcountll(M[v][0]) + __builtin_popcountll(M[v][1]) + __builtin_popcountll(M[v][2]);
                far2 += n - pc;
            }
            int fk = (int)(far2 / 2);
            if (k == 7) {
                last_far7 = fk;
                for (int v = 0; v < n; v++) { farm[v][0] = ~M[v][0]; farm[v][1] = ~M[v][1]; farm[v][2] = ~M[v][2]; }
            }
            cost += fk;
        }
    }
    return cost;
}

static int load_group(const char *fn) {
    FILE *f = fopen(fn, "r");
    if (!f) { perror(fn); exit(2); }
    int order;
    if (fscanf(f, "%d %d", &n, &order) != 2) { fprintf(stderr, "bad group file\n"); exit(2); }
    if (order > MAXG) { fprintf(stderr, "order too big\n"); exit(2); }
    for (int g = 0; g < order; g++)
        for (int v = 0; v < n; v++)
            if (fscanf(f, "%d", &G[g][v]) != 1) { fprintf(stderr, "bad perm\n"); exit(2); }
    fclose(f);
    return order;
}

static void load_deg(const char *fn) {
    FILE *f = fopen(fn, "r");
    if (!f) { perror(fn); exit(2); }
    int nn;
    if (fscanf(f, "%d %d", &nn, &NA) != 2) { fprintf(stderr, "bad deg file\n"); exit(2); }
    if (nn != n) { fprintf(stderr, "deg file n mismatch\n"); exit(2); }
    for (int v = 0; v < n; v++) if (fscanf(f, "%d", &tgt[v]) != 1) { fprintf(stderr, "bad deg\n"); exit(2); }
    fclose(f);
}

static void write_edges(const char *fn) {
    FILE *f = fopen(fn, "w");
    if (!f) { perror(fn); return; }
    int m = 0;
    for (int v = 0; v < n; v++) m += deg[v];
    fprintf(f, "%d\n", n);
    for (int v = 0; v < n; v++)
        for (int i = 0; i < deg[v]; i++)
            if (adj[v][i] > v) fprintf(f, "%d %d\n", v, adj[v][i]);
    fclose(f);
}

/* Orbit-greedy random G-invariant start with the target degrees. Returns 1 on success. */
static int init_graph(void) {
    for (int attempt = 0; attempt < 20000; attempt++) {
        for (int v = 0; v < n; v++) deg[v] = 0;
        int stuck = 0;
        while (1) {
            int any = 0;
            for (int v = 0; v < n; v++) if (deg[v] < tgt[v]) { any = 1; break; }
            if (!any) return 1;
            if (stuck > 3000) break;
            /* random deficient A-vertex and B-vertex */
            int a = -1, b = -1;
            for (int tries = 0; tries < 10000; tries++) {
                int x = rndint(n);
                if (a < 0 && x < NA && deg[x] < tgt[x]) a = x;
                if (b < 0 && x >= NA && deg[x] < tgt[x]) b = x;
                if (a >= 0 && b >= 0) break;
            }
            if (a < 0 || b < 0) break;
            /* orbit of (a,b) */
            pr S[MAXG]; int ns = 0; int ok = 1;
            for (int g = 0; g < ng && ok; g++) {
                pr e = { G[g][a], G[g][b] };
                int dup = 0;
                for (int i = 0; i < ns; i++) if (S[i].p == e.p && S[i].q == e.q) { dup = 1; break; }
                if (!dup) S[ns++] = e;
            }
            int inc[MAXN]; memset(inc, 0, sizeof(int) * n);
            for (int i = 0; i < ns && ok; i++) {
                if (has_edge(S[i].p, S[i].q)) ok = 0;
                inc[S[i].p]++; inc[S[i].q]++;
            }
            for (int v = 0; v < n && ok; v++) if (deg[v] + inc[v] > tgt[v]) ok = 0;
            if (ok) { for (int i = 0; i < ns; i++) add_edge(S[i].p, S[i].q); stuck = 0; }
            else stuck++;
        }
    }
    return 0;
}

static int check_deg(void) {
    for (int v = 0; v < n; v++) if (deg[v] != tgt[v]) return 0;
    return 1;
}

static int addset(pr *S, int *cnt, int p, int q) {
    if (p > q) { int t = p; p = q; q = t; }
    for (int i = 0; i < *cnt; i++) if (S[i].p == p && S[i].q == q) return 0;
    S[*cnt].p = p; S[*cnt].q = q; (*cnt)++;
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 8) { fprintf(stderr, "usage: c3sa GROUPFILE DEGFILE SECONDS T0 T1 SEED OUTPREFIX [INITEDGES]\n"); return 2; }
    ng = load_group(argv[1]);
    load_deg(argv[2]);
    double secs = atof(argv[3]), T0 = atof(argv[4]), T1 = atof(argv[5]);
    rs ^= (u64)atoll(argv[6]) * 0x9E3779B97F4A7C15ULL; if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd64();
    const char *outp = argv[7];

    /* check that G preserves sides and is a permutation group (basic check) */
    for (int g = 0; g < ng; g++)
        for (int v = 0; v < n; v++)
            if ((v < NA) != (G[g][v] < NA)) { fprintf(stderr, "group does not preserve sides\n"); return 2; }

    if (argc > 8) {
        /* start from an edge list in c3sa convention (A = 0..NA-1); targets = its degrees */
        FILE *f = fopen(argv[8], "r");
        if (!f) { perror(argv[8]); return 2; }
        int nn; if (fscanf(f, "%d", &nn) != 1 || nn != n) { fprintf(stderr, "init n mismatch\n"); return 2; }
        for (int v = 0; v < n; v++) deg[v] = 0;
        int a, b;
        while (fscanf(f, "%d %d", &a, &b) == 2) {
            if (a >= NA || b < NA) { fprintf(stderr, "init graph not in A-B convention\n"); return 2; }
            if (has_edge(a, b)) { fprintf(stderr, "init multi-edge\n"); return 2; }
            add_edge(a, b);
        }
        fclose(f);
        for (int v = 0; v < n; v++) tgt[v] = deg[v];
        for (int v = 0; v < n; v++) if (deg[v] > 3) { fprintf(stderr, "deg>3\n"); return 2; }
    } else if (!init_graph()) { fprintf(stderr, "init failed\n"); return 1; }
    if (getenv("COSTK")) COSTK = atoi(getenv("COSTK"));
    if (getenv("PT")) PT = atof(getenv("PT"));
    int cur = far_eval();
    int best = last_far7;
    int curf7 = last_far7;
    memcpy(farm_cur, farm, sizeof farm);
    char fn[512];
    snprintf(fn, sizeof fn, "%s_best.edges", outp);
    write_edges(fn);
    fprintf(stderr, "init far=%d\n", cur);

    struct timespec t0s, t1s;
    clock_gettime(CLOCK_MONOTONIC, &t0s);
    long long it = 0, acc = 0, valid = 0;
    double el = 0;
    double T = T0;
    while (1) {
        if ((it & 1023) == 0) {
            clock_gettime(CLOCK_MONOTONIC, &t1s);
            el = (t1s.tv_sec - t0s.tv_sec) + 1e-9 * (t1s.tv_nsec - t0s.tv_nsec);
            if (el >= secs) break;
            double frac = el / secs;
            T = T0 * pow(T1 / T0, frac);
        }
        it++;
        int a, b, c, d;
        if (PT > 0 && rnd01() < PT) {
            /* targeted: far same-side pair (u,v); x near u, z near v (radius 0 or 2), edges (x,y),(z,w) switched */
            int u = -1, v = -1;
            for (int tries = 0; tries < 60 && v < 0; tries++) {
                int uu = rndint(n);
                int cnt = 0; int cand[MAXN];
                for (int w2 = 0; w2 < n; w2++) {
                    if (w2 == uu) continue;
                    if (!((farm_cur[uu][w2 >> 6] >> (w2 & 63)) & 1ULL)) continue;
                    if ((uu < NA) != (w2 < NA)) continue;
                    cand[cnt++] = w2;
                }
                if (cnt) { u = uu; v = cand[rndint(cnt)]; }
            }
            if (v < 0) continue;
            int Lu[16], nu = 0, Lv[16], nv = 0;
            Lu[nu++] = u;
            for (int i = 0; i < deg[u]; i++) { int y = adj[u][i]; for (int j = 0; j < deg[y]; j++) { int x = adj[y][j]; if (x != u) Lu[nu++] = x; } }
            Lv[nv++] = v;
            for (int i = 0; i < deg[v]; i++) { int y = adj[v][i]; for (int j = 0; j < deg[y]; j++) { int x = adj[y][j]; if (x != v) Lv[nv++] = x; } }
            int x = Lu[rndint(nu)], z = Lv[rndint(nv)];
            if (x == z) continue;
            a = x; b = adj[x][rndint(deg[x])];
            c = z; d = adj[z][rndint(deg[z])];
            if (b == d) continue;
        } else {
            a = rndint(NA);
            b = adj[a][rndint(deg[a])];
            c = rndint(NA);
            if (c == a) continue;
            d = adj[c][rndint(deg[c])];
            if (d == b) continue;
        }

        pr R[2 * MAXG], Ad[2 * MAXG]; int nR = 0, nAd = 0;
        for (int g = 0; g < ng; g++) {
            addset(R, &nR, G[g][a], G[g][b]);
            addset(R, &nR, G[g][c], G[g][d]);
        }
        for (int g = 0; g < ng; g++) {
            addset(Ad, &nAd, G[g][a], G[g][d]);
            addset(Ad, &nAd, G[g][c], G[g][b]);
        }
        int ok = 1;
        for (int i = 0; i < nAd && ok; i++) if (has_edge(Ad[i].p, Ad[i].q)) ok = 0;
        if (!ok) continue;
        /* degree balance: net change must vanish at every vertex */
        int dd[MAXN]; memset(dd, 0, sizeof(int) * n);
        for (int i = 0; i < nR; i++) { dd[R[i].p]--; dd[R[i].q]--; }
        for (int i = 0; i < nAd; i++) { dd[Ad[i].p]++; dd[Ad[i].q]++; }
        for (int v = 0; v < n && ok; v++) if (dd[v] != 0) ok = 0;
        if (!ok) continue;
        valid++;

        for (int i = 0; i < nR; i++) rem_edge(R[i].p, R[i].q);
        for (int i = 0; i < nAd; i++) add_edge(Ad[i].p, Ad[i].q);
        int nw = far_eval();
        int nwf7 = last_far7;
        int delta = nw - cur;
        if (getenv("DBG") && it < 400) fprintf(stderr, "DBG it=%lld tgt=%d cur=%d nw=%d\n", it, (PT>0 && it>0), cur, nw);
        if (delta <= 0 || rnd01() < exp(-delta / T)) {
            cur = nw; curf7 = nwf7; acc++;
            memcpy(farm_cur, farm, sizeof farm);
            if (curf7 < best) {
                best = curf7;
                write_edges(fn);
                fprintf(stderr, "it=%lld t=%.1f T=%.3f best=%d\n", it, el, T, best);
                if (best == 0) break;
            }
        } else {
            for (int i = 0; i < nAd; i++) rem_edge(Ad[i].p, Ad[i].q);
            for (int i = 0; i < nR; i++) add_edge(R[i].p, R[i].q);
        }
        if ((it % 2000000) == 0)
            fprintf(stderr, "it=%lld t=%.1f T=%.3f cost=%d far7=%d best=%d acc=%lld valid=%lld\n", it, el, T, cur, curf7, best, acc, valid);
    }
    if (!check_deg()) fprintf(stderr, "WARNING: degree check failed\n");
    printf("DONE best=%d far7=%d cost=%d it=%lld valid=%lld acc=%lld secs=%.1f file=%s\n", best, curf7, cur, it, valid, acc, el, fn);
    return 0;
}
