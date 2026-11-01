/* h1.c: card h1. The 684 Haar record graph (shared/h684.edges, A = 0..341, B = 342..683), delete a matching of k
 * edges (x_i,y_i), insert a = 684 (side A) and b = 685 (side B), edges a-b, a-y_i, b-x_i.
 * bad = unordered pairs at distance > 5 among the 686 vertices (same as score65).
 * Modes:
 *   h1 eval K x1 y1 .. xK yK [OUT]        exact bad count + breakdown (+ edge list to OUT)
 *   h1 sa K SECS SEED T0 T1 [OUT]          simulated annealing over k-matchings (time-limited)
 *   h1 beam K W [OUT]                      beam search growing the matching one edge at a time
 *   h1 star [SECS]                          structured (i): x_1..x_5 all adjacent to one B-vertex w
 *   h1 cycle [SECS]                         structured (ii): alternating 10-cycles through x_1 = 0
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <math.h>

#define NB 684
#define NN 686
#define A_NEW 684
#define B_NEW 685

static int m0;
static int AB = 1;
static int NA_ATT = 99, NBX_ATT = 99;   /* how many deleted edges attach a (to y) and b (to x); default all */   /* 1: edge a-b (k <= 5); 0: no a-b edge (k <= 6) */
static int EU[2100], EV[2100];
static int adjB[NB][6], adjE[NB][6], degB[NB];   /* base adjacency + edge ids */
static int adj[NN][6], deg[NN];   /* a and b: up to 6 neighbours each */
static uint64_t M0[NN], M1[NN];
static unsigned char D0[NB][NB];

static double now(void) { struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts); return ts.tv_sec + 1e-9 * ts.tv_nsec; }
static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static double u01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

/* build graph: base minus removed edges, plus a,b (ins=1) */
static void build(const int *rem, int k, int ins) {
    static char removed[2100];
    memset(removed, 0, sizeof removed);
    for (int i = 0; i < k; i++) removed[rem[i]] = 1;
    for (int v = 0; v < NN; v++) deg[v] = 0;
    for (int e = 0; e < m0; e++) if (!removed[e]) {
        int u = EU[e], v = EV[e];
        adj[u][deg[u]++] = v; adj[v][deg[v]++] = u;
    }
    if (!ins) return;
    if (AB) { adj[A_NEW][deg[A_NEW]++] = B_NEW; adj[B_NEW][deg[B_NEW]++] = A_NEW; }
    for (int i = 0; i < k; i++) {
        int e = rem[i], x = EU[e], y = EV[e];
        if (i < NA_ATT) { adj[A_NEW][deg[A_NEW]++] = y; adj[y][deg[y]++] = A_NEW; }
        if (i < NBX_ATT) { adj[B_NEW][deg[B_NEW]++] = x; adj[x][deg[x]++] = B_NEW; }
    }
}

/* bit-parallel ball iteration: bad = unordered pairs at distance > 5 */
static int bad_count(const int *rem, int k) {
    build(rem, k, 1);
    long tot = 0;
    for (int s0 = 0; s0 < NN; s0 += 64) {
        int ns = NN - s0 < 64 ? NN - s0 : 64;
        uint64_t full = ns == 64 ? ~0ULL : ((1ULL << ns) - 1);
        uint64_t *cur = M0, *nx = M1;
        memset(cur, 0, sizeof(uint64_t) * NN);
        for (int j = 0; j < ns; j++) cur[s0 + j] |= 1ULL << j;
        for (int lev = 0; lev < 5; lev++) {
            for (int x = 0; x < NN; x++) {
                uint64_t acc = cur[x];
                for (int i = 0; i < deg[x]; i++) acc |= cur[adj[x][i]];
                nx[x] = acc;
            }
            uint64_t *t = cur; cur = nx; nx = t;
        }
        for (int x = 0; x < NN; x++) tot += __builtin_popcountll(full & ~cur[x]);
    }
    return (int)(tot / 2);
}

static int compat(const int *sel, int k, int e) {
    for (int i = 0; i < k; i++)
        if (sel[i] == e || EU[sel[i]] == EU[e] || EV[sel[i]] == EV[e]) return 0;
    return 1;
}

/* all-pairs BFS on the current build (ins flag), returns dist matrix in dist (NN*NN) */
static void allpairs(unsigned char *dist) {
    static int q[NN];
    for (int s = 0; s < NN; s++) {
        unsigned char *d = dist + (size_t)s * NN;
        memset(d, 255, NN);
        int h = 0, t = 0; d[s] = 0; q[t++] = s;
        while (h < t) { int x = q[h++]; for (int i = 0; i < deg[x]; i++) { int y = adj[x][i]; if (d[y] == 255) { d[y] = d[x] + 1; q[t++] = y; } } }
    }
}

static void base_dist(void) {
    static int q[NB];
    for (int s = 0; s < NB; s++) {
        unsigned char *d = D0[s];
        memset(d, 255, NB);
        int h = 0, t = 0; d[s] = 0; q[t++] = s;
        while (h < t) { int x = q[h++]; for (int i = 0; i < degB[x]; i++) { int y = adjB[x][i]; if (d[y] == 255) { d[y] = d[x] + 1; q[t++] = y; } } }
    }
}

static void write_graph(const char *path, const int *rem, int k) {
    build(rem, k, 1);
    FILE *f = fopen(path, "w");
    fprintf(f, "%d\n", NN);
    for (int v = 0; v < NN; v++) for (int i = 0; i < deg[v]; i++) if (adj[v][i] > v) fprintf(f, "%d %d\n", v, adj[v][i]);
    fclose(f);
}

static void report(const int *rem, int k) {
    static unsigned char dist[NN * NN], dnoins[NN * NN];
    build(rem, k, 0); allpairs(dnoins);
    build(rem, k, 1); allpairs(dist);
    int pre = 0;                 /* damaged old pairs before insertion (bad in graph minus a,b) */
    int unrep = 0, same[6] = {0}, cross[6] = {0};   /* by base distance (2..5) */
    int newc[4] = {0};          /* a-A, a-B, b-A, b-B bad pairs */
    int bad_total = 0; static int kind[10][10]; memset(kind, 0, sizeof kind);
    for (int u = 0; u < NB; u++) for (int v = u + 1; v < NB; v++) if (dnoins[(size_t)u * NN + v] > 5) pre++;
    for (int u = 0; u < NN; u++) for (int v = u + 1; v < NN; v++) {
        if (dist[(size_t)u * NN + v] <= 5) continue;
        bad_total++;
        if (u < NB && v < NB) {
            unrep++;
            int d0 = D0[u][v]; int sm = ((u < 342) == (v < 342));
            if (sm) same[d0 < 6 ? d0 : 5]++; else cross[d0 < 6 ? d0 : 5]++;
            if (d0 <= 5) {   /* kind (near,far) of the first deleted edge on a base shortest path (as damage684.c) */
                int found = 0;
                for (int i = 0; i < k && !found; i++) {
                    int x = EU[rem[i]], y = EV[rem[i]];
                    int p1 = D0[u][x], r1 = D0[y][v], p2 = D0[u][y], r2 = D0[x][v];
                    int p = -1, r = -1;
                    if (p1 + 1 + r1 == d0) { p = p1; r = r1; } else if (p2 + 1 + r2 == d0) { p = p2; r = r2; }
                    if (p >= 0) { if (p > r) { int t = p; p = r; r = t; } kind[p][r]++; found = 1; }
                }
                if (!found) kind[9][9]++;
            }
        } else {
            int w = u >= NB ? u : v; int o = u >= NB ? v : u;   /* w new, o old or b */
            if (w == B_NEW && o == A_NEW) continue;
            int oa = (o < 342) || o == A_NEW;   /* old endpoint side (a is side A) */
            if (w == A_NEW) newc[oa ? 0 : 1]++; else newc[oa ? 2 : 3]++;
        }
    }
    printf("RESULT bad=%d unrepaired_old=%d damaged_pre_insert=%d repaired=%d new_pairs(a-A,a-B,b-A,b-B)=%d,%d,%d,%d\n",
           bad_total, unrep, pre, pre - unrep, newc[0], newc[1], newc[2], newc[3]);
    printf("  unrepaired old pairs by (near,far) kind of first deleted edge on a base shortest path:");
    for (int p = 0; p < 10; p++) for (int r = 0; r < 10; r++) if (kind[p][r]) printf(" (%d,%d):%d", p, r, kind[p][r]);
    printf("\n");
    printf("  unrepaired old same-side by base dist: d2=%d d4=%d d(other)=%d ; old cross by base dist: d1=%d d3=%d d5=%d d(other)=%d\n",
           same[2], same[4], same[0] + same[1] + same[3] + same[5], cross[1], cross[3], cross[5], cross[0] + cross[2] + cross[4]);
}

static void print_sel(const int *sel, int k) {
    for (int i = 0; i < k; i++) printf(" %d:%d", EU[sel[i]], EV[sel[i]]);
    printf("\n");
}

static void load(const char *path) {
    FILE *f = fopen(path, "r");
    int n; if (fscanf(f, "%d", &n) != 1) exit(2);
    int u, v; m0 = 0;
    while (fscanf(f, "%d %d", &u, &v) == 2) {
        if (u >= NB || v >= NB) { fprintf(stderr, "bad vertex\n"); exit(2); }
        if (u >= 342) { int t = u; u = v; v = t; }
        if (u >= 342 || v < 342) { fprintf(stderr, "not bipartite A-B orientation\n"); exit(2); }
        EU[m0] = u; EV[m0] = v;
        adjB[u][degB[u]] = v; adjE[u][degB[u]] = m0; degB[u]++;
        adjB[v][degB[v]] = u; adjE[v][degB[v]] = m0; degB[v]++;
        m0++;
    }
    fclose(f);
    base_dist();
}

static int edge_id(int x, int y) {
    for (int i = 0; i < degB[x]; i++) if (adjB[x][i] == y) return adjE[x][i];
    return -1;
}

/* ---------------- beam search ---------------- */
typedef struct { int val; uint64_t key; int sel[8]; } cand_t;
static int cmp_cand(const void *a, const void *b) { const cand_t *x = a, *y = b; return (x->val > y->val) - (x->val < y->val); }
static uint64_t hr[2100];

static int beam(int K, int W, const char *out) {
    static cand_t beamst[64], cand[64 * 2100];
    int nb = 1; memset(&beamst[0], 0, sizeof beamst[0]); beamst[0].val = 0; beamst[0].key = 0;
    for (int l = 0; l < K; l++) {
        int nc = 0;
        for (int s = 0; s < nb; s++) {
            for (int e = 0; e < m0; e++) {
                if (!compat(beamst[s].sel, l, e)) continue;
                cand_t *c = &cand[nc++];
                memcpy(c->sel, beamst[s].sel, sizeof c->sel); c->sel[l] = e;
                c->key = beamst[s].key + hr[e];
                c->val = bad_count(c->sel, l + 1);
            }
        }
        qsort(cand, nc, sizeof(cand_t), cmp_cand);
        nb = 0;
        for (int i = 0; i < nc && nb < W; i++) {
            int dup = 0; for (int j = 0; j < nb; j++) if (beamst[j].key == cand[i].key) { dup = 1; break; }
            if (dup) continue;
            beamst[nb++] = cand[i];
        }
        printf("level %d: best %d (", l + 1, beamst[0].val); print_sel(beamst[0].sel, l + 1); printf(")\n"); fflush(stdout);
    }
    printf("BEST bad=%d", beamst[0].val); print_sel(beamst[0].sel, K);
    if (out) write_graph(out, beamst[0].sel, K);
    return beamst[0].val;
}

int main(int argc, char **argv) {
    if (argc < 2) { fprintf(stderr, "usage: see header\n"); return 2; }
    load("/home/user/degree-diameter/research/squads/deep-65/shared/h684.edges");
    for (int i = 0; i < m0; i++) hr[i] = rnd() | 1;
    if (getenv("AB")) AB = atoi(getenv("AB"));
    if (getenv("NA")) NA_ATT = atoi(getenv("NA"));
    if (getenv("NBX")) NBX_ATT = atoi(getenv("NBX"));
    const char *mode = argv[1];
    if (!strcmp(mode, "eval")) {
        int K = atoi(argv[2]); int sel[8];
        for (int i = 0; i < K; i++) {
            int x = atoi(argv[3 + 2 * i]), y = atoi(argv[4 + 2 * i]);
            sel[i] = edge_id(x, y);
            if (sel[i] < 0) { printf("no base edge %d-%d\n", x, y); return 1; }
        }
        printf("bad=%d\n", bad_count(sel, K));
        report(sel, K);
        if (argc > 3 + 2 * K) write_graph(argv[3 + 2 * K], sel, K);
        return 0;
    }
    if (!strcmp(mode, "sa")) {
        int K = atoi(argv[2]); double secs = atof(argv[3]); uint64_t seed = strtoull(argv[4], 0, 10);
        double T0 = atof(argv[5]), T1 = atof(argv[6]);
        rs = seed * 0x9E3779B97F4A7C15ULL + 1234567ULL; for (int i = 0; i < 20; i++) rnd();
        int sel[8], bsel[8]; for (int i = 0; i < K;) { int e = rnd() % m0; if (compat(sel, i, e)) sel[i++] = e; }
        if (getenv("INIT")) {   /* start from given pairs "x1 y1 x2 y2 ..." */
            char *q = getenv("INIT"); for (int i = 0; i < K; i++) { int x = strtol(q, &q, 10), y = strtol(q, &q, 10); sel[i] = edge_id(x, y); if (sel[i] < 0) return 1; }
        }
        int cur = bad_count(sel, K), best = cur; memcpy(bsel, sel, sizeof bsel);
        double t0 = now(); long it = 0, acc = 0;
        for (;;) {
            double el = now() - t0; if (el > secs) break;
            double T = T0 * pow(T1 / T0, el / secs);
            int i = rnd() % K, e = rnd() % m0;
            if (!compat(sel, K, e) && 0) continue;
            int ok = 1; for (int j = 0; j < K; j++) if (j != i && (sel[j] == e || EU[sel[j]] == EU[e] || EV[sel[j]] == EV[e])) ok = 0;
            it++; if (!ok) continue;
            int old = sel[i]; sel[i] = e; int val = bad_count(sel, K);
            if (val <= cur || u01() < exp((cur - val) / T)) {
                cur = val; acc++;
                if (cur < best) { best = cur; memcpy(bsel, sel, sizeof bsel); }
            } else sel[i] = old;
        }
        printf("SA K=%d seed=%llu iters=%ld accepted=%ld best=%d", K, (unsigned long long)seed, it, acc, best);
        print_sel(bsel, K);
        report(bsel, K);
        if (argc > 7) write_graph(argv[7], bsel, K);
        return 0;
    }
    if (!strcmp(mode, "nbr")) {
        /* full 1-exchange neighbourhood of a given selection; prints the best neighbour (ties counted) */
        int K = atoi(argv[2]); int sel[8];
        for (int i = 0; i < K; i++) { sel[i] = edge_id(atoi(argv[3 + 2 * i]), atoi(argv[4 + 2 * i])); if (sel[i] < 0) return 1; }
        int base = bad_count(sel, K); int best = 1 << 30, nbest = 0; int bs[8];
        long hist[400] = {0};
        for (int i = 0; i < K; i++) {
            int keep = sel[i];
            for (int e = 0; e < m0; e++) {
                int ok = 1; for (int j = 0; j < K; j++) if (j != i && (sel[j] == e || EU[sel[j]] == EU[e] || EV[sel[j]] == EV[e])) ok = 0;
                if (!ok || e == keep) continue;
                sel[i] = e; int v = bad_count(sel, K);
                if (v < 400) hist[v]++;
                if (v < best) { best = v; nbest = 0; memcpy(bs, sel, sizeof bs); }
                if (v == best) nbest++;
            }
            sel[i] = keep;
        }
        printf("NBR base=%d best_neighbour=%d (ties %d) ", base, best, nbest); print_sel(bs, K);
        printf("hist(<=base+0..):"); for (int v = 0; v < 400 && v <= base; v++) if (hist[v]) printf(" %d:%ld", v, hist[v]);
        printf("\n");
        return 0;
    }
    if (!strcmp(mode, "two")) {
        /* 2-exchange over candidate edges: candidates = edges giving the best single-exchange values (top T), then all
           pairs of positions (i,j) with replacements from the candidate set. Usage: two K x1 y1 .. (env T, default 150) */
        int K = atoi(argv[2]); int sel[8];
        for (int i = 0; i < K; i++) { sel[i] = edge_id(atoi(argv[3 + 2 * i]), atoi(argv[4 + 2 * i])); if (sel[i] < 0) return 1; }
        int T = getenv("T") ? atoi(getenv("T")) : 150; double t0 = now();
        int base = bad_count(sel, K);
        static int candv[2100]; static int candlist[2100]; int nc = 0;
        /* best single-exchange value per edge over positions */
        static int bestv[2100]; for (int e = 0; e < m0; e++) bestv[e] = 1 << 30;
        for (int i = 0; i < K; i++) {
            int keep = sel[i];
            for (int e = 0; e < m0; e++) {
                int ok = 1; for (int j = 0; j < K; j++) if (j != i && (sel[j] == e || EU[sel[j]] == EU[e] || EV[sel[j]] == EV[e])) ok = 0;
                if (!ok || e == keep) continue;
                sel[i] = e; int v = bad_count(sel, K); if (v < bestv[e]) bestv[e] = v;
            }
            sel[i] = keep;
        }
        for (int e = 0; e < m0; e++) if (bestv[e] < (1 << 30)) candv[nc] = bestv[e], candlist[nc++] = e;
        /* sort candidate indices by value (simple selection of T smallest) */
        for (int a = 0; a < nc && a < T; a++) { int bi = a; for (int b = a + 1; b < nc; b++) if (candv[b] < candv[bi]) bi = b;
            int tv = candv[a]; candv[a] = candv[bi]; candv[bi] = tv; int tl = candlist[a]; candlist[a] = candlist[bi]; candlist[bi] = tl; }
        int C = nc < T ? nc : T;
        printf("base=%d candidates=%d (time %.1fs)\n", base, C, now() - t0); fflush(stdout);
        int best = base, bsel[8]; memcpy(bsel, sel, sizeof bsel); long cnt = 0;
        for (int i = 0; i < K; i++) for (int j = i + 1; j < K; j++) {
            int oi = sel[i], oj = sel[j];
            for (int a = 0; a < C; a++) for (int b = 0; b < C; b++) {
                int ea = candlist[a], eb = candlist[b];
                if (ea == eb) continue;
                sel[i] = ea; sel[j] = eb;
                int ok = 1; for (int q = 0; q < K; q++) for (int r = q + 1; r < K; r++) if (EU[sel[q]] == EU[sel[r]] || EV[sel[q]] == EV[sel[r]] || sel[q] == sel[r]) ok = 0;
                if (!ok) continue;
                int v = bad_count(sel, K); cnt++;
                if (v < best) { best = v; memcpy(bsel, sel, sizeof bsel); printf("improved %d:", v); print_sel(bsel, K); fflush(stdout); }
                if (now() - t0 > 100) goto twodone;
            }
            sel[i] = oi; sel[j] = oj;
        }
        twodone:
        printf("TWO evaluated=%ld best=%d", cnt, best); print_sel(bsel, K);
        report(bsel, K);
        if (argc > 3 + 2 * K) write_graph(argv[3 + 2 * K], bsel, K);
        return 0;
    }
    if (!strcmp(mode, "beam")) {
        int K = atoi(argv[2]), W = atoi(argv[3]);
        beam(K, W, argc > 4 ? argv[4] : NULL);
        int sel[8]; (void)sel;
        return 0;
    }
    if (!strcmp(mode, "star")) {
        double secs = argc > 2 ? atof(argv[2]) : 90; double t0 = now();
        int w = adjB[0][0]; /* any B vertex; B-vertex 342 is in orbit of all (group acts transitively on B) */
        w = NB - 1 > 0 ? 342 : w;
        int X[6], nX = 0; for (int i = 0; i < degB[w]; i++) X[nX++] = adjB[w][i];
        long cnt = 0, best_cnt = 0; int best = 1 << 30; int bsel[8];
        for (int drop = 0; drop < 6; drop++) {
            int xs[5], nx = 0; for (int i = 0; i < 6; i++) if (i != drop) xs[nx++] = X[i];
            int c[5];
            for (c[0] = 0; c[0] < 6; c[0]++) for (c[1] = 0; c[1] < 6; c[1]++) for (c[2] = 0; c[2] < 6; c[2]++)
            for (c[3] = 0; c[3] < 6; c[3]++) for (c[4] = 0; c[4] < 6; c[4]++) {
                int sel[8], ok = 1;
                for (int i = 0; i < 5; i++) { int x = xs[i]; int y = adjB[x][c[i]]; sel[i] = adjE[x][c[i]]; (void)y; }
                for (int i = 0; i < 5 && ok; i++) for (int j = 0; j < i; j++) if (EV[sel[i]] == EV[sel[j]]) ok = 0;
                if (!ok) continue;
                int v = bad_count(sel, 5); cnt++;
                if (v < best) { best = v; memcpy(bsel, sel, sizeof bsel); }
                if (now() - t0 > secs) { drop = 6; break; }
            }
        }
        printf("STAR evaluated=%ld best=%d", cnt, best); print_sel(bsel, 5); report(bsel, 5);
        (void)best_cnt;
        return 0;
    }
    if (!strcmp(mode, "star6")) {
        /* generalised (i) for K = 6 (use AB=0): all six x_i = N(w) for one B-vertex w = 342, y_i in N(x_i) distinct */
        double secs = argc > 2 ? atof(argv[2]) : 90; double t0 = now();
        int w = 342; int X[6], nX = 0; for (int i = 0; i < degB[w]; i++) X[nX++] = adjB[w][i];
        long cnt = 0; int best = 1 << 30; int bsel[8]; int c[6];
        for (c[0] = 0; c[0] < degB[X[0]]; c[0]++) for (c[1] = 0; c[1] < degB[X[1]]; c[1]++) for (c[2] = 0; c[2] < degB[X[2]]; c[2]++)
        for (c[3] = 0; c[3] < degB[X[3]]; c[3]++) for (c[4] = 0; c[4] < degB[X[4]]; c[4]++) for (c[5] = 0; c[5] < degB[X[5]]; c[5]++) {
            int sel[8], ok = 1;
            for (int i = 0; i < 6; i++) sel[i] = adjE[X[i]][c[i]];
            for (int i = 0; i < 6 && ok; i++) for (int j = 0; j < i; j++) if (EV[sel[i]] == EV[sel[j]]) ok = 0;
            if (!ok) continue;
            int v = bad_count(sel, 6); cnt++;
            if (v < best) { best = v; memcpy(bsel, sel, sizeof bsel); }
            if ((cnt & 63) == 0 && now() - t0 > secs) goto done6;
        }
        done6:
        printf("STAR6 evaluated=%ld best=%d", cnt, best); print_sel(bsel, 6); report(bsel, 6);
        return 0;
    }
    if (!strcmp(mode, "cycle6")) {
        /* random sampling of closed alternating cycles x1 y1 .. x6 y6 through x1 = 0 (K = 6, AB=0): deleted (x_i,y_i),
           kept (y_i,x_{i+1}) and (y6,x1). Random DFS order, evaluated until SECS runs out. */
        double secs = argc > 2 ? atof(argv[2]) : 90; rs = 777ULL * (argc > 3 ? atoll(argv[3]) : 1) + 99;
        double t0 = now(); long cnt = 0; int best = 1 << 30; int bsel[8];
        int xs[6], ys[6]; xs[0] = 0; long tries = 0;
        for (;;) {
            /* one random DFS descent with restarts; depth d chooses y_d then x_{d+1} (or closes at depth 6) */
            int d = 0; int ch[12]; int nchoice[12]; int pos[12];
            /* stack of candidate lists is built lazily: pick random neighbour ordering per level */
            int stop = 0;
            /* depth-first with random start index and random direction, full scan of each level */
            int okpath = 1; int lvl = 0; int ordv[12][6]; int nn_[12];
            for (int l = 0; l < 11; l++) nn_[l] = -1;
            #define BUILD_LEVEL(l, from) { nn_[l] = 0; int dd = degB[from]; int off = rnd() % (dd ? dd : 1); \
                for (int t = 0; t < dd; t++) ordv[l][nn_[l]++] = adjB[from][(t + off) % dd]; }
            /* level l even: choose y_{l/2+1} from neighbours of x; level l odd: choose x from neighbours of y */
            int cur_node = 0; (void)cur_node; (void)okpath; (void)d; (void)ch; (void)nchoice; (void)pos; (void)stop;
            int used_x[7], used_y[7]; int cntu = 0; (void)cntu; (void)used_x; (void)used_y; (void)lvl;
            /* explicit iterative random DFS over 11 steps */
            int depthv[12]; int idxl[12];
            int L = 0; BUILD_LEVEL(0, 0);
            idxl[0] = 0; int sx[12]; sx[0] = 0; int found = 0;
            while (L >= 0) {
                if (idxl[L] >= nn_[L]) { L--; if (L >= 0) idxl[L]++; continue; }
                int v = ordv[L][idxl[L]];
                /* check distinctness of the new vertex against the path so far */
                int path_v[12]; int np = 0; (void)path_v; (void)np;
                int vert_ok = 1;
                if (L % 2 == 0) { /* v is a B-vertex y, stored at sx[L+1]; earlier y's at odd indices 1..L-1 */
                    for (int j = 1; j < L; j += 2) if (sx[j] == v) vert_ok = 0;
                } else {          /* v is an A-vertex x, stored at sx[L+1]; earlier x's at even indices 0..L-1 */
                    for (int j = 0; j < L; j += 2) if (sx[j] == v) vert_ok = 0;
                }
                if (!vert_ok) { idxl[L]++; continue; }
                sx[L + 1] = v;
                if (L == 10) { /* last step: v is y6 and must be adjacent to 0 */
                    if (edge_id(0, v) >= 0) { found = 1; sx[11] = v; break; }
                    idxl[L]++; continue;
                }
                /* descend: next level chooses from neighbours of v */
                L++; BUILD_LEVEL(L, v); idxl[L] = 0;
                (void)depthv;
            }
            tries++;
            if (!found) { if (now() - t0 > secs) break; continue; }
            /* sx[0]=x1=0, sx[1]=y1, sx[2]=x2, ..., sx[10]=x6?, sx[11]=y6: vertices along the cycle */
            int sel[8]; int ok = 1;
            for (int i = 0; i < 6; i++) {
                int xv = sx[2 * i], yv = sx[2 * i + 1];
                sel[i] = edge_id(xv, yv); if (sel[i] < 0) ok = 0;
            }
            if (!ok) continue;
            cnt++;
            int v = bad_count(sel, 6);
            if (v < best) { best = v; memcpy(bsel, sel, sizeof bsel); printf("new best %d:", v); print_sel(bsel, 6); fflush(stdout); }
            if (now() - t0 > secs) break;
        }
        printf("CYCLE6 tries=%ld evaluated=%ld best=%d", tries, cnt, best); print_sel(bsel, 6);
        report(bsel, 6);
        return 0;
    }
    if (!strcmp(mode, "cycle")) {
        double secs = argc > 2 ? atof(argv[2]) : 90; double t0 = now();
        /* closed alternating cycles x1 y1 x2 y2 .. x5 y5 (x1 = 0 WLOG): deleted (x_i,y_i), kept (y_i,x_{i+1}), (y5,x1) */
        long cnt = 0, closed = 0; int best = 1 << 30; int bsel[8];
        int xs[5], ys[5]; xs[0] = 0;
        int stop = 0;
        /* iterative DFS over 9 steps: depth d: 0 -> choose y1; 1 -> x2; ... 8 -> y5 must be adjacent to 0 */
        int idx[10] = {0}; int nch[10];
        int stepv[10];
        /* generic recursion via explicit function-like loops */
        #define OK_Y(yv, depth) 1
        int y1, x2, y2, x3, y3, x4, y4, x5, y5;
        for (int i1 = 0; i1 < degB[0] && !stop; i1++) { y1 = adjB[0][i1];
        for (int i2 = 0; i2 < degB[y1] && !stop; i2++) { x2 = adjB[y1][i2]; if (x2 == 0) continue;
        for (int i3 = 0; i3 < degB[x2] && !stop; i3++) { y2 = adjB[x2][i3]; if (y2 == y1) continue;
        for (int i4 = 0; i4 < degB[y2] && !stop; i4++) { x3 = adjB[y2][i4]; if (x3 == 0 || x3 == x2) continue;
        for (int i5 = 0; i5 < degB[x3] && !stop; i5++) { y3 = adjB[x3][i5]; if (y3 == y1 || y3 == y2) continue;
        for (int i6 = 0; i6 < degB[y3] && !stop; i6++) { x4 = adjB[y3][i6]; if (x4 == 0 || x4 == x2 || x4 == x3) continue;
        for (int i7 = 0; i7 < degB[x4] && !stop; i7++) { y4 = adjB[x4][i7]; if (y4 == y1 || y4 == y2 || y4 == y3) continue;
        for (int i8 = 0; i8 < degB[y4] && !stop; i8++) { x5 = adjB[y4][i8]; if (x5 == 0 || x5 == x2 || x5 == x3 || x5 == x4) continue;
        for (int i9 = 0; i9 < degB[x5] && !stop; i9++) { y5 = adjB[x5][i9];
            if (y5 == y1 || y5 == y2 || y5 == y3 || y5 == y4) continue;
            if (edge_id(0, y5) < 0) continue;   /* kept closing edge (y5, x1 = 0) */
            closed++;
            int sel[8]; xs[1]=x2; xs[2]=x3; xs[3]=x4; xs[4]=x5; ys[0]=y1; ys[1]=y2; ys[2]=y3; ys[3]=y4; ys[4]=y5;
            sel[0] = edge_id(0, y1); sel[1] = edge_id(x2, y2); sel[2] = edge_id(x3, y3); sel[3] = edge_id(x4, y4); sel[4] = edge_id(x5, y5);
            cnt++;
            int v = bad_count(sel, 5);
            if (v < best) { best = v; memcpy(bsel, sel, sizeof bsel); printf("new best %d:", v); print_sel(bsel, 5); fflush(stdout); }
            if ((cnt & 255) == 0 && now() - t0 > secs) stop = 1;
        }}}}}}}}}
        printf("CYCLE closed=%ld evaluated=%ld stopped_early=%d best=%d", closed, cnt, stop, best); print_sel(bsel, 5);
        report(bsel, 5);
        return 0;
    }
    fprintf(stderr, "unknown mode\n");
    return 2;
}
