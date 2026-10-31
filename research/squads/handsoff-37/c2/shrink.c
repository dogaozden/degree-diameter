/* c2 shrink engine (handsoff-37, card c2).
   Cubic bipartite graphs, sides A = side 0, B = side 1, vertices kept with A first.
   far = number of unordered vertex pairs at distance > 7 (unreachable counts).
   Modes:
     shrink sa    IN steps T0 T1 seed OUT [focus_pct]        simulated annealing over 2-switches at fixed n
     shrink beam  IN target width sa_steps T0 T1 seed TAG [nonadj 0|1] [focus_pct]
                  beam search over reductions n -> n-2 -> ... -> target, SA after each level
   Edge format: first number n, then "a b" per edge (0-based). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>

#define MAXN 256
#define MAXW 4

typedef struct { int n; int side[MAXN]; int adj[MAXN][3]; } G;

static uint64_t vis[MAXN][MAXW], fr[MAXN][MAXW], nx[MAXN][MAXW];
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) {
    uint64_t z = (rs += 0x9E3779B97F4A7C15ULL);
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL; z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
    return z ^ (z >> 31);
}
static inline double urand(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
static inline int irand(int m) { return (int)(rnd() % (uint64_t)m); }

/* far cost: all sources at once, depth 7. Fills badl with vertices that have an unreached partner. */
static int far_cost(const G *g, int *badl, int *nbad) {
    int n = g->n, nw = (n + 63) >> 6;
    for (int x = 0; x < n; x++) for (int w = 0; w < nw; w++) vis[x][w] = fr[x][w] = 0;
    for (int x = 0; x < n; x++) { vis[x][x >> 6] |= 1ULL << (x & 63); fr[x][x >> 6] |= 1ULL << (x & 63); }
    for (int lev = 1; lev <= 7; lev++) {
        uint64_t any = 0;
        for (int x = 0; x < n; x++) {
            const int *a = g->adj[x];
            for (int w = 0; w < nw; w++) {
                uint64_t acc = (fr[a[0]][w] | fr[a[1]][w] | fr[a[2]][w]) & ~vis[x][w];
                nx[x][w] = acc; any |= acc;
            }
        }
        if (!any) break;
        for (int x = 0; x < n; x++) for (int w = 0; w < nw; w++) { vis[x][w] |= nx[x][w]; fr[x][w] = nx[x][w]; }
    }
    long tot = 0; int nb = 0;
    for (int x = 0; x < n; x++) {
        int bad = 0;
        for (int w = 0; w < nw; w++) {
            uint64_t valid = (64 * (w + 1) <= n) ? ~0ULL : ((1ULL << (n - 64 * w)) - 1);
            uint64_t u = valid & ~vis[x][w];
            if (u) bad = 1;
            tot += __builtin_popcountll(u);
        }
        if (bad && badl) badl[nb++] = x;
    }
    if (nbad) *nbad = nb;
    return (int)(tot / 2);
}

static int has_edge(const G *g, int x, int y) { return g->adj[x][0] == y || g->adj[x][1] == y || g->adj[x][2] == y; }
static void repl(int adj[][3], int x, int from, int to) {
    for (int k = 0; k < 3; k++) if (adj[x][k] == from) { adj[x][k] = to; return; }
    fprintf(stderr, "repl failed\n"); exit(3);
}
/* (a,b),(c,d) -> (a,d),(c,b); a,c in A, b,d in B */
static int try_switch(G *g, int a, int b, int c, int d) {
    if (a == c || b == d) return 0;
    if (has_edge(g, a, d) || has_edge(g, c, b)) return 0;
    repl(g->adj, a, b, d); repl(g->adj, b, a, c); repl(g->adj, c, d, b); repl(g->adj, d, c, a);
    return 1;
}
static void undo_switch(G *g, int a, int b, int c, int d) {
    repl(g->adj, a, d, b); repl(g->adj, c, b, d); repl(g->adj, b, c, a); repl(g->adj, d, a, c);
}

/* renumber: drop removed vertices, A first then B */
static void normalize(int n, const int *side, int adj[][3], const int *removed, G *out) {
    int map[MAXN], m = 0;
    for (int s = 0; s < 2; s++) for (int x = 0; x < n; x++) if (!removed[x] && side[x] == s) { map[x] = m; out->side[m] = s; m++; }
    out->n = m;
    for (int x = 0; x < n; x++) if (!removed[x]) {
        int nx_ = map[x];
        for (int k = 0; k < 3; k++) out->adj[nx_][k] = map[adj[x][k]];
    }
}

/* reduce: delete a (in A) and b (in B), match the leftover neighbours N(a)-b (in B) with N(b)-a (in A) by perm */
static int reduce(const G *g, int a, int b, const int *perm, int k, G *out) {
    int P[3], Q[3], np = 0, nq = 0;
    for (int i = 0; i < 3; i++) if (g->adj[a][i] != b) P[np++] = g->adj[a][i];
    for (int i = 0; i < 3; i++) if (g->adj[b][i] != a) Q[nq++] = g->adj[b][i];
    if (np != k || nq != k) return 0;
    int adj[MAXN][3]; memcpy(adj, g->adj, sizeof(int) * 3 * g->n);
    for (int i = 0; i < k; i++) {
        int p = P[i], q = Q[perm[i]];
        if (has_edge(g, p, q)) return 0;
        repl(adj, p, a, q); repl(adj, q, b, p);
    }
    int removed[MAXN] = {0};
    removed[a] = removed[b] = 1;
    normalize(g->n, g->side, adj, removed, out);
    return 1;
}

static const int PERM2[2][2] = {{0, 1}, {1, 0}};
static const int PERM3[6][3] = {{0,1,2},{0,2,1},{1,0,2},{1,2,0},{2,0,1},{2,1,0}};

static int nA(const G *g) { int c = 0; for (int x = 0; x < g->n; x++) c += g->side[x] == 0; return c; }

static int read_graph(const char *fn, G *g) {
    FILE *f = fopen(fn, "r"); if (!f) { perror(fn); exit(2); }
    int n; if (fscanf(f, "%d", &n) != 1) exit(2);
    static int raw[MAXN][3]; int deg[MAXN] = {0}; int a, b;
    while (fscanf(f, "%d %d", &a, &b) == 2) { raw[a][deg[a]++] = b; raw[b][deg[b]++] = a; }
    fclose(f);
    int side[MAXN]; for (int i = 0; i < n; i++) side[i] = -1;
    side[0] = 0; int q[MAXN], h = 0, t = 0; q[t++] = 0;
    while (h < t) { int x = q[h++]; for (int k = 0; k < deg[x]; k++) { int y = raw[x][k]; if (side[y] < 0) { side[y] = 1 - side[x]; q[t++] = y; } } }
    for (int i = 0; i < n; i++) if (deg[i] != 3) { fprintf(stderr, "vertex %d has degree %d (need cubic)\n", i, deg[i]); exit(2); }
    int removed[MAXN] = {0};
    normalize(n, side, raw, removed, g);
    return n;
}

static int write_graph(const G *g, const char *fn) {
    FILE *f = fopen(fn, "w"); if (!f) return 0;
    fprintf(f, "%d\n", g->n);
    for (int x = 0; x < g->n; x++) if (g->side[x] == 0) for (int k = 0; k < 3; k++) fprintf(f, "%d %d\n", x, g->adj[x][k]);
    fclose(f); return 1;
}

static uint64_t mix64(uint64_t z) { z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL; z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL; return z ^ (z >> 31); }
static uint64_t ghash(const G *g) {
    uint64_t h = 0;
    for (int x = 0; x < g->n; x++) if (g->side[x] == 0) for (int k = 0; k < 3; k++) h += mix64((uint64_t)x * 1024 + g->adj[x][k]);
    return h;
}

/* simulated annealing over edge switches at fixed n; focus_pct % of the moves start at a vertex with far pairs */
static int sa_run(G *g, long steps, double T0, double T1, int focus_pct, G *best, int verbose) {
    static int badA[MAXN], badB[MAXN];
    int *badc = badA, *badn = badB; int nbc = 0, nbn = 0;
    int f = far_cost(g, badc, &nbc);
    int bestf = f; *best = *g;
    int na = nA(g), n = g->n;
    int *Alist = malloc(sizeof(int) * na); int c = 0;
    for (int x = 0; x < n; x++) if (g->side[x] == 0) Alist[c++] = x;
    for (long s = 0; s < steps && bestf > 0; s++) {
        double T = T0 * pow(T1 / T0, (double)s / (double)steps);
        int a, b, cc, d;
        if (nbc > 0 && (int)(rnd() % 100) < focus_pct) {
            int x = badc[irand(nbc)];
            int p = x; int walk = irand(3);
            for (int t = 0; t < walk; t++) p = g->adj[p][irand(3)];
            int q = g->adj[p][irand(3)];
            if (g->side[p] == 0) { a = p; b = q; } else { a = q; b = p; }
            cc = Alist[irand(na)]; d = g->adj[cc][irand(3)];
        } else {
            a = Alist[irand(na)]; b = g->adj[a][irand(3)];
            cc = Alist[irand(na)]; d = g->adj[cc][irand(3)];
        }
        if (verbose >= 2 && s % 20000 == 0) fprintf(stderr, "    s=%ld T=%.3f cur=%d best=%d\n", s, T, f, bestf);
        if (!try_switch(g, a, b, cc, d)) continue;
        int nf = far_cost(g, badn, &nbn);
        int delta = nf - f;
        if (delta <= 0 || urand() < exp(-delta / T)) {
            f = nf; int *tb = badc; badc = badn; badn = tb; nbc = nbn;
            if (f < bestf) { bestf = f; *best = *g; if (verbose) fprintf(stderr, "  step %ld T=%.3f best %d\n", s, T, bestf); }
        } else {
            undo_switch(g, a, b, cc, d);
        }
    }
    free(Alist);
    return bestf;
}


/* tabu search: each step samples K focused 2-switches, applies the best non-tabu one (aspiration on new best).
   A switch removes edges ab, cd; they become tabu for re-creation for TEN steps. */
static int tabu_tab[MAXN][MAXN];
static int tabu_run(G *g, long iters, int K, int TEN, int *nopt, G *best, int verbose) {
    static int badA[MAXN], badB[MAXN];
    int *badc = badA, *badn = badB; int nbc = 0, nbn = 0;
    int f = far_cost(g, badc, &nbc);
    int bestf = f; *best = *g;
    int n = g->n, na = nA(g);
    int *Alist = malloc(sizeof(int) * na); int c = 0;
    for (int x = 0; x < n; x++) if (g->side[x] == 0) Alist[c++] = x;
    memset(tabu_tab, 0, sizeof tabu_tab);
    for (long it = 1; it <= iters && bestf > 0; it++) {
        int bfa = -1, bfb = -1, bfc = -1, bfd = -1, bestcand = 1 << 30, cnt = 0;
        for (int k = 0; k < K; k++) {
            int a, b, cc, d;
            int x1 = badc[irand(nbc)];
            int p = x1; int w = irand(3);
            for (int t = 0; t < w; t++) p = g->adj[p][irand(3)];
            int q = g->adj[p][irand(3)];
            if (g->side[p] == 0) { a = p; b = q; } else { a = q; b = p; }
            if (rnd() % 10 < 7) { int x2 = badc[irand(nbc)]; p = x2; w = irand(3); for (int t = 0; t < w; t++) p = g->adj[p][irand(3)]; q = g->adj[p][irand(3)];
                if (g->side[p] == 0) { cc = p; d = q; } else { cc = q; d = p; } }
            else { cc = Alist[irand(na)]; d = g->adj[cc][irand(3)]; }
            if (a == cc || b == d) continue;
            if (has_edge(g, a, d) || has_edge(g, cc, b)) continue;
            if (tabu_tab[a][d] > it || tabu_tab[cc][b] > it) { /* tabu: only aspiration */
                if (1) { /* evaluate anyway, reject unless it beats best */ }
                int tmp_ok = 1; (void)tmp_ok;
                if (try_switch(g, a, b, cc, d)) {
                    int nf = far_cost(g, badn, &nbn);
                    undo_switch(g, a, b, cc, d);
                    if (nf < bestf) { /* aspiration */
                        if (nf < bestcand) { bestcand = nf; bfa = a; bfb = b; bfc = cc; bfd = d; cnt = 1; }
                    }
                }
                continue;
            }
            if (!try_switch(g, a, b, cc, d)) continue;
            int nf = far_cost(g, badn, &nbn);
            undo_switch(g, a, b, cc, d);
            cnt++;
            if (nf < bestcand || (nf == bestcand && (rnd() & 1))) { bestcand = nf; bfa = a; bfb = b; bfc = cc; bfd = d; }
        }
        if (bfa < 0) continue;
        /* apply chosen move */
        try_switch(g, bfa, bfb, bfc, bfd);
        tabu_tab[bfa][bfb] = tabu_tab[bfb][bfa] = (int)it + TEN;
        tabu_tab[bfc][bfd] = tabu_tab[bfd][bfc] = (int)it + TEN;
        f = far_cost(g, badc, &nbc);
        (*nopt)++;
        if (f < bestf) { bestf = f; *best = *g; if (verbose) fprintf(stderr, "    tabu it=%ld best=%d\n", it, bestf); }
    }
    free(Alist);
    return bestf;
}



/* ---- k-edge LNS with heat-bath over reconnections ----
   Remove k edges (a_i,b_i) with distinct endpoints near a bad vertex, then reconnect the a's to the b's by a permutation
   pi (new edges a_i - b_pi(i)); every valid pi is scored (far) and one is drawn with weight exp(-far/T). */
static int lns_valid[8][8];
static long lns_skip_ok = 0, lns_done = 0; static double lns_sum = 0;
static int lns_a[8], lns_b[8];
static void set_slot(G *g, int x, int from, int to) {
    for (int k = 0; k < 3; k++) if (g->adj[x][k] == from) { g->adj[x][k] = to; return; }
    fprintf(stderr, "set_slot failed %d %d %d\n", x, from, to); exit(4);
}
static void free_edge(G *g, int a, int b) { set_slot(g, a, b, -1); set_slot(g, b, a, -1); }
static void add_edge(G *g, int a, int b) {
    for (int k = 0; k < 3; k++) if (g->adj[a][k] == -1) { g->adj[a][k] = b; break; }
    for (int k = 0; k < 3; k++) if (g->adj[b][k] == -1) { g->adj[b][k] = a; break; }
}
static int lns_k, lns_perm_count;
static int lns_perms[720][8];
static void gen_perms(int k, int *cur, int used, int pos, int *cnt) {
    if (pos == k) { for (int i = 0; i < k; i++) lns_perms[*cnt][i] = cur[i]; (*cnt)++; return; }
    for (int j = 0; j < k; j++) if (!(used & (1 << j)) && lns_valid[pos][j]) { cur[pos] = j; gen_perms(k, cur, used | (1 << j), pos + 1, cnt); }
}
static int lns_run(G *g, long iters, int k, double T0, double T1, int R, G *best, int verbose) {
    static int badA[MAXN], badB[MAXN];
    int *badc = badA; int nbc = 0;
    int f = far_cost(g, badc, &nbc);
    int bestf = f; *best = *g;
    int n = g->n;
    static int bl2[MAXN];
    for (long it = 0; it < iters && bestf > 0; it++) {
        double T = T0 * pow(T1 / T0, (double)it / (double)iters);
        int centre = (nbc > 0) ? badc[irand(nbc)] : irand(n);
        /* ball of radius R around centre */
        static int dist[MAXN], qq[MAXN];
        for (int x = 0; x < n; x++) dist[x] = -1;
        int qh = 0, qt = 0; dist[centre] = 0; qq[qt++] = centre;
        while (qh < qt) { int x = qq[qh++]; if (dist[x] >= R) continue; for (int t = 0; t < 3; t++) { int y = g->adj[x][t]; if (dist[y] < 0) { dist[y] = dist[x] + 1; qq[qt++] = y; } } }
        /* pick k edges inside the ball with distinct endpoints */
        int ok = 0;
        for (int tries = 0; tries < 200 && !ok; tries++) {
            int cnt = 0; int usedA = 0, usedB = 0;
            for (int j = 0; j < qt && cnt < k; j++) { }
            /* random order over ball vertices */
            int tot = qt; int order_[MAXN]; for (int j = 0; j < tot; j++) order_[j] = qq[j];
            for (int j = tot - 1; j > 0; j--) { int r = irand(j + 1); int t2 = order_[j]; order_[j] = order_[r]; order_[r] = t2; }
            for (int j = 0; j < tot && cnt < k; j++) {
                int x = order_[j]; int ax, bx;
                if (g->side[x] == 0) { ax = x; bx = g->adj[x][irand(3)]; } else { bx = x; ax = g->adj[x][irand(3)]; }
                if (dist[ax] < 0 || dist[bx] < 0) continue;
                int ia = ax, ib = bx;
                int dupA = 0, dupB = 0;
                for (int c = 0; c < cnt; c++) { if (lns_a[c] == ia) dupA = 1; if (lns_b[c] == ib) dupB = 1; }
                if (dupA || dupB) continue;
                lns_a[cnt] = ia; lns_b[cnt] = ib; cnt++;
            }
            if (cnt == k) ok = 1;
        }
        if (!ok) { lns_skip_ok++; if (verbose >= 3 && lns_skip_ok < 4) fprintf(stderr, "skip: centre=%d qt=%d\n", centre, qt); continue; }
        /* validity matrix: new pair (a_i, b_j) must not already be an edge (other than the removed one for i==j) */
        for (int i = 0; i < k; i++) for (int j = 0; j < k; j++) {
            if (i == j) { lns_valid[i][j] = 1; continue; }
            int e = 0; for (int t = 0; t < 3; t++) if (g->adj[lns_a[i]][t] == lns_b[j]) e = 1;
            lns_valid[i][j] = !e;
        }
        lns_perm_count = 0; int cur[8];
        gen_perms(k, cur, 0, 0, &lns_perm_count);
        if (lns_perm_count == 0) continue;
        /* evaluate each permutation */
        static int pf[720];
        for (int p = 0; p < lns_perm_count; p++) {
            G h = *g;
            for (int i = 0; i < k; i++) free_edge(&h, lns_a[i], lns_b[i]);
            for (int i = 0; i < k; i++) add_edge(&h, lns_a[i], lns_b[lns_perms[p][i]]);
            pf[p] = far_cost(&h, NULL, NULL);
        }
        /* heat-bath draw */
        int fmin = pf[0]; for (int p = 1; p < lns_perm_count; p++) if (pf[p] < fmin) fmin = pf[p];
        double wsum = 0; static double wt[720];
        for (int p = 0; p < lns_perm_count; p++) { wt[p] = exp(-(pf[p] - fmin) / T); wsum += wt[p]; }
        double u = urand() * wsum; int pick = lns_perm_count - 1;
        for (int p = 0; p < lns_perm_count; p++) { u -= wt[p]; if (u <= 0) { pick = p; break; } }
        /* apply the picked permutation to g */
        for (int i = 0; i < k; i++) free_edge(g, lns_a[i], lns_b[i]);
        for (int i = 0; i < k; i++) add_edge(g, lns_a[i], lns_b[lns_perms[pick][i]]);
        f = pf[pick]; lns_done++; lns_sum += f;
        if (verbose >= 2 && it % 500 == 0) fprintf(stderr, "    it=%ld T=%.2f perms=%d cur=%d best=%d skip=%ld\n", it, T, lns_perm_count, f, bestf, lns_skip_ok);
        if (f < bestf) { bestf = f; *best = *g; if (verbose) fprintf(stderr, "  lns it=%ld T=%.2f best=%d\n", it, T, bestf); }
        far_cost(g, badc, &nbc);
    }
    if (verbose) fprintf(stderr, "lns: done=%ld skipped=%ld mean_cur=%.1f\n", lns_done, lns_skip_ok, lns_done ? lns_sum / lns_done : 0.0);
    return bestf;
}


/* exhaustive k-edge reconnection neighbourhood (k = 2 or 3) of a graph: min far over all valid reconnections */
static long kopt_hist_lo[64];
static void kopt_exhaustive(G *g, int k, int f0) {
    int n = g->n; int ea[MAXN * 3], eb[MAXN * 3], m = 0;
    for (int a = 0; a < n; a++) if (g->side[a] == 0) for (int t = 0; t < 3; t++) { ea[m] = a; eb[m] = g->adj[a][t]; m++; }
    long combos = 0, evals = 0, plateau = 0; int bestf = 1 << 30; int cnt_best = 0;
    int idx[3];
    for (idx[0] = 0; idx[0] < m; idx[0]++)
    for (idx[1] = (k >= 2 ? idx[0] + 1 : m); idx[1] < (k >= 2 ? m : m + 1); idx[1]++)
    for (idx[2] = (k >= 3 ? idx[1] + 1 : m); idx[2] < (k >= 3 ? m : m + 1); idx[2]++) {
        int a[3], b[3], ok = 1;
        for (int i = 0; i < k; i++) { a[i] = ea[idx[i]]; b[i] = eb[idx[i]]; }
        for (int i = 0; i < k && ok; i++) for (int j = i + 1; j < k; j++) if (a[i] == a[j] || b[i] == b[j]) ok = 0;
        if (!ok) continue;
        combos++;
        for (int i = 0; i < k; i++) for (int j = 0; j < k; j++) {
            if (i == j) { lns_valid[i][j] = 1; continue; }
            int e = 0; for (int t = 0; t < 3; t++) if (g->adj[a[i]][t] == b[j]) e = 1;
            lns_valid[i][j] = !e;
        }
        int cnt = 0, cur[8]; gen_perms(k, cur, 0, 0, &cnt);
        for (int p = 0; p < cnt; p++) {
            int id = 1; for (int i = 0; i < k; i++) if (lns_perms[p][i] != i) id = 0;
            if (id) continue;
            G h = *g;
            for (int i = 0; i < k; i++) free_edge(&h, a[i], b[i]);
            for (int i = 0; i < k; i++) add_edge(&h, a[i], b[lns_perms[p][i]]);
            int f = far_cost(&h, NULL, NULL); evals++;
            if (f < bestf) { bestf = f; cnt_best = 0; }
            if (f == bestf) cnt_best++;
            if (f <= f0) plateau++;
        }
    }
    printf("kopt k=%d: edge-sets=%ld reconnections=%ld min_far=%d (count %d) reconnections_with_far<=start(%d): %ld\n", k, combos, evals, bestf, cnt_best, f0, plateau);
}


/* ---- ball deletion with rematching ----
   Delete m vertices of A and m of B taken in BFS order around a centre (balanced, local), then rewire the loose
   slots: the new edges form a bijection between the A-side slots (x outside, adjacent to a deleted B-vertex) and the
   B-side slots (y outside, adjacent to a deleted A-vertex). The bijection is optimised by annealing over swaps. */
#define MAXE 64
static int bd_n, bd_map[MAXN];
static int bd_base[MAXN][3];   /* base adjacency among kept vertices, -1 = free slot */
static int bd_ax[MAXE], bd_by[MAXE], bd_E;
static int bd_eval(const int *sig, long *invalid_out) {
    G h; h.n = bd_n;
    for (int x = 0; x < bd_n; x++) { h.side[x] = 0; }
    memcpy(h.adj, bd_base, sizeof(int) * 3 * bd_n);
    for (int i = 0; i < bd_E; i++) {
        int x = bd_ax[i], y = bd_by[sig[i]];
        int placed = 0;
        for (int k = 0; k < 3 && !placed; k++) if (h.adj[x][k] == -1) { h.adj[x][k] = y; placed = 1; }
        if (!placed) { *invalid_out = 1; return 1000000; }
        placed = 0;
        for (int k = 0; k < 3 && !placed; k++) if (h.adj[y][k] == -1) { h.adj[y][k] = x; placed = 1; }
        if (!placed) { *invalid_out = 1; return 1000000; }
    }
    /* check simple: no duplicate neighbours */
    for (int x = 0; x < bd_n; x++) for (int a = 0; a < 3; a++) for (int b = a + 1; b < 3; b++) if (h.adj[x][a] == h.adj[x][b]) { *invalid_out = 1; return 1000000; }
    for (int x = 0; x < bd_n; x++) for (int k = 0; k < 3; k++) if (h.adj[x][k] < 0) { *invalid_out = 1; return 1000000; }
    /* sides: kept vertices ordered A first: use the mapping built by caller (side array in bd_side) */
    extern int bd_side[MAXN];
    memcpy(h.side, bd_side, sizeof(int) * bd_n);
    return far_cost(&h, NULL, NULL);
}
int bd_side[MAXN];
static int ball_reduce(const G *g, int centre, int m, long steps, double T0, double T1, int *best_sig, int *best_f_out, G *bestg, int verbose) {
    int n = g->n;
    /* BFS order from centre */
    static int order_[MAXN], dist_[MAXN]; for (int x = 0; x < n; x++) dist_[x] = -1;
    int h0 = 0, t0 = 0; order_[t0++] = centre; dist_[centre] = 0;
    while (h0 < t0) { int x = order_[h0++]; for (int k = 0; k < 3; k++) { int y = g->adj[x][k]; if (dist_[y] < 0) { dist_[y] = dist_[x] + 1; order_[t0++] = y; } } }
    int inS[MAXN] = {0}; int cA = 0, cB = 0;
    for (int j = 0; j < t0 && (cA < m || cB < m); j++) { int x = order_[j];
        if (g->side[x] == 0 && cA < m) { inS[x] = 1; cA++; }
        else if (g->side[x] == 1 && cB < m) { inS[x] = 1; cB++; } }
    if (cA < m || cB < m) return -1;
    /* kept vertices: A first then B */
    int map[MAXN]; int kept = 0;
    for (int s = 0; s < 2; s++) for (int x = 0; x < n; x++) if (!inS[x] && g->side[x] == s) { map[x] = kept; bd_side[kept] = s; kept++; }
    bd_n = kept;
    for (int x = 0; x < n; x++) if (!inS[x]) for (int k = 0; k < 3; k++) { int y = g->adj[x][k]; if (!inS[y]) bd_base[map[x]][k] = map[y]; else bd_base[map[x]][k] = -1; }
    /* slots */
    bd_E = 0;
    for (int s = 0; s < n; s++) if (inS[s] && g->side[s] == 1) for (int k = 0; k < 3; k++) { int x = g->adj[s][k]; if (!inS[x]) { bd_ax[bd_E] = map[x]; bd_E++; } }
    int Ea = bd_E; int Eb = 0; static int bdb_y[MAXE];
    for (int s = 0; s < n; s++) if (inS[s] && g->side[s] == 0) for (int k = 0; k < 3; k++) { int y = g->adj[s][k]; if (!inS[y]) { bdb_y[Eb++] = map[y]; } }
    if (Ea != Eb || Ea > MAXE) return -2;
    for (int i = 0; i < Ea; i++) bd_by[i] = bdb_y[i];
    bd_E = Ea;
    /* free slots must match: bd_base has -1 for every removed neighbour; new edges fill them */
    /* initial bijection: identity; invalid starts are penalised */
    int sig[MAXE]; for (int i = 0; i < Ea; i++) sig[i] = i;
    long inv = 0; int f = bd_eval(sig, &inv); int bestf = f; memcpy(best_sig, sig, sizeof(int) * Ea);
    for (long s = 0; s < steps && bestf > 0; s++) {
        double T = T0 * pow(T1 / T0, (double)s / (double)steps);
        int i = irand(Ea), j = irand(Ea); if (i == j) continue;
        int t = sig[i]; sig[i] = sig[j]; sig[j] = t;
        long inv2 = 0; int nf = bd_eval(sig, &inv2);
        if (nf <= f || urand() < exp(-(nf - f) / T)) { f = nf; if (f < bestf) { bestf = f; memcpy(best_sig, sig, sizeof(int) * Ea); } }
        else { t = sig[i]; sig[i] = sig[j]; sig[j] = t; }
    }
    /* materialise the best graph */
    if (bestg) {
        G h; h.n = bd_n; memcpy(h.adj, bd_base, sizeof(int) * 3 * bd_n); memcpy(h.side, bd_side, sizeof(int) * bd_n);
        for (int i = 0; i < Ea; i++) { int x = bd_ax[i], y = bd_by[best_sig[i]];
            for (int k = 0; k < 3; k++) if (h.adj[x][k] == -1) { h.adj[x][k] = y; break; }
            for (int k = 0; k < 3; k++) if (h.adj[y][k] == -1) { h.adj[y][k] = x; break; } }
        *bestg = h;
    }
    *best_f_out = bestf;
    if (verbose) fprintf(stderr, "centre %d: E=%d best %d\n", centre, Ea, bestf);
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 2) { fprintf(stderr, "usage: see header\n"); return 2; }
    if (!strcmp(argv[1], "far")) {  /* shrink far IN : print far */
        G g; read_graph(argv[2], &g);
        static int bl[MAXN]; int nb; int f = far_cost(&g, bl, &nb);
        printf("n=%d far=%d badvertices=%d\n", g.n, f, nb); return 0;
    }
    if (!strcmp(argv[1], "stats")) {  /* shrink stats IN N : random switch statistics */
        G g; read_graph(argv[2], &g); int N = atoi(argv[3]);
        static int bl[MAXN]; int nb; int f = far_cost(&g, bl, &nb);
        int na = nA(&g); int *Al = malloc(sizeof(int) * na); int c = 0;
        for (int x = 0; x < g.n; x++) if (g.side[x] == 0) Al[c++] = x;
        int ok = 0; long hist[1024] = {0};
        for (int it = 0; it < N; it++) {
            int a = Al[irand(na)], b = g.adj[a][irand(3)], cc = Al[irand(na)], d = g.adj[cc][irand(3)];
            if (!try_switch(&g, a, b, cc, d)) continue;
            ok++; int nf = far_cost(&g, bl, &nb); hist[nf < 1024 ? nf : 1023]++;
            undo_switch(&g, a, b, cc, d);
        }
        printf("f0=%d tried=%d ok=%d\n", f, N, ok);
        for (int i = 0; i < 1024; i++) if (hist[i] && i < 200) printf("far %d: %ld\n", i, hist[i]);
        return 0;
    }
    if (!strcmp(argv[1], "tabu")) {  /* shrink tabu IN iters K TEN seed OUT */
        G g, best; read_graph(argv[2], &g);
        long iters = atol(argv[3]); int K = atoi(argv[4]), TEN = atoi(argv[5]);
        rs = strtoull(argv[6], 0, 10) * 2654435761ULL + 777;
        int nopt = 0;
        int bf = tabu_run(&g, iters, K, TEN, &nopt, &best, getenv("VERB") ? atoi(getenv("VERB")) : 0);
        printf("n=%d tabu_best_far=%d steps=%d\n", best.n, bf, nopt);
        write_graph(&best, argv[7]);
        return 0;
    }
    if (!strcmp(argv[1], "compound")) {  /* shrink compound IN samples msize rounds seed OUT : greedy descent by best sampled compound move */
        G g; read_graph(argv[2], &g);
        long samples = atol(argv[3]); int msz = atoi(argv[4]); long rounds = atol(argv[5]);
        rs = strtoull(argv[6], 0, 10) * 2654435761ULL + 31337;
        static int bl[MAXN]; int nb; int f = far_cost(&g, bl, &nb);
        int n = g.n; int *Al = malloc(sizeof(int) * n); int na = 0;
        for (int x = 0; x < n; x++) if (g.side[x] == 0) Al[na++] = x;
        printf("start n=%d far=%d\n", n, f); fflush(stdout);
        int bestf = f; G best = g;
        for (long r = 0; r < rounds && f > 0; r++) {
            far_cost(&g, bl, &nb);
            int bsf = 1 << 30; G bg; int improved = 0;
            long hitsame = 0;
            for (long s = 0; s < samples; s++) {
                G h = g;
                int ea[8], eb[8], ec[8], ed[8], ns = 0;
                for (int j = 0; j < msz; j++) {
                    int a, b, cc, d;
                    if (rnd() % 10 < 8) { int x = bl[irand(nb)]; int p = x, w = irand(3); for (int t = 0; t < w; t++) p = h.adj[p][irand(3)];
                        int q = h.adj[p][irand(3)]; if (h.side[p] == 0) { a = p; b = q; } else { a = q; b = p; } }
                    else { a = Al[irand(na)]; b = h.adj[a][irand(3)]; }
                    cc = Al[irand(na)]; d = h.adj[cc][irand(3)];
                    if (try_switch(&h, a, b, cc, d)) { ea[ns] = a; eb[ns] = b; ec[ns] = cc; ed[ns] = d; ns++; }
                }
                if (ns == 0) continue;
                int nf = far_cost(&h, NULL, NULL);
                if (nf < bsf) { bsf = nf; bg = h; }
                if (nf == f) hitsame++;
            }
            if (bsf < f) { g = bg; f = bsf; improved = 1; }
            if (f < bestf) { bestf = f; best = g; }
            printf("round %ld best_sampled=%d cur=%d (ties %ld)\n", r, bsf, f, hitsame); fflush(stdout);
            if (!improved) { /* perturb: sideways random accept not implemented; stop */ break; }
        }
        printf("compound best far=%d n=%d\n", bestf, best.n);
        write_graph(&best, argv[7]);
        return 0;
    }
    if (!strcmp(argv[1], "ils")) {  /* shrink ils IN rounds kick tabu_iters K TEN seed OUTPREFIX [accept_slack] */
        G g, cur, gb; read_graph(argv[2], &g);
        long rounds = atol(argv[3]); int kick = atoi(argv[4]); long titers = atol(argv[5]);
        int K = atoi(argv[6]), TEN = atoi(argv[7]);
        rs = strtoull(argv[8], 0, 10) * 2654435761ULL + 4242;
        const char *pref = argv[9]; int slack = argc > 10 ? atoi(argv[10]) : 0;
        static int bl[MAXN]; int nb;
        cur = g; int f = far_cost(&cur, bl, &nb);
        G gbest = cur; int gbf = f;
        printf("ILS start n=%d far=%d\n", cur.n, f); fflush(stdout);
        for (long r = 1; r <= rounds && gbf > 0; r++) {
            G cand = cur;
            /* kick: random switches at bad vertices, without repair */
            int done = 0, tries = 0;
            while (done < kick && tries < 1000) {
                tries++;
                int x = bl[irand(nb)];
                int p = x; int w = irand(3); for (int t = 0; t < w; t++) p = cand.adj[p][irand(3)];
                int q = cand.adj[p][irand(3)];
                int a, b; if (cand.side[p] == 0) { a = p; b = q; } else { a = q; b = p; }
                int cc = 0, d = 0; { int na = nA(&cand); (void)na; }
                int pa; do { pa = irand(cand.n); } while (cand.side[pa] != 0); cc = pa; d = cand.adj[cc][irand(3)];
                if (try_switch(&cand, a, b, cc, d)) done++;
            }
            int nopt = 0; G bt; int bf = tabu_run(&cand, titers, K, TEN, &nopt, &bt, 0);
            if (bf <= f + slack) { cur = bt; f = bf; }
            if (bf < gbf) { gbf = bf; gbest = bt; char fn[300]; snprintf(fn, sizeof fn, "%s_far%d.edges", pref, gbf); write_graph(&gbest, fn); }
            if (r % 10 == 0 || bf < 10) { printf("round %ld cand=%d cur=%d best=%d\n", r, bf, f, gbf); fflush(stdout); }
            far_cost(&cur, bl, &nb);
        }
        printf("ILS best far=%d\n", gbf);
        return 0;
    }
    if (!strcmp(argv[1], "stream")) {  /* shrink stream : reads blocks "n m" + m edge lines from stdin, prints far per block */
        int n, m; int cnt = 0;
        while (scanf("%d %d", &n, &m) == 2) {
            G g; memset(&g, 0, sizeof g); g.n = n; int deg[MAXN] = {0}; int raw[MAXN][3]; int ok = 1;
            for (int i = 0; i < m; i++) { int a, b; if (scanf("%d %d", &a, &b) != 2) return 3; if (deg[a] >= 3 || deg[b] >= 3) { ok = 0; continue; } raw[a][deg[a]++] = b; raw[b][deg[b]++] = a; }
            /* sides: taken from first block header via bipartite 2-colouring */
            int side[MAXN]; for (int i = 0; i < n; i++) side[i] = -1; int q[MAXN], h = 0, t = 0; side[0] = 0; q[t++] = 0;
            while (h < t) { int x = q[h++]; for (int k = 0; k < deg[x]; k++) { int y = raw[x][k]; if (side[y] < 0) { side[y] = 1 - side[x]; q[t++] = y; } } }
            int cub = 1; for (int i = 0; i < n; i++) if (deg[i] != 3) cub = 0;
            int simple = 1; for (int i = 0; i < n && simple; i++) if (raw[i][0] == raw[i][1] || raw[i][0] == raw[i][2] || raw[i][1] == raw[i][2]) simple = 0;
            if (!ok || !cub || !simple) { printf("-1 invalid\n"); fflush(stdout); continue; }
            int disc = 0; for (int i = 0; i < n; i++) if (side[i] < 0) disc = 1;
            if (disc) { printf("100000\n"); fflush(stdout); ++cnt; continue; }
            int removed[MAXN] = {0}; normalize(n, side, raw, removed, &g);
            static int bl[MAXN]; int nb; int f = far_cost(&g, bl, &nb);
            printf("%d\n", f); fflush(stdout); ++cnt;
        }
        fflush(stdout);
        return 0;
    }
    if (!strcmp(argv[1], "lns")) {  /* shrink lns IN iters k T0 T1 R seed OUT */
        G g, best; read_graph(argv[2], &g);
        long iters = atol(argv[3]); int k = atoi(argv[4]); double T0 = atof(argv[5]), T1 = atof(argv[6]); int R = atoi(argv[7]);
        rs = strtoull(argv[8], 0, 10) * 2654435761ULL + 99991;
        int bf = lns_run(&g, iters, k, T0, T1, R, &best, getenv("VERB") ? atoi(getenv("VERB")) : 0);
        printf("n=%d lns_best_far=%d\n", best.n, bf);
        write_graph(&best, argv[9]);
        return 0;
    }
    if (!strcmp(argv[1], "kopt")) {  /* shrink kopt IN k : exhaustive k-edge reconnection neighbourhood */
        G g; read_graph(argv[2], &g); int k = atoi(argv[3]);
        static int bl[MAXN]; int nb; int f0 = far_cost(&g, bl, &nb);
        kopt_exhaustive(&g, k, f0);
        return 0;
    }
    if (!strcmp(argv[1], "ballred")) {  /* shrink ballred IN m steps T0 T1 seed TAG : all centres */
        G g; read_graph(argv[2], &g); int m = atoi(argv[3]); long steps = atol(argv[4]);
        double T0 = atof(argv[5]), T1 = atof(argv[6]); rs = strtoull(argv[7], 0, 10) * 2654435761ULL + 5150;
        const char *tag = argv[8]; int gbf = 1 << 30; int hist[64] = {0};
        for (int c = 0; c < g.n; c++) {
            int sigb[MAXE]; int bf = 0; G h;
            int r = ball_reduce(&g, c, m, steps, T0, T1, sigb, &bf, &h, 0);
            if (r < 0) continue;
            if (bf < 64) hist[bf]++;
            if (bf < gbf) { gbf = bf; char fn[300]; snprintf(fn, sizeof fn, "out/%s_n%d_far%d.edges", tag, h.n, bf); write_graph(&h, fn); printf("centre %d n=%d best far %d\n", c, h.n, bf); fflush(stdout); }
        }
        printf("ballred m=%d best far over centres = %d\n", m, gbf);
        return 0;
    }
    if (!strcmp(argv[1], "sa")) {  /* shrink sa IN steps T0 T1 seed OUT [focus] */
        G g, best; read_graph(argv[2], &g);
        long steps = atol(argv[3]); double T0 = atof(argv[4]), T1 = atof(argv[5]);
        rs = strtoull(argv[6], 0, 10) * 2654435761ULL + 12345; int focus = argc > 8 ? atoi(argv[8]) : 50;
        int bf = sa_run(&g, steps, T0, T1, focus, &best, getenv("VERB") ? atoi(getenv("VERB")) : 0);
        printf("n=%d sa_best_far=%d\n", best.n, bf);
        write_graph(&best, argv[7]);
        return 0;
    }
    if (!strcmp(argv[1], "beam")) {
        /* shrink beam IN target width sa_steps T0 T1 seed TAG [nonadj] [focus] */
        G start; read_graph(argv[2], &start);
        int target = atoi(argv[3]), width = atoi(argv[4]); long sast = atol(argv[5]);
        double T0 = atof(argv[6]), T1 = atof(argv[7]);
        rs = strtoull(argv[8], 0, 10) * 2654435761ULL + 999;
        const char *tag = argv[9];
        int nonadj = argc > 10 ? atoi(argv[10]) : 0;
        int focus = argc > 11 ? atoi(argv[11]) : 50;
        static int bl[MAXN]; int nb;
        if (getenv("PERTURB")) {   /* random restart: apply PERTURB random 2-switches first */
            int kp = atoi(getenv("PERTURB")); int done2 = 0; int Al2[MAXN], na2 = 0;
            for (int x = 0; x < start.n; x++) if (start.side[x] == 0) Al2[na2++] = x;
            while (done2 < kp) { int a = Al2[irand(na2)], b = start.adj[a][irand(3)], cc = Al2[irand(na2)], d = start.adj[cc][irand(3)];
                if (try_switch(&start, a, b, cc, d)) done2++; }
        }
        G *beam = malloc(sizeof(G) * width); int nbeam = 1; beam[0] = start;
        int bestfar_at_n = 0;
        int n = start.n;
        {   /* initial SA at start size */
            G b; int f0 = far_cost(&start, bl, &nb);
            int f = sa_run(&beam[0], sast, T0, T1, focus, &b, 0);
            beam[0] = b;
            printf("START n=%d far_in=%d after_sa=%d\n", n, f0, f); fflush(stdout);
            (void)bestfar_at_n;
        }
        while (n > target) {
            int nt = n - 2;
            /* enumerate all reductions of all beam graphs; keep the best 'cap' by far */
            int cap = width * 4;
            int *cf = malloc(sizeof(int) * cap), *cg = malloc(sizeof(int) * cap), *ca = malloc(sizeof(int) * cap), *cb = malloc(sizeof(int) * cap), *cp = malloc(sizeof(int) * cap);
            int ccount = 0; long total = 0;
            for (int gi = 0; gi < nbeam; gi++) {
                G *g = &beam[gi];
                int na_ = nA(g);
                for (int ai = 0; ai < g->n; ai++) if (g->side[ai] == 0) {
                    for (int kk = 0; kk < 3; kk++) {
                        int b_ = g->adj[ai][kk];
                        /* adjacent reduction, 2 matchings */
                        for (int pi = 0; pi < 2; pi++) {
                            G r; if (!reduce(g, ai, b_, PERM2[pi], 2, &r)) continue;
                            total++;
                            int f = far_cost(&r, NULL, NULL);
                            /* keep top cap (simple insertion into unsorted with replace-worst) */
                            if (ccount < cap) { cf[ccount] = f; cg[ccount] = gi; ca[ccount] = ai; cb[ccount] = b_; cp[ccount] = pi; ccount++; }
                            else { int w = 0; for (int t = 1; t < cap; t++) if (cf[t] > cf[w]) w = t;
                                   if (f < cf[w]) { cf[w] = f; cg[w] = gi; ca[w] = ai; cb[w] = b_; cp[w] = pi; } }
                        }
                    }
                }
                if (nonadj) {
                    for (int ai = 0; ai < g->n; ai++) if (g->side[ai] == 0) for (int bi = 0; bi < g->n; bi++) if (g->side[bi] == 1 && !has_edge(g, ai, bi)) {
                        for (int pi = 0; pi < 6; pi++) {
                            G r; if (!reduce(g, ai, bi, PERM3[pi], 3, &r)) continue;
                            total++;
                            int f = far_cost(&r, NULL, NULL);
                            if (ccount < cap) { cf[ccount] = f; cg[ccount] = gi; ca[ccount] = ai; cb[ccount] = bi; cp[ccount] = 100 + pi; ccount++; }
                            else { int w = 0; for (int t = 1; t < cap; t++) if (cf[t] > cf[w]) w = t;
                                   if (f < cf[w]) { cf[w] = f; cg[w] = gi; ca[w] = ai; cb[w] = bi; cp[w] = 100 + pi; } }
                        }
                    }
                }
                (void)na_;
            }
            /* sort candidate indices by far */
            for (int i = 1; i < ccount; i++) for (int j = i; j > 0 && cf[j] < cf[j - 1]; j--) {
                int t;
#define SW(arr) t = arr[j]; arr[j] = arr[j-1]; arr[j-1] = t;
                SW(cf) SW(cg) SW(ca) SW(cb) SW(cp)
#undef SW
            }
            G *nbeam_g = malloc(sizeof(G) * width); int nn = 0;
            uint64_t *hs = malloc(sizeof(uint64_t) * width);
            int reduced_best = 1 << 30;
            for (int i = 0; i < ccount && nn < width; i++) {
                G r;
                int perm_k = cp[i] >= 100 ? 3 : 2; const int *perm = cp[i] >= 100 ? PERM3[cp[i] - 100] : PERM2[cp[i]];
                if (!reduce(&beam[cg[i]], ca[i], cb[i], perm, perm_k, &r)) continue;
                uint64_t h = ghash(&r); int dup = 0;
                for (int t = 0; t < nn; t++) if (hs[t] == h) { dup = 1; break; }
                if (dup) continue;
                hs[nn] = h; nbeam_g[nn] = r; nn++;
                if (cf[i] < reduced_best) reduced_best = cf[i];
            }
            free(hs);
            printf("LEVEL n=%d candidates=%ld (kept %d) best_reduced_far=%d\n", nt, total, nn, reduced_best); fflush(stdout);
            free(cf); free(cg); free(ca); free(cb); free(cp);
            free(beam); beam = nbeam_g; nbeam = nn; n = nt;
            /* SA on each beam member */
            int best_f = 1 << 30; G bestg = beam[0];
            for (int gi = 0; gi < nbeam; gi++) {
                G b; int f0 = far_cost(&beam[gi], NULL, NULL);
                int f = sa_run(&beam[gi], sast, T0, T1, focus, &b, 0);
                beam[gi] = b;
                if (f < best_f) { best_f = f; bestg = b; }
                if (gi == 0 || f < best_f + 0) {}
                (void)f0;
            }
            printf("SA n=%d beam=%d best_far=%d\n", n, nbeam, best_f); fflush(stdout);
            char fn[256]; snprintf(fn, sizeof fn, "out/%s_n%d_far%d.edges", tag, n, best_f);
            write_graph(&bestg, fn);
            if (best_f == 0) { printf("FOUND far=0 at n=%d\n", n); }
        }
        return 0;
    }
    fprintf(stderr, "unknown mode\n");
    return 2;
}
