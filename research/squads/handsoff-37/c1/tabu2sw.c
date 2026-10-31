/* c1 tabu search over bipartite 2-switches, cost = far (unordered pairs at distance > 7).
   Each step scores every admissible 2-switch among candidate edges, takes the best non-tabu move (aspiration if it
   beats the best ever), and forbids re-creating the two removed edges for TT steps.
   Usage: tabu2sw IN STEPS TT SEED OUTPREFIX [R] [TIME_LIMIT_SEC]
     R > 0: candidate edges must lie inside the radius-R ball around the last two vertices (the inserted pair). */
#include "g37.h"
#include <math.h>

static int side[MAXN];
static int ea[MAXN * 2], eb[MAXN * 2]; static int m;
static int tabu_until[MAXN][MAXN];

static void bip(const G *g) {
    for (int i = 0; i < g->n; i++) side[i] = -1;
    int q[MAXN], h = 0, t = 0; side[0] = 0; q[t++] = 0;
    while (h < t) { int x = q[h++]; for (int i = 0; i < g->deg[x]; i++) { int y = g->nb[x][i]; if (side[y] < 0) { side[y] = 1 - side[x]; q[t++] = y; } } }
}

int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: tabu2sw IN STEPS TT SEED OUTPREFIX [R] [TLIM]\n"); return 2; }
    G g; if (g_load(&g, argv[1]) < 0) return 2;
    long steps = atol(argv[2]); int TT = atoi(argv[3]); rng_seed(strtoull(argv[4], 0, 10)); const char *pre = argv[5];
    int R = argc > 6 ? atoi(argv[6]) : 0; double tlim = argc > 7 ? atof(argv[7]) : 1e9;
    int n = g.n; bip(&g);
    m = 0;
    for (int x = 0; x < n; x++) for (int i = 0; i < g.deg[x]; i++) { int y = g.nb[x][i]; if (x < y) { if (side[x] == 0) { ea[m] = x; eb[m] = y; } else { ea[m] = y; eb[m] = x; } m++; } }
    int ex[MAXN]; long cur = far_detail(&g, ex), best = cur;
    static int inR[MAXN]; int nR = n;
    if (R > 0) {
        int dist[MAXN]; for (int i = 0; i < n; i++) dist[i] = -1;
        int q[MAXN], h = 0, t = 0;
        for (int s = n - 2; s < n; s++) { dist[s] = 0; q[t++] = s; }
        while (h < t) { int x = q[h++]; if (dist[x] >= R) continue; for (int i = 0; i < g.deg[x]; i++) { int y = g.nb[x][i]; if (dist[y] < 0) { dist[y] = dist[x] + 1; q[t++] = y; } } }
        nR = 0; for (int i = 0; i < n; i++) { inR[i] = dist[i] >= 0; nR += inR[i]; }
    } else for (int i = 0; i < n; i++) inR[i] = 1;
    static int cand[MAXN * 2]; int nc = 0;
    for (int i = 0; i < m; i++) if (inR[ea[i]] && inR[eb[i]]) cand[nc++] = i;
    fprintf(stderr, "start far=%ld edges=%d candidates=%d (ball %d)\n", cur, m, nc, nR);
    char fn[512]; snprintf(fn, sizeof fn, "%s_best.edges", pre);
    g_write(&g, fn);
    long bestf = cur;
    clock_t t0 = clock();
    long last_imp = 0;
    for (long s = 1; s <= steps; s++) {
        long bf = 1L << 40; int bi = -1, bj = -1; int nties = 0;
        for (int ci = 0; ci < nc; ci++) for (int cj = ci + 1; cj < nc; cj++) {
            int i = cand[ci], j = cand[cj];
            int a = ea[i], c = eb[i], b = ea[j], d = eb[j];
            if (a == b || c == d) continue;
            if (g_has(&g, a, d) || g_has(&g, b, c)) continue;
            int tabu = (tabu_until[a][d] > s) || (tabu_until[b][c] > s);
            g_del(&g, a, c); g_del(&g, b, d); g_add(&g, a, d); g_add(&g, b, c);
            long f = far_cost(&g);
            g_del(&g, a, d); g_del(&g, b, c); g_add(&g, a, c); g_add(&g, b, d);
            if (tabu && f >= bestf) continue;
            if (f < bf) { bf = f; bi = i; bj = j; nties = 1; }
            else if (f == bf) { nties++; if (rng_int(nties) == 0) { bi = i; bj = j; } }
        }
        if (bi < 0) { fprintf(stderr, "no move\n"); break; }
        int a = ea[bi], c = eb[bi], b = ea[bj], d = eb[bj];
        g_del(&g, a, c); g_del(&g, b, d); g_add(&g, a, d); g_add(&g, b, c);
        ea[bi] = a; eb[bi] = d; ea[bj] = b; eb[bj] = c;
        tabu_until[a][c] = tabu_until[c][a] = (int)s + TT + rng_int(3);
        tabu_until[b][d] = tabu_until[d][b] = (int)s + TT + rng_int(3);
        cur = bf;
        if (cur < bestf) { bestf = cur; last_imp = s; g_write(&g, fn); fprintf(stderr, "step %ld best far=%ld\n", s, bestf); if (bestf == 0) break; }
        if (s % 50 == 0) fprintf(stderr, "step %ld cur=%ld best=%ld (%.0fs)\n", s, cur, bestf, (double)(clock() - t0) / CLOCKS_PER_SEC);
        if ((double)(clock() - t0) / CLOCKS_PER_SEC > tlim) break;
        (void)last_imp;
    }
    printf("%s: tabu done best=%ld cur=%ld\n", pre, bestf, cur);
    return 0;
}
