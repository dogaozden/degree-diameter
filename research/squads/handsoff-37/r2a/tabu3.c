/* c1 tabu search over bipartite 2-switches, cost = far. Candidate edges: all edges (MODE 0) or, MODE r > 0, edges with
   an endpoint within distance r of a vertex that still has unreached same-side vertices (recomputed every step).
   Each step takes the best non-tabu move (aspiration if it beats the best). Removed edges are tabu to re-add for TT steps.
   Usage: tabu3 IN STEPS TT SEED OUTPREFIX MODE TLIM   (progress lines on stderr, one per 25 steps) */
#include "g37.h"
#include <math.h>
#include <time.h>

static int side[MAXN];
static int ea[MAXN * 2], eb[MAXN * 2]; static int m;
static long tabu_until[MAXN][MAXN];

static void bip(const G *g) {
    for (int i = 0; i < g->n; i++) side[i] = -1;
    int q[MAXN], h = 0, t = 0; side[0] = 0; q[t++] = 0;
    while (h < t) { int x = q[h++]; for (int i = 0; i < g->deg[x]; i++) { int y = g->nb[x][i]; if (side[y] < 0) { side[y] = 1 - side[x]; q[t++] = y; } } }
}

int main(int argc, char **argv) {
    if (argc < 8) { fprintf(stderr, "usage: tabu3 IN STEPS TT SEED OUTPREFIX MODE TLIM\n"); return 2; }
    G g; if (g_load(&g, argv[1]) < 0) return 2;
    long steps = atol(argv[2]); int TT = atoi(argv[3]); rng_seed(strtoull(argv[4], 0, 10));
    const char *pre = argv[5]; int MODE = atoi(argv[6]); double tlim = atof(argv[7]);
    int n = g.n; bip(&g);
    m = 0;
    for (int x = 0; x < n; x++) for (int i = 0; i < g.deg[x]; i++) { int y = g.nb[x][i]; if (x < y) { if (side[x] == 0) { ea[m] = x; eb[m] = y; } else { ea[m] = y; eb[m] = x; } m++; } }
    int ex[MAXN]; long cur = far_detail(&g, ex), best = cur;
    char fn[512]; snprintf(fn, sizeof fn, "%s_best.edges", pre); g_write(&g, fn);
    static int cand[MAXN * 2]; static int inR[MAXN];
    clock_t t0 = clock();
    long s;
    for (s = 1; s <= steps; s++) {
        int nc = 0;
        if (MODE == 0) { for (int i = 0; i < m; i++) cand[nc++] = i; }
        else {
            int dist[MAXN], q[MAXN], h = 0, t = 0;
            for (int i = 0; i < n; i++) { dist[i] = -1; }
            far_detail(&g, ex);
            for (int i = 0; i < n; i++) if (ex[i] > 0) { dist[i] = 0; q[t++] = i; }
            while (h < t) { int x = q[h++]; if (dist[x] >= MODE) continue; for (int i = 0; i < g.deg[x]; i++) { int y = g.nb[x][i]; if (dist[y] < 0) { dist[y] = dist[x] + 1; q[t++] = y; } } }
            for (int i = 0; i < m; i++) if (dist[ea[i]] >= 0 || dist[eb[i]] >= 0) cand[nc++] = i;
        }
        long bf = 1L << 40; int bi = -1, bj = -1, nties = 0;
        for (int ci = 0; ci < nc; ci++) for (int cj = ci + 1; cj < nc; cj++) {
            int i = cand[ci], j = cand[cj];
            int a = ea[i], c = eb[i], b = ea[j], d = eb[j];
            if (a == b || c == d) continue;
            if (g_has(&g, a, d) || g_has(&g, b, c)) continue;
            int tabu = (tabu_until[a][d] > s) || (tabu_until[b][c] > s);
            g_del(&g, a, c); g_del(&g, b, d); g_add(&g, a, d); g_add(&g, b, c);
            long f = far_cost(&g);
            g_del(&g, a, d); g_del(&g, b, c); g_add(&g, a, c); g_add(&g, b, d);
            if (tabu && f >= best) continue;
            if (f < bf) { bf = f; bi = i; bj = j; nties = 1; }
            else if (f == bf) { nties++; if (rng_int(nties) == 0) { bi = i; bj = j; } }
        }
        if (bi < 0) { fprintf(stderr, "no admissible move at step %ld\n", s); break; }
        int a = ea[bi], c = eb[bi], b = ea[bj], d = eb[bj];
        g_del(&g, a, c); g_del(&g, b, d); g_add(&g, a, d); g_add(&g, b, c);
        ea[bi] = a; eb[bi] = d; ea[bj] = b; eb[bj] = c;
        tabu_until[a][c] = tabu_until[c][a] = s + TT + rng_int(3);
        tabu_until[b][d] = tabu_until[d][b] = s + TT + rng_int(3);
        cur = bf;
        if (cur < best) { best = cur; g_write(&g, fn); fprintf(stderr, "step %ld best far=%ld (cand %d)\n", s, best, nc); if (best == 0) break; }
        if (s % 25 == 0) fprintf(stderr, "step %ld cur=%ld best=%ld cand=%d (%.0fs)\n", s, cur, best, nc, (double)(clock() - t0) / CLOCKS_PER_SEC);
        if ((double)(clock() - t0) / CLOCKS_PER_SEC > tlim) break;
    }
    printf("%s: tabu3 mode=%d steps=%ld best=%ld cur=%ld\n", pre, MODE, s - 1, best, cur);
    return 0;
}
