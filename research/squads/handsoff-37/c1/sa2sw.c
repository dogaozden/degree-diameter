/* c1 simulated annealing over bipartite 2-switches, cost = far (unordered pairs at distance > 7).
   A 2-switch takes edges (a,c),(b,d) with a,b in A and c,d in B to (a,d),(b,c); sides are found by BFS.
   Usage: sa2sw IN ITERS T0 T1 SEED OUTPREFIX [RESTRICT_RADIUS]
     RESTRICT_RADIUS r > 0: both edges of a move must lie inside the ball of radius r around vertices n-2, n-1
     (the inserted pair). r = 0: unrestricted. Writes OUTPREFIX_best.edges when the best improves. */
#include "g37.h"
#include <math.h>

static int side[MAXN];
static int ea[MAXN * 2], eb[MAXN * 2]; static int m;

static void bip(const G *g) {
    for (int i = 0; i < g->n; i++) side[i] = -1;
    int q[MAXN], h = 0, t = 0; side[0] = 0; q[t++] = 0;
    while (h < t) { int x = q[h++]; for (int i = 0; i < g->deg[x]; i++) { int y = g->nb[x][i]; if (side[y] < 0) { side[y] = 1 - side[x]; q[t++] = y; } } }
}

int main(int argc, char **argv) {
    if (argc < 7) { fprintf(stderr, "usage: sa2sw IN ITERS T0 T1 SEED OUTPREFIX [R]\n"); return 2; }
    G g; if (g_load(&g, argv[1]) < 0) return 2;
    long iters = atol(argv[2]); double T0 = atof(argv[3]), T1 = atof(argv[4]);
    rng_seed(strtoull(argv[5], 0, 10)); const char *pre = argv[6];
    int R = argc > 7 ? atoi(argv[7]) : 0;
    int n = g.n; bip(&g);
    /* edge list oriented A->B */
    m = 0;
    for (int x = 0; x < n; x++) for (int i = 0; i < g.deg[x]; i++) { int y = g.nb[x][i]; if (x < y) { if (side[x] == 0) { ea[m] = x; eb[m] = y; } else { ea[m] = y; eb[m] = x; } m++; } }
    int ex[MAXN]; long cur = far_detail(&g, ex), best = cur;
    /* restriction set */
    static int inR[MAXN]; int nR = n;
    if (R > 0) {
        int dist[MAXN]; for (int i = 0; i < n; i++) { inR[i] = 0; dist[i] = -1; }
        int q[MAXN], h = 0, t = 0;
        for (int s = n - 2; s < n; s++) { dist[s] = 0; q[t++] = s; }
        while (h < t) { int x = q[h++]; if (dist[x] >= R) continue; for (int i = 0; i < g.deg[x]; i++) { int y = g.nb[x][i]; if (dist[y] < 0) { dist[y] = dist[x] + 1; q[t++] = y; } } }
        nR = 0; for (int i = 0; i < n; i++) if (dist[i] >= 0) { inR[i] = 1; nR++; }
        fprintf(stderr, "restricted to ball radius %d: %d vertices\n", R, nR);
    } else for (int i = 0; i < n; i++) inR[i] = 1;
    /* candidate edge indices restricted */
    static int cand[MAXN * 2]; int nc = 0;
    for (int i = 0; i < m; i++) if (inR[ea[i]] && inR[eb[i]]) cand[nc++] = i;
    fprintf(stderr, "start far=%ld edges=%d candidates=%d\n", cur, m, nc);
    static int bestg_ea[MAXN*2], bestg_eb[MAXN*2];
    char fn[512]; snprintf(fn, sizeof fn, "%s_best.edges", pre);
    long acc = 0, tried = 0;
    if (nc < 2) { printf("no candidates\n"); return 0; }
    for (long it = 0; it < iters; it++) {
        double T = T0 * pow(T1 / T0, (double)it / (double)iters);
        int i = cand[rng_int(nc)], j = cand[rng_int(nc)];
        if (i == j) continue;
        int a = ea[i], c = eb[i], b = ea[j], d = eb[j];
        if (a == b || c == d) continue;
        if (g_has(&g, a, d) || g_has(&g, b, c)) continue;
        g_del(&g, a, c); g_del(&g, b, d); g_add(&g, a, d); g_add(&g, b, c);
        long f = far_cost(&g); tried++;
        int ok = (f <= cur) || (rng_unif() < exp(-(double)(f - cur) / T));
        if (ok) {
            ea[i] = a; eb[i] = d; ea[j] = b; eb[j] = c; cur = f; acc++;
            if (cur < best) { best = cur; g_write(&g, fn); fprintf(stderr, "it %ld T=%.3f best far=%ld\n", it, T, best); if (best == 0) break; }
        } else {
            g_del(&g, a, d); g_del(&g, b, c); g_add(&g, a, c); g_add(&g, b, d);
        }
        if ((it & ((1 << 20) - 1)) == 0 && it) fprintf(stderr, "  it %ld T=%.3f cur=%ld best=%ld acc=%ld\n", it, T, cur, best, acc);
    }
    printf("%s: start-best done best=%ld final=%ld tried=%ld accepted=%ld\n", pre, best, cur, tried, acc);
    return 0;
}
