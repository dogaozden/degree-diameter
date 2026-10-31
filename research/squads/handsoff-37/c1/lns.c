/* c1 large-neighbourhood search for bipartite cubic graphs with a pair of vertices of the "insertion" type.
   Move: pick an edge a~b (a in A, b in B). Remove a and b, reconnect the outer neighbours x1,x2 (of b, in A) and
   y1,y2 (of a, in B) as x1-y1, x2-y2 or x1-y2, x2-y1 (graph of n-2 vertices, relabelled to 0..n-3).
   Then re-insert a pair: all k=2 insertions (delete edges e,f; add a'~ y's, b'~ x's, a'~b') on the reduced graph.
   Keep the best of all re-insertions of the move; first-improvement descent over moves in random order; when a full
   pass finds nothing, perturb with a random move (accepted regardless) and continue (iterated local search).
   Usage: lns IN PASSES SEED OUTPREFIX TLIM */
#include "g37.h"
#include <math.h>
#include <time.h>

static int side[MAXN];
static void bip(const G *g) {
    for (int i = 0; i < g->n; i++) side[i] = -1;
    int q[MAXN], h = 0, t = 0; side[0] = 0; q[t++] = 0;
    while (h < t) { int x = q[h++]; for (int i = 0; i < g->deg[x]; i++) { int y = g->nb[x][i]; if (side[y] < 0) { side[y] = 1 - side[x]; q[t++] = y; } } }
}

typedef struct { int x, y; } E2;

/* best re-insertion into base B (n0 vertices, cubic except none): returns best far, fills ia/ib (edge ids) */
static long best_insert(const G *B, int *bestA, int *bestB, int *bestOK) {
    static E2 EL[MAXN * 2]; int NE = 0;
    bip(B);
    for (int x = 0; x < B->n; x++) for (int i = 0; i < B->deg[x]; i++) { int y = B->nb[x][i]; if (x < y) { if (side[x] == 0) { EL[NE].x = x; EL[NE].y = y; } else { EL[NE].x = y; EL[NE].y = x; } NE++; } }
    long best = 1L << 40; *bestOK = 0;
    G g;
    int n0 = B->n;
    for (int i = 0; i < NE; i++) for (int j = i + 1; j < NE; j++) {
        if (EL[i].x == EL[j].x || EL[i].y == EL[j].y) continue;
        int a = n0, b = n0 + 1;
        g_init(&g, n0 + 2);
        for (int x = 0; x < n0; x++) for (int k = 0; k < B->deg[x]; k++) { int y = B->nb[x][k]; if (x < y) g_add(&g, x, y); }
        g_del(&g, EL[i].x, EL[i].y); g_del(&g, EL[j].x, EL[j].y);
        g_add(&g, a, EL[i].y); g_add(&g, a, EL[j].y); g_add(&g, b, EL[i].x); g_add(&g, b, EL[j].x); g_add(&g, a, b);
        long f = far_cost(&g);
        if (f < best) { best = f; *bestA = i; *bestB = j; *bestOK = 1; }
    }
    return best;
}

/* build the reduced graph for move (a,b,choice) of G with n vertices; returns reduced graph in R, relabelled */
static int reduce_graph(const G *G0, int a, int b, int choice, G *R) {
    /* outer neighbours */
    int x[2], y[2], nx = 0, ny = 0;
    for (int i = 0; i < G0->deg[a]; i++) if (G0->nb[a][i] != b) y[ny++] = G0->nb[a][i];
    for (int i = 0; i < G0->deg[b]; i++) if (G0->nb[b][i] != a) x[nx++] = G0->nb[b][i];
    /* side: x are A-side (same side as a? b is in B, its neighbours are in A) ; y are B-side */
    int map[MAXN]; int idx = 0;
    for (int v = 0; v < G0->n; v++) { if (v == a || v == b) map[v] = -1; else map[v] = idx++; }
    g_init(R, G0->n - 2);
    for (int u = 0; u < G0->n; u++) for (int i = 0; i < G0->deg[u]; i++) { int w = G0->nb[u][i]; if (u < w && u != a && u != b && w != a && w != b) g_add(R, map[u], map[w]); }
    int p = map[y[0]], q = map[y[1]], r = map[x[0]], s = map[x[1]];
    int e1a, e1b, e2a, e2b;
    if (choice == 0) { e1a = r; e1b = p; e2a = s; e2b = q; } else { e1a = r; e1b = q; e2a = s; e2b = p; }
    if (g_has(R, e1a, e1b) || g_has(R, e2a, e2b)) return 0;
    if (e1a == e2a || e1b == e2b) return 0;
    g_add(R, e1a, e1b); g_add(R, e2a, e2b);
    for (int v = 0; v < R->n; v++) if (R->deg[v] != 3) return 0;
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: lns IN PASSES SEED OUTPREFIX TLIM\n"); return 2; }
    G cur; if (g_load(&cur, argv[1]) < 0) return 2;
    long passes = atol(argv[2]); rng_seed(strtoull(argv[3], 0, 10)); const char *pre = argv[4]; double tlim = atof(argv[5]);
    long curf = far_cost(&cur), bestf = curf;
    char fn[512]; snprintf(fn, sizeof fn, "%s_best.edges", pre); g_write(&cur, fn);
    clock_t t0 = clock();
    fprintf(stderr, "start n=%d far=%ld\n", cur.n, curf);
    for (long ps = 0; ps < passes; ps++) {
        /* list of candidate moves: all edges (a in A, b in B) x 2 choices, shuffled */
        bip(&cur);
        int na = 0; static int ma[MAXN * 4], mb[MAXN * 4], mc[MAXN * 4];
        for (int x = 0; x < cur.n; x++) if (side[x] == 0) for (int i = 0; i < cur.deg[x]; i++) { int y = cur.nb[x][i];
            ma[na] = x; mb[na] = y; mc[na] = 0; na++; ma[na] = x; mb[na] = y; mc[na] = 1; na++; }
        for (int i = na - 1; i > 0; i--) { int j = rng_int(i + 1); int t; t = ma[i]; ma[i] = ma[j]; ma[j] = t; t = mb[i]; mb[i] = mb[j]; mb[j] = t; t = mc[i]; mc[i] = mc[j]; mc[j] = t; }
        int improved = 0;
        for (int k = 0; k < na; k++) {
            int a = ma[k], b = mb[k];
            G R;
            if (!reduce_graph(&cur, a, b, mc[k], &R)) continue;
            int ia, ib, ok; long f = best_insert(&R, &ia, &ib, &ok);
            if (!ok) continue;
            if (f < curf || (f == curf && rng_int(3) == 0 && 0)) {
                /* rebuild the new graph of size n: R plus pair inserted with edges ia, ib */
                G N; int n0 = R.n; g_init(&N, n0 + 2);
                int ax[2], bx[2];
                bip(&R);
                E2 EL[MAXN*2]; int NE = 0;
                for (int u = 0; u < R.n; u++) for (int i = 0; i < R.deg[u]; i++) { int w = R.nb[u][i]; if (u < w) { if (side[u] == 0) { EL[NE].x = u; EL[NE].y = w; } else { EL[NE].x = w; EL[NE].y = u; } NE++; } }
                for (int u = 0; u < R.n; u++) for (int i = 0; i < R.deg[u]; i++) { int w = R.nb[u][i]; if (u < w) g_add(&N, u, w); }
                g_del(&N, EL[ia].x, EL[ia].y); g_del(&N, EL[ib].x, EL[ib].y);
                g_add(&N, n0, EL[ia].y); g_add(&N, n0, EL[ib].y); g_add(&N, n0 + 1, EL[ia].x); g_add(&N, n0 + 1, EL[ib].x); g_add(&N, n0, n0 + 1);
                int ok2 = 1; for (int v = 0; v < N.n; v++) if (N.deg[v] != 3) ok2 = 0;
                if (!ok2) continue;
                long nf = far_cost(&N);
                if (nf != f) { fprintf(stderr, "internal mismatch %ld %ld\n", nf, f); continue; }
                cur = N; curf = f; improved = 1;
                if (curf < bestf) { bestf = curf; g_write(&cur, fn); fprintf(stderr, "pass %ld move %d/%d best far=%ld (%.0fs)\n", ps, k, na, bestf, (double)(clock() - t0) / CLOCKS_PER_SEC); }
                if (bestf == 0) break;
                break; /* restart pass with a fresh shuffle after each improvement */
            }
            if ((double)(clock() - t0) / CLOCKS_PER_SEC > tlim) break;
        }
        fprintf(stderr, "pass %ld done cur=%ld best=%ld improved=%d (%.0fs)\n", ps, curf, bestf, improved, (double)(clock() - t0) / CLOCKS_PER_SEC);
        if (bestf == 0 || (double)(clock() - t0) / CLOCKS_PER_SEC > tlim) break;
        if (!improved) break;
    }
    printf("%s: lns n=%d best=%ld cur=%ld\n", pre, cur.n, bestf, curf);
    return 0;
}
