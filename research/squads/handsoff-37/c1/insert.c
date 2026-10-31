/* c1 generic insertion: base graph (any n, bipartite, cubic). Adds two new vertices a (side of the B-side? no:
   a joins the A side, b joins the B side) where A/B are found by BFS colouring of the base from vertex 0.
   Deletes k edges x_i y_i (x in A, y in B) and adds a ~ y_i (all i), b ~ x_i (all i), plus a ~ b when k = 2.
   Enumerates ALL choices of the k edges (k = 2: m^2/2 pairs; k = 3: m^3/6, use only with FIXED=1 which fixes edge 0).
   Usage: insert BASE k FIXED TOPK OUTPREFIX
   Writes top-K graphs as OUTPREFIX_r{rank}_far{F}.edges and prints the histogram head.  */
#include "g37.h"

typedef struct { int x, y; } E2;
typedef struct { long far; int idx[3]; } Hit;
static G base; static E2 EL[MAXN * 2]; static int NE; static int side[MAXN];
#define TOPMAX 256
static Hit top[TOPMAX]; static int ntop = 0, TOPK = 20;
#define HMAX 100000
static long hist[HMAX];

static void bip(const G *g) {
    for (int i = 0; i < g->n; i++) side[i] = -1;
    int q[MAXN], h = 0, t = 0; side[0] = 0; q[t++] = 0;
    while (h < t) { int x = q[h++]; for (int i = 0; i < g->deg[x]; i++) { int y = g->nb[x][i]; if (side[y] < 0) { side[y] = 1 - side[x]; q[t++] = y; } } }
}

static void build(G *g, int *ids, int k) {
    int n0 = base.n, a = n0, b = n0 + 1;
    g_init(g, n0 + 2);
    for (int x = 0; x < n0; x++) for (int i = 0; i < base.deg[x]; i++) { int y = base.nb[x][i]; if (x < y) g_add(g, x, y); }
    for (int i = 0; i < k; i++) g_del(g, EL[ids[i]].x, EL[ids[i]].y);
    for (int i = 0; i < k; i++) g_add(g, a, EL[ids[i]].y);
    for (int i = 0; i < k; i++) g_add(g, b, EL[ids[i]].x);
    if (k == 2) g_add(g, a, b);
}

static void consider(long far, int *ids, int k) {
    if (ntop == TOPK && far >= top[TOPK - 1].far) return;
    int pos = ntop < TOPK ? ntop++ : TOPK - 1;
    top[pos].far = far; for (int i = 0; i < k; i++) top[pos].idx[i] = ids[i];
    while (pos > 0 && top[pos - 1].far > top[pos].far) { Hit t = top[pos]; top[pos] = top[pos - 1]; top[pos - 1] = t; pos--; }
}

int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: insert BASE k FIXED TOPK OUTPREFIX\n"); return 2; }
    if (g_load(&base, argv[1]) < 0) return 2;
    int k = atoi(argv[2]); int fixed = atoi(argv[3]); TOPK = atoi(argv[4]); const char *pre = argv[5];
    bip(&base);
    NE = 0;
    for (int x = 0; x < base.n; x++) for (int i = 0; i < base.deg[x]; i++) { int y = base.nb[x][i]; if (x < y) { if (side[x] == 0) { EL[NE].x = x; EL[NE].y = y; } else { EL[NE].x = y; EL[NE].y = x; } NE++; } }
    int n0 = base.n;
    fprintf(stderr, "base n=%d edges=%d k=%d fixed=%d\n", n0, NE, k, fixed);
    int ids[3]; G g; long cnt = 0, best = 1L << 40;
    int first = fixed ? 0 : 0;
    if (k == 2) {
        int lo = fixed ? 0 : 0;
        for (int i = lo; i < (fixed ? 1 : NE); i++) for (int j = (fixed ? 1 : i + 1); j < NE; j++) {
            if (fixed && j == i) continue;
            if (!fixed && j <= i) continue;
            int ok = 1;
            if (EL[i].x == EL[j].x || EL[i].y == EL[j].y) ok = 0;
            if (!ok) continue;
            ids[0] = i; ids[1] = j; build(&g, ids, 2);
            long f = far_cost(&g); cnt++; if (f < HMAX) hist[f]++; consider(f, ids, 2); if (f < best) best = f;
        }
    } else {
        for (int i = 0; i < (fixed ? 1 : NE); i++) for (int j = (fixed ? 1 : i + 1); j < NE; j++) for (int l = j + 1; l < NE; l++) {
            if (!fixed && (l <= i)) continue;
            int ii[3] = {i, j, l};
            int ok = 1;
            for (int p = 0; p < 3 && ok; p++) for (int q = p + 1; q < 3; q++) if (EL[ii[p]].x == EL[ii[q]].x || EL[ii[p]].y == EL[ii[q]].y) { ok = 0; break; }
            if (!ok) continue;
            ids[0] = i; ids[1] = j; ids[2] = l; build(&g, ids, 3);
            long f = far_cost(&g); cnt++; if (f < HMAX) hist[f]++; consider(f, ids, 3); if (f < best) best = f;
        }
    }
    printf("insert k=%d base_n=%d -> n=%d graphs=%ld best_far=%ld\n", k, n0, n0 + 2, cnt, best);
    printf("hist head:");
    int shown = 0; for (long f = 0; f < HMAX && shown < 12; f++) if (hist[f]) { printf(" %ld:%ld", f, hist[f]); shown++; }
    printf("\n");
    for (int t = 0; t < ntop; t++) {
        int kk = k; build(&g, top[t].idx, kk);
        char fn[600]; snprintf(fn, sizeof fn, "%s_r%02d_far%ld.edges", pre, t, top[t].far);
        g_write(&g, fn);
    }
    printf("top far: "); for (int t = 0; t < ntop && t < 10; t++) printf("%ld ", top[t].far); printf("\n");
    return 0;
}
