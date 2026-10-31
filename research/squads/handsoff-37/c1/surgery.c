/* c1 exhaustive insertion: from base graph (n0 vertices, A = [0,n0/2), B = rest), delete k edges
   x_i y_i (x in A, y in B) and add a ~ y_1..y_k, b ~ x_1..x_k (new A vertex a = n0, new B vertex b = n0+1),
   and optionally the edge a~b (mode "2ab": k=2 with a~b). k=2 (with ab) or k=3 (no ab).
   Fixes the first edge (base must be arc-transitive: conder168). Usage: surgery BASE k OUTPREFIX [TOP] */
#include "g37.h"

typedef struct { int x, y; } E2;
typedef struct { long far; int idx[3]; int k; } Hit;

static G base; static E2 EL[400]; static int NE;

static void build(G *g, int *dx, int *dy, int k, int with_ab) {
    int n0 = base.n, a = n0, b = n0 + 1;
    g_init(g, n0 + 2);
    for (int x = 0; x < n0; x++) for (int i = 0; i < base.deg[x]; i++) { int y = base.nb[x][i]; if (x < y) g_add(g, x, y); }
    for (int i = 0; i < k; i++) g_del(g, dx[i], dy[i]);
    for (int i = 0; i < k; i++) g_add(g, a, dy[i]);
    for (int i = 0; i < k; i++) g_add(g, b, dx[i]);
    if (with_ab) g_add(g, a, b);
}

#define HMAX 200000
static long hist[HMAX];
#define TOPK 40
static Hit top[TOPK]; static int ntop = 0;
static void consider(long far, int *idx, int k) {
    if (ntop == TOPK && far >= top[TOPK - 1].far) return;
    int pos = ntop < TOPK ? ntop++ : TOPK - 1;
    top[pos].far = far; top[pos].k = k; for (int i = 0; i < k; i++) top[pos].idx[i] = idx[i];
    while (pos > 0 && top[pos - 1].far > top[pos].far) { Hit t = top[pos]; top[pos] = top[pos - 1]; top[pos - 1] = t; pos--; }
}

int main(int argc, char **argv) {
    if (argc < 4) { fprintf(stderr, "usage: surgery BASE k OUTPREFIX\n"); return 2; }
    if (g_load(&base, argv[1]) < 0) return 2;
    int k = atoi(argv[2]); const char *pre = argv[3];
    NE = 0;
    for (int x = 0; x < base.n / 2; x++) for (int i = 0; i < base.deg[x]; i++) { int y = base.nb[x][i]; EL[NE].x = x; EL[NE].y = y; NE++; }
    fprintf(stderr, "base n=%d edges=%d\n", base.n, NE);
    int dx[3], dy[3], idx[3]; G g; long best = 1L << 40; long cnt = 0;
    int e1 = 0; dx[0] = EL[e1].x; dy[0] = EL[e1].y;
    int with_ab = (k == 2);
    if (k == 2) {
        for (int e2 = 0; e2 < NE; e2++) {
            if (EL[e2].x == dx[0] || EL[e2].y == dy[0]) continue;
            dx[1] = EL[e2].x; dy[1] = EL[e2].y;
            build(&g, dx, dy, 2, with_ab);
            long f = far_cost(&g); cnt++;
            if (f < HMAX) hist[f]++;
            idx[0] = e1; idx[1] = e2; consider(f, idx, 2);
            if (f < best) best = f;
        }
    } else {
        for (int e2 = 0; e2 < NE; e2++) {
            if (EL[e2].x == dx[0] || EL[e2].y == dy[0]) continue;
            for (int e3 = e2 + 1; e3 < NE; e3++) {
                if (EL[e3].x == dx[0] || EL[e3].y == dy[0]) continue;
                if (EL[e3].x == EL[e2].x || EL[e3].y == EL[e2].y) continue;
                dx[1] = EL[e2].x; dy[1] = EL[e2].y; dx[2] = EL[e3].x; dy[2] = EL[e3].y;
                build(&g, dx, dy, 3, 0);
                long f = far_cost(&g); cnt++;
                if (f < HMAX) hist[f]++;
                idx[0] = e1; idx[1] = e2; idx[2] = e3; consider(f, idx, 3);
                if (f < best) best = f;
            }
        }
    }
    printf("k=%d n=%d graphs=%ld best_far=%ld\n", k, base.n + 2, cnt, best);
    printf("histogram (far: count) first 15 values:");
    int shown = 0;
    for (long f = 0; f < HMAX && shown < 15; f++) if (hist[f]) { printf(" %ld:%ld", f, hist[f]); shown++; }
    printf("\n");
    /* write top graphs */
    for (int t = 0; t < ntop && t < 5; t++) {
        int ii[3]; for (int i = 0; i < top[t].k; i++) ii[i] = top[t].idx[i];
        int ddx[3], ddy[3];
        for (int i = 0; i < top[t].k; i++) { ddx[i] = EL[ii[i]].x; ddy[i] = EL[ii[i]].y; }
        build(&g, ddx, ddy, top[t].k, top[t].k == 2);
        char fn[512]; snprintf(fn, sizeof fn, "%s_k%d_top%d_far%ld.edges", pre, k, t, top[t].far);
        g_write(&g, fn);
        printf("top%d far=%ld file=%s\n", t, top[t].far, fn);
    }
    return 0;
}
