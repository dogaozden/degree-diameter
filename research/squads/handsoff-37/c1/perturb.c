/* apply K random bipartite 2-switches (keeping simple, cubic, sides) to an edge list. usage: perturb IN K SEED OUT */
#include "g37.h"
int main(int c, char **v) {
    G g; if (g_load(&g, v[1]) < 0) return 2;
    int K = atoi(v[2]); rng_seed(strtoull(v[3], 0, 10));
    int n = g.n; int side[MAXN]; for (int i = 0; i < n; i++) side[i] = -1;
    { int q[MAXN], h = 0, t = 0; side[0] = 0; q[t++] = 0; while (h < t) { int x = q[h++]; for (int i = 0; i < g.deg[x]; i++) { int y = g.nb[x][i]; if (side[y] < 0) { side[y] = 1 - side[x]; q[t++] = y; } } } }
    int done = 0;
    while (done < K) {
        int a = rng_int(n); if (side[a] != 0) continue;
        int c_ = g.nb[a][rng_int(3)];
        int b = rng_int(n); if (side[b] != 0 || b == a) continue;
        int d = g.nb[b][rng_int(3)];
        if (c_ == d) continue;
        if (g_has(&g, a, d) || g_has(&g, b, c_)) continue;
        g_del(&g, a, c_); g_del(&g, b, d); g_add(&g, a, d); g_add(&g, b, c_); done++;
    }
    g_write(&g, v[4]); return 0;
}
