/* print per-vertex unreached count (ex) histogram, and girth-related info for a graph */
#include "g37.h"
int main(int c, char **v) {
    G g; if (g_load(&g, v[1]) < 0) return 2;
    int ex[MAXN]; long far = far_detail(&g, ex);
    int h[MAXN]; memset(h, 0, sizeof h); int mx = 0;
    for (int i = 0; i < g.n; i++) { h[ex[i]]++; if (ex[i] > mx) mx = ex[i]; }
    printf("far=%ld n=%d\nunreached-per-vertex histogram:", far, g.n);
    for (int k = 0; k <= mx; k++) if (h[k]) printf(" %d:%d", k, h[k]);
    printf("\n");
    return 0;
}
