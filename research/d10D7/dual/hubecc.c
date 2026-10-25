/* hubecc.c: same-side eccentricity of a bipartite hub graph file ("H m" then m lines "j k": line-side j ~ point-side k).
   Prints the number of same-side pairs at hub-graph distance > LIM (default 6) and the max same-side distance. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int main(int argc, char **argv) {
    FILE *f = fopen(argv[1], "r"); int H, m, lim = argc > 2 ? atoi(argv[2]) : 6; if (!f || fscanf(f, "%d %d", &H, &m) != 2) return 1;
    int *deg = calloc(2 * H, sizeof(int)), *ej = malloc(sizeof(int) * m), *ek = malloc(sizeof(int) * m);
    for (int e = 0; e < m; e++) { if (fscanf(f, "%d %d", &ej[e], &ek[e]) != 2) return 1; deg[ej[e]]++; deg[H + ek[e]]++; }
    int *st = calloc(2 * H + 1, sizeof(int)); for (int v = 0; v < 2 * H; v++) st[v + 1] = st[v] + deg[v];
    int *adj = malloc(sizeof(int) * 2 * m), *pos = calloc(2 * H, sizeof(int));
    for (int e = 0; e < m; e++) { int a = ej[e], b = H + ek[e]; adj[st[a] + pos[a]++] = b; adj[st[b] + pos[b]++] = a; }
    int *d = malloc(sizeof(int) * 2 * H), *qq = malloc(sizeof(int) * 2 * H); long bad = 0; int worst = 0;
    for (int s = 0; s < 2 * H; s++) {
        for (int v = 0; v < 2 * H; v++) d[v] = -1; int h = 0, t = 0; d[s] = 0; qq[t++] = s;
        while (h < t) { int v = qq[h++]; for (int i = st[v]; i < st[v + 1]; i++) { int w = adj[i]; if (d[w] < 0) { d[w] = d[v] + 1; qq[t++] = w; } } }
        int lo = s < H ? 0 : H, hi = lo + H;
        for (int v = lo; v < hi; v++) { int dv = d[v] < 0 ? 99 : d[v]; if (dv > worst) worst = dv; if (dv > lim) bad++; }
    }
    printf("hubs %d per side, edges %d: same-side pairs (ordered) beyond %d: %ld, max same-side distance %d\n", H, m, lim, bad, worst);
    return 0;
}
