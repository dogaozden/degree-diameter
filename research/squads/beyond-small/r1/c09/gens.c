/* usage: gens graph.txt  (graph: n, then m, then m lines "u v"); prints automorphism generators, one per line */
#include "nauty.h"
#include <stdio.h>
#include <stdlib.h>
static int n_glob;
static void automproc(int count, int *perm, int *orbits, int numorbits, int stabvertex, int n) {
    (void)count; (void)orbits; (void)numorbits; (void)stabvertex;
    for (int i = 0; i < n; i++) printf("%d ", perm[i]);
    printf("\n");
}
int main(int argc, char **argv) {
    FILE *f = fopen(argv[1], "r"); int n, m; if (fscanf(f, "%d %d", &n, &m) != 2) return 1;
    int M = SETWORDSNEEDED(n);
    graph *g = calloc((size_t)M * n, sizeof(graph));
    for (int i = 0; i < m; i++) { int u, v; if (fscanf(f, "%d %d", &u, &v) != 2) return 1;
        ADDELEMENT(GRAPHROW(g, u, M), v); ADDELEMENT(GRAPHROW(g, v, M), u); }
    int lab[n], ptn[n], orbits[n]; statsblk stats; DEFAULTOPTIONS_GRAPH(options);
    options.getcanon = FALSE; options.userautomproc = automproc;
    nauty_check(WORDSIZE, M, n, NAUTYVERSIONID);
    densenauty(g, lab, ptn, orbits, &options, &stats, M, n, NULL);
    fprintf(stderr, "grpsize %f * 10^%d, gens reported via callback\n", stats.grpsize1, stats.grpsize2);
    return 0;
}
