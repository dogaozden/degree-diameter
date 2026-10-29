/* dcenum.c: exhaustive search over bi-coset graphs exported by dc_export.g.
 * Input (.dc): "nA nB ndc", then per double coset "contrib nedges" and its edges "a b" (A-point, B-point).
 * Every union S of double cosets with total contribution DELTA gives a DELTA-regular bipartite graph on nA + nB
 * vertices (|H| = |K|). G is transitive on each side, so diameter <= D iff the A-point 0 and the B-point 0 both
 * reach every vertex within D. Cost = number of vertices missed by the two BFS. Prints the best cost and every
 * cost-0 union, and writes the first cost-0 graph (or the best one) as an edge list.
 * usage: dcenum FILE.dc DELTA [D=5] [OUT.edges] [MAXSETS]
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int nA, nB, ndc, DELTA, D = 5;
static int *contrib, *nE, **EA, **EB;
static int chosen[64], nch;
static long long tested = 0, nsol = 0, maxsets = 0;
static long bestcost = 1L << 40;
static int bestset[64], nbest;
static int *adj, *deg;   /* vertices 0..nA-1 A, nA..nA+nB-1 B */
static int *dist, *q;
static const char *outpath;

static int bfs(int s) {
    int n = nA + nB; for (int i = 0; i < n; i++) dist[i] = -1;
    int h = 0, t = 0; dist[s] = 0; q[t++] = s;
    while (h < t) { int x = q[h++]; if (dist[x] == D) continue;
        for (int i = 0; i < deg[x]; i++) { int y = adj[x * DELTA + i]; if (dist[y] < 0) { dist[y] = dist[x] + 1; q[t++] = y; } } }
    return n - t;
}
static void write_graph(int *set, int k) {
    if (!outpath) return;
    FILE *f = fopen(outpath, "w"); fprintf(f, "%d\n", nA + nB);
    for (int j = 0; j < k; j++) { int d = set[j]; for (int e = 0; e < nE[d]; e++) fprintf(f, "%d %d\n", EA[d][e], nA + EB[d][e]); }
    fclose(f);
}
static void test(void) {
    tested++;
    int n = nA + nB; memset(deg, 0, sizeof(int) * n);
    for (int j = 0; j < nch; j++) { int d = chosen[j];
        for (int e = 0; e < nE[d]; e++) { int a = EA[d][e], b = nA + EB[d][e];
            if (deg[a] >= DELTA || deg[b] >= DELTA) { fprintf(stderr, "degree overflow\n"); exit(1); }
            adj[a * DELTA + deg[a]++] = b; adj[b * DELTA + deg[b]++] = a; } }
    long c = bfs(0); c += bfs(nA);
    if (c < bestcost) { bestcost = c; nbest = nch; memcpy(bestset, chosen, sizeof(int) * nch); if (!nsol) write_graph(chosen, nch); }
    if (c == 0) { nsol++; printf("SOL"); for (int j = 0; j < nch; j++) printf(" %d", chosen[j]); printf("\n"); fflush(stdout);
        if (nsol == 1) write_graph(chosen, nch); }
}
static void rec(int start, int left) {
    if (maxsets && tested >= maxsets) return;
    if (left == 0) { test(); return; }
    for (int d = start; d < ndc; d++) if (contrib[d] <= left) { chosen[nch++] = d; rec(d + 1, left - contrib[d]); nch--; }
}

int main(int argc, char **argv) {
    if (argc < 3) return 2;
    DELTA = atoi(argv[2]); if (argc > 3) D = atoi(argv[3]); if (argc > 4) outpath = argv[4]; if (argc > 5) maxsets = atoll(argv[5]);
    int len = strlen(argv[1]);
    if (len > 4 && !strcmp(argv[1] + len - 4, ".dc2")) {
        FILE *f = fopen(argv[1], "r"); int ng; if (!f || fscanf(f, "%d %d %d %d", &nA, &nB, &ng, &ndc) != 4) return 2;
        int **gA = malloc(sizeof(int *) * ng), **gB = malloc(sizeof(int *) * ng);
        for (int s = 0; s < ng; s++) { gA[s] = malloc(sizeof(int) * nA); gB[s] = malloc(sizeof(int) * nB);
            for (int a = 0; a < nA; a++) if (fscanf(f, "%d", &gA[s][a]) != 1) return 2;
            for (int b = 0; b < nB; b++) if (fscanf(f, "%d", &gB[s][b]) != 1) return 2; }
        /* Schreier tree on A-points: permB[a] = B-image map of an element sending A-point 0 to a */
        int *permB = malloc(sizeof(int) * (size_t)nA * nB), *seen = calloc(nA, sizeof(int)), *qq = malloc(sizeof(int) * nA);
        for (int b = 0; b < nB; b++) permB[b] = b;
        int h = 0, t = 0; seen[0] = 1; qq[t++] = 0;
        while (h < t) { int a = qq[h++];
            for (int s = 0; s < ng; s++) { int a2 = gA[s][a]; if (seen[a2]) continue; seen[a2] = 1; qq[t++] = a2;
                for (int b = 0; b < nB; b++) permB[(size_t)a2 * nB + b] = gB[s][permB[(size_t)a * nB + b]]; } }
        if (t != nA) { fprintf(stderr, "not transitive on A\n"); return 2; }
        contrib = malloc(sizeof(int) * ndc); nE = malloc(sizeof(int) * ndc); EA = malloc(sizeof(int *) * ndc); EB = malloc(sizeof(int *) * ndc);
        for (int d = 0; d < ndc; d++) { int c; if (fscanf(f, "%d", &c) != 1) return 2; int bs[256];
            for (int k = 0; k < c; k++) if (fscanf(f, "%d", &bs[k]) != 1) return 2;
            contrib[d] = c; nE[d] = c * nA; EA[d] = malloc(sizeof(int) * nE[d]); EB[d] = malloc(sizeof(int) * nE[d]);
            int e = 0; for (int a = 0; a < nA; a++) for (int k = 0; k < c; k++) { EA[d][e] = a; EB[d][e] = permB[(size_t)a * nB + bs[k]]; e++; } }
        fclose(f);
        goto loaded;
    }
    FILE *f = fopen(argv[1], "r"); if (!f || fscanf(f, "%d %d %d", &nA, &nB, &ndc) != 3) return 2;
    contrib = malloc(sizeof(int) * ndc); nE = malloc(sizeof(int) * ndc); EA = malloc(sizeof(int *) * ndc); EB = malloc(sizeof(int *) * ndc);
    for (int d = 0; d < ndc; d++) { if (fscanf(f, "%d %d", &contrib[d], &nE[d]) != 2) return 2;
        EA[d] = malloc(sizeof(int) * nE[d]); EB[d] = malloc(sizeof(int) * nE[d]);
        for (int e = 0; e < nE[d]; e++) if (fscanf(f, "%d %d", &EA[d][e], &EB[d][e]) != 2) return 2; }
    fclose(f);
  loaded:;
    int n = nA + nB; adj = malloc(sizeof(int) * n * DELTA); deg = malloc(sizeof(int) * n); dist = malloc(sizeof(int) * n); q = malloc(sizeof(int) * n);
    int hist[64] = {0}; for (int d = 0; d < ndc; d++) if (contrib[d] < 64) hist[contrib[d]]++;
    fprintf(stderr, "%s: nA %d nB %d double cosets %d; contributions", argv[1], nA, nB, ndc);
    for (int c = 1; c < 64; c++) if (hist[c]) fprintf(stderr, " %dx%d", hist[c], c); fprintf(stderr, "\n");
    rec(0, DELTA);
    printf("RESULT %s tested %lld solutions %lld best %ld vertices %d set", argv[1], tested, nsol, bestcost, n);
    for (int j = 0; j < nbest; j++) printf(" %d", bestset[j]); printf("\n");
    return 0;
}
