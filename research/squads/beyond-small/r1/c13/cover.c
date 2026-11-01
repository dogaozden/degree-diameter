/* cover.c: add new vertices to a bipartite graph keeping max degree <= DELTA and diameter <= 6.
   A new vertex u on side A with neighbour set T (subset of deficient B-vertices, deg < DELTA) keeps diameter 6
   iff every old vertex is within distance 5 of T in the old graph (sufficient; new-new pairs follow since
   dist(t1,t2) <= 4 for t2 in B_old covered by T1). Greedy set cover with capacities.
   usage: cover edges DELTA Bcol(0|1|-1 auto) out.edges trials seed */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

int main(int argc, char **argv) {
    if (argc < 7) { fprintf(stderr, "usage\n"); return 1; }
    FILE *f = fopen(argv[1], "r"); if (!f) return 1;
    int n; if (fscanf(f, "%d", &n) != 1) return 1;
    int DELTA = atoi(argv[2]); int Bcol_arg = atoi(argv[3]); const char *outname = argv[4];
    int trials = atoi(argv[5]); srand(atoi(argv[6])); int TMAX = argc > 7 ? atoi(argv[7]) : atoi(argv[2]); if (TMAX > 64) TMAX = 64;
    int cap_eu = 1 << 20, E = 0; int *eu = malloc(sizeof(int) * cap_eu), *ev = malloc(sizeof(int) * cap_eu);
    int a, b;
    while (fscanf(f, "%d %d", &a, &b) == 2) {
        if (E == cap_eu) { cap_eu *= 2; eu = realloc(eu, sizeof(int) * cap_eu); ev = realloc(ev, sizeof(int) * cap_eu); }
        eu[E] = a; ev[E] = b; E++;
    }
    fclose(f);
    int *deg = calloc(n, sizeof(int)), *off = calloc(n + 1, sizeof(int));
    for (int i = 0; i < E; i++) { deg[eu[i]]++; deg[ev[i]]++; }
    for (int v = 0; v < n; v++) off[v + 1] = off[v] + deg[v];
    int *adj = malloc(sizeof(int) * 2 * E), *fill = calloc(n, sizeof(int));
    for (int i = 0; i < E; i++) {
        adj[off[eu[i]] + fill[eu[i]]++] = ev[i];
        adj[off[ev[i]] + fill[ev[i]]++] = eu[i];
    }
    /* 2-colour */
    int *col = malloc(sizeof(int) * n); for (int v = 0; v < n; v++) col[v] = -1;
    int *q = malloc(sizeof(int) * n); int qh = 0, qt = 0;
    col[0] = 0; q[qt++] = 0;
    while (qh < qt) { int v = q[qh++]; for (int j = off[v]; j < off[v + 1]; j++) { int w = adj[j];
        if (col[w] < 0) { col[w] = 1 - col[v]; q[qt++] = w; } else if (col[w] == col[v]) { fprintf(stderr, "not bipartite\n"); return 1; } } }
    int def[2] = {0, 0}; int maxdeg = 0;
    for (int v = 0; v < n; v++) { if (deg[v] < DELTA) def[col[v]]++; if (deg[v] > maxdeg) maxdeg = deg[v]; }
    int Bcol = Bcol_arg; if (Bcol < 0) Bcol = def[0] >= def[1] ? 0 : 1;
    fprintf(stderr, "n=%d E=%d maxdeg=%d deficient colour0=%d colour1=%d using Bcol=%d\n", n, E, maxdeg, def[0], def[1], Bcol);
    int K = 0; int *S = malloc(sizeof(int) * n);
    for (int v = 0; v < n; v++) if (col[v] == Bcol && deg[v] < DELTA) S[K++] = v;
    uint8_t *D = malloc((size_t)K * n);
    for (int k = 0; k < K; k++) {
        uint8_t *d = D + (size_t)k * n; memset(d, 255, n);
        int h = 0, t = 0; d[S[k]] = 0; q[t++] = S[k];
        while (h < t) { int v = q[h++]; for (int j = off[v]; j < off[v + 1]; j++) { int w = adj[j];
            if (d[w] == 255) { d[w] = d[v] + 1; q[t++] = w; } } }
    }
    /* greedy with capacities, several trials keep the best */
    int *cap = malloc(sizeof(int) * K); for (int k = 0; k < K; k++) cap[k] = DELTA - deg[S[k]];
    int bestcount = -1; int *bestT = NULL; int *bestTsize = NULL; int *bestNew = NULL; int *bestNewk = NULL;
    int *bestNewStart = NULL;
    for (int tr = 0; tr < trials; tr++) {
        int *cc = malloc(sizeof(int) * K); memcpy(cc, cap, sizeof(int) * K);
        uint8_t *unc = malloc(n); memset(unc, 1, n);
        int nnew = 0, maxnew = 100000;
        int *edgesNewK = malloc(sizeof(int) * 8 * 100000); int *edgesNewU = malloc(sizeof(int) * 8 * 100000);
        int ne = 0;
        int *chosen = malloc(sizeof(int) * K);
        while (nnew < maxnew) {
            memset(chosen, 0, sizeof(int) * K);
            int Ucnt = n; memset(unc, 1, n);
            int tsz = 0; int Tk[64];
            while (Ucnt > 0 && tsz < TMAX) {
                int best = -1, bg = 0, nties = 0;
                for (int k = 0; k < K; k++) {
                    if (cc[k] <= 0 || chosen[k]) continue;
                    uint8_t *d = D + (size_t)k * n; int g = 0;
                    for (int x = 0; x < n; x++) g += (unc[x] & (d[x] <= 5));
                    if (g > bg) { bg = g; best = k; nties = 1; }
                    else if (g == bg && g > 0 && best >= 0) { nties++; if (rand() % nties == 0) best = k; }
                }
                if (best < 0 || bg == 0) break;
                chosen[best] = 1; Tk[tsz++] = best;
                uint8_t *d = D + (size_t)best * n;
                for (int x = 0; x < n; x++) if (unc[x] && d[x] <= 5) { unc[x] = 0; Ucnt--; }
            }
            if (Ucnt > 0) { if (nnew == 0 && tr == 0) fprintf(stderr, "first vertex: uncovered %d after %d picks\n", Ucnt, tsz); break; }
            if (nnew == 0 && tr == 0) fprintf(stderr, "first vertex covered with %d picks\n", tsz);
            int id = n + nnew;
            for (int i = 0; i < tsz; i++) { edgesNewK[ne] = Tk[i]; edgesNewU[ne] = id; ne++; cc[Tk[i]]--; }
            nnew++;
        }
        fprintf(stderr, "trial %d: added %d new vertices\n", tr, nnew);
        if (nnew > bestcount) {
            bestcount = nnew;
            free(bestNewk); free(bestNew);
            bestNewk = malloc(sizeof(int) * ne); bestNew = malloc(sizeof(int) * ne);
            memcpy(bestNewk, edgesNewK, sizeof(int) * ne); memcpy(bestNew, edgesNewU, sizeof(int) * ne);
            bestTsize = (int *)(intptr_t)ne; /* store edge count */
        }
        free(cc); free(unc); free(chosen); free(edgesNewK); free(edgesNewU);
    }
    int ne = (int)(intptr_t)bestTsize;
    FILE *o = fopen(outname, "w");
    fprintf(o, "%d\n", n + bestcount);
    for (int i = 0; i < E; i++) fprintf(o, "%d %d\n", eu[i], ev[i]);
    for (int i = 0; i < ne; i++) fprintf(o, "%d %d\n", bestNewk[i] >= 0 ? S[bestNewk[i]] : -1, bestNew[i]);
    fclose(o);
    fprintf(stderr, "wrote %s with n=%d, added %d\n", outname, n + bestcount, bestcount);
    return 0;
}
