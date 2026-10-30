/* Seeded lift annealing (job fresh-6-5): start from a Haar graph H(G,S) written as a voltage lift of an h+h base
 * by a subgroup Gamma of index h, then anneal the voltages freely (the lift stops being a Haar graph).
 *
 * input (from liftseed.g): n (= |Gamma|) h E, the n x n table of Gamma (0 = identity), then E lines "i j v":
 * base edge a_i - b_j with voltage v, lift edges (a_i, g) ~ (b_j, v*g).
 * Lift vertices: A(i,g) = i*n + g, B(j,g) = h*n + j*n + g. Right multiplication by Gamma is an automorphism, so BFS from
 * the 2h vertices (a_i, e), (b_j, e) gives the exact diameter. cost = sum over these sources of vertices beyond D.
 * usage: liftseed FILE D SECONDS SEED [OUTEDGES]
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <time.h>

static int n, h, E, D, *M, *EI, *EJ, *EV, NV, *adjoff, *adj, *dist, *q;
static unsigned long long rs = 88172645463325252ULL;
static unsigned long long rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }

static void build(void) {   /* adjacency in CSR: every A vertex has E_i edges, every B vertex likewise */
    int *deg = calloc(NV, sizeof(int));
    for (int e = 0; e < E; e++) for (int g = 0; g < n; g++) { deg[EI[e] * n + g]++; deg[h * n + EJ[e] * n + M[EV[e] * n + g]]++; }
    adjoff[0] = 0; for (int v = 0; v < NV; v++) adjoff[v + 1] = adjoff[v] + deg[v];
    memset(deg, 0, NV * sizeof(int));
    for (int e = 0; e < E; e++) for (int g = 0; g < n; g++) {
        int a = EI[e] * n + g, b = h * n + EJ[e] * n + M[EV[e] * n + g];
        adj[adjoff[a] + deg[a]++] = b; adj[adjoff[b] + deg[b]++] = a;
    }
    free(deg);
}
static int bfs(int s) {
    for (int v = 0; v < NV; v++) dist[v] = -1;
    int hd = 0, tl = 0, r = 0; dist[s] = 0; q[tl++] = s;
    while (hd < tl) { int x = q[hd++]; r++; if (dist[x] == D) continue;
        for (int k = adjoff[x]; k < adjoff[x + 1]; k++) { int y = adj[k]; if (dist[y] < 0) { dist[y] = dist[x] + 1; q[tl++] = y; } } }
    return NV - r;
}
static int cost(void) {
    build(); int c = 0;
    for (int i = 0; i < h; i++) c += bfs(i * n);
    for (int j = 0; j < h; j++) c += bfs(h * n + j * n);
    return c;
}
static int simple(void) {   /* no two base edges a_i b_j with equal voltage (would give a double edge) */
    for (int e = 0; e < E; e++) for (int f = e + 1; f < E; f++) if (EI[e] == EI[f] && EJ[e] == EJ[f] && EV[e] == EV[f]) return 0;
    return 1;
}
int main(int argc, char **argv) {
    FILE *fp = fopen(argv[1], "r"); D = atoi(argv[2]); double secs = atof(argv[3]); rs ^= (unsigned long long)atoll(argv[4]) * 0x9E3779B97F4A7C15ULL;
    if (fscanf(fp, "%d %d %d", &n, &h, &E) != 3) return 2;
    M = malloc(sizeof(int) * n * n); for (int i = 0; i < n * n; i++) if (fscanf(fp, "%d", &M[i]) != 1) return 2;
    EI = malloc(sizeof(int) * E); EJ = malloc(sizeof(int) * E); EV = malloc(sizeof(int) * E);
    for (int e = 0; e < E; e++) if (fscanf(fp, "%d %d %d", &EI[e], &EJ[e], &EV[e]) != 3) return 2;
    fclose(fp);
    NV = 2 * h * n; adjoff = malloc(sizeof(int) * (NV + 1)); adj = malloc(sizeof(int) * 2 * E * n); dist = malloc(sizeof(int) * NV); q = malloc(sizeof(int) * NV);
    int c = cost(), best = c; int *bestV = malloc(sizeof(int) * E); memcpy(bestV, EV, sizeof(int) * E);
    printf("start cost %d (n=%d h=%d E=%d, %d vertices)\n", c, n, h, E, NV); fflush(stdout);
    double T = 2.0; clock_t t0 = clock(); long it = 0;
    while ((double)(clock() - t0) / CLOCKS_PER_SEC < secs && best > 0) {
        int e = rnd() % E, old = EV[e];
        EV[e] = rnd() % n;
        if (!simple()) { EV[e] = old; continue; }
        int c2 = cost(); it++;
        if (c2 <= c || exp((c - c2) / T) > (rnd() % 1000000) / 1e6) { c = c2; if (c < best) { best = c; memcpy(bestV, EV, sizeof(int) * E); printf("it %ld best %d T %.3f\n", it, best, T); fflush(stdout); } }
        else EV[e] = old;
        T *= 0.99995; if (T < 0.05) { T = 1.5; c = best; memcpy(EV, bestV, sizeof(int) * E); }
    }
    printf("DONE best %d iterations %ld\n", best, it);
    if (argc > 5) { memcpy(EV, bestV, sizeof(int) * E); build(); FILE *o = fopen(argv[5], "w"); fprintf(o, "%d\n", NV);
        for (int v = 0; v < h * n; v++) for (int k = adjoff[v]; k < adjoff[v + 1]; k++) fprintf(o, "%d %d\n", v, adj[k]); fclose(o); }
    return 0;
}
