/* relaxed.c: large "relaxed" sets T of points of a GQ (given as a collinearity graph) in which every point of T is
   collinear with at most one other point of T, and every collinear pair of T is joined by a line NOT in a
   forbidden line set (the spread S).  Simulated annealing on penalty = sum over points of max(0, deg_T - 1)
   + forbidden pairs, maximising |T|.
   input file: n, then for each point: degree k and its k collinear neighbours with the joining line's flag
   (1 = forbidden), i.e. "k  nb1 f1 nb2 f2 ...".  usage: relaxed IN target seed seconds OUT */
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <string.h>
#include <math.h>
int n, *deg, **nb, **fb;
int main(int argc, char **argv) {
    FILE *f = fopen(argv[1], "r"); int target = atoi(argv[2]); srand(atoi(argv[3])); double secs = atof(argv[4]);
    if (fscanf(f, "%d", &n) != 1) return 1;
    deg = malloc(n * sizeof(int)); nb = malloc(n * sizeof(int *)); fb = malloc(n * sizeof(int *));
    for (int i = 0; i < n; i++) { if (fscanf(f, "%d", &deg[i]) != 1) return 1; nb[i] = malloc(deg[i] * sizeof(int)); fb[i] = malloc(deg[i] * sizeof(int));
        for (int k = 0; k < deg[i]; k++) if (fscanf(f, "%d %d", &nb[i][k], &fb[i][k]) != 2) return 1; }
    char *in = calloc(n, 1); int *cnt = calloc(n, sizeof(int)), *cntf = calloc(n, sizeof(int));
    /* cost of vertex v in T: max(0, cnt[v]-1) + cntf[v] (forbidden neighbours in T, counted per endpoint) */
    int best = 0; char *bestin = calloc(n, 1); clock_t t0 = clock();
    int size = 0; long cost = 0;
    #define VC(v) ((cnt[v] > 1 ? cnt[v] - 1 : 0) + cntf[v])
    double T = 0.6;
    long it = 0;
    while ((double)(clock() - t0) / CLOCKS_PER_SEC < secs) {
        it++;
        int v = rand() % n;
        /* delta of toggling v */
        long d = 0;
        if (!in[v]) {
            d += VC(v) == 0 ? 0 : 0;
            /* adding v: v's own cost = max(0,cnt-1)+cntf ; neighbours u in T get cnt+1 (and cntf+1 if forbidden) */
            d += (cnt[v] > 1 ? cnt[v] - 1 : 0) + cntf[v];
            for (int k = 0; k < deg[v]; k++) { int u = nb[v][k]; if (!in[u]) continue; d += (cnt[u] >= 1 ? 1 : 0) + fb[v][k]; }
            double obj = d * 3.0 - 1.0;   /* weight 3 per violation, -1 per point */
            if (obj <= 0 || (double)rand() / RAND_MAX < exp(-obj / T)) {
                in[v] = 1; size++; cost += d;
                for (int k = 0; k < deg[v]; k++) { int u = nb[v][k]; cnt[u]++; cntf[u] += fb[v][k]; }
            }
        } else {
            d -= (cnt[v] > 1 ? cnt[v] - 1 : 0) + cntf[v];
            for (int k = 0; k < deg[v]; k++) { int u = nb[v][k]; if (!in[u]) continue; d -= (cnt[u] >= 2 ? 1 : 0) + fb[v][k]; }
            double obj = d * 3.0 + 1.0;
            if (obj <= 0 || (double)rand() / RAND_MAX < exp(-obj / T)) {
                in[v] = 0; size--; cost += d;
                for (int k = 0; k < deg[v]; k++) { int u = nb[v][k]; cnt[u]--; cntf[u] -= fb[v][k]; }
            }
        }
        if (cost == 0 && size > best) { best = size; memcpy(bestin, in, n); if (best >= target) break; }
        if (it % 200000 == 0) { T *= 0.97; if (T < 0.08) T = 0.6; }
    }
    FILE *o = fopen(argv[5], "w"); fprintf(o, "%d\n", best); for (int i = 0; i < n; i++) if (bestin[i]) fprintf(o, "%d\n", i); fclose(o);
    printf("best %d\n", best);
    return 0;
}
