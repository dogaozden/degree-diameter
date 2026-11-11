/* sa_repair.c: simulated annealing on a cubic bipartite graph with 2-switch moves, to remove pairs at distance > D.

   cost = sum over ordered pairs (s,t) of max(0, dist(s,t) - D)     (all-pairs BFS, exact)
   move = 2-switch: edges (a,b),(c,d) with a,c white  ->  (a,d),(c,b)   (keeps cubic, bipartite, simple)

   Usage: sa_repair EDGEFILE D ITERS T0 T1 SEED OUT
     EDGEFILE: "n m" then m lines "u v" with u white (u < n/2 by convention of the file; any labelling works as long
     as the sides are given: the first vertex of each line is white).
     OUT: written when cost 0 is reached (edge list in the same format) and also with the best state at the end.
*/
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>

#define MAXV 1024

static int n, D;
static int adj[MAXV][3];
static int white[MAXV], isw[MAXV];
static int nw;
static unsigned long long rs;

static unsigned long long rnd(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs;
}
static double urand(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int dist[MAXV], q[MAXV];

static long cost_all(void) {
    long c = 0;
    for (int s = 0; s < n; s++) {
        for (int v = 0; v < n; v++) dist[v] = -1;
        int h = 0, t = 0;
        q[t++] = s; dist[s] = 0;
        while (h < t) {
            int v = q[h++];
            for (int j = 0; j < 3; j++) {
                int w = adj[v][j];
                if (dist[w] < 0) { dist[w] = dist[v] + 1; q[t++] = w; }
            }
        }
        if (t < n) { c += (long)(n - t) * 100; /* disconnected: heavy */ }
        for (int i = 0; i < t; i++) if (dist[q[i]] > D) c += dist[q[i]] - D;
    }
    return c;
}

static int has_edge(int a, int b) {
    for (int j = 0; j < 3; j++) if (adj[a][j] == b) return 1;
    return 0;
}
static void repl(int v, int old, int nw_) {
    for (int j = 0; j < 3; j++) if (adj[v][j] == old) { adj[v][j] = nw_; return; }
    fprintf(stderr, "repl failed\n"); exit(2);
}

static void write_graph(const char *path) {
    FILE *f = fopen(path, "w");
    if (!f) return;
    fprintf(f, "%d %d\n", n, 3 * n / 2);
    for (int a = 0; a < n; a++) if (isw[a])
        for (int j = 0; j < 3; j++) fprintf(f, "%d %d\n", a, adj[a][j]);
    fclose(f);
}

int main(int argc, char **argv) {
    if (argc < 8) { fprintf(stderr, "usage: sa_repair EDGEFILE D ITERS T0 T1 SEED OUT\n"); return 2; }
    FILE *f = fopen(argv[1], "r");
    if (!f) { perror(argv[1]); return 2; }
    D = atoi(argv[2]);
    long iters = atol(argv[3]);
    double T0 = atof(argv[4]), T1 = atof(argv[5]);
    rs = strtoull(argv[6], NULL, 10) * 2654435761ULL + 88172645463325252ULL;
    const char *out = argv[7];
    int m;
    if (fscanf(f, "%d %d", &n, &m) != 2) return 2;
    int deg[MAXV];
    for (int v = 0; v < n; v++) deg[v] = 0;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (fscanf(f, "%d %d", &u, &v) != 2) return 2;
        if (deg[u] >= 3 || deg[v] >= 3) { fprintf(stderr, "not cubic\n"); return 2; }
        adj[u][deg[u]++] = v;
        adj[v][deg[v]++] = u;
        isw[u] = 1; isw[v] = 0;
    }
    fclose(f);
    nw = 0;
    for (int v = 0; v < n; v++) if (isw[v]) white[nw++] = v;
    long cur = cost_all();
    long best = cur;
    fprintf(stderr, "start n %d whites %d cost %ld\n", n, nw, cur);
    for (long it = 0; it < iters && cur > 0; it++) {
        double T = T0 * pow(T1 / T0, (double)it / iters);
        int a = white[rnd() % nw];
        int c = white[rnd() % nw];
        if (a == c) continue;
        int ja = rnd() % 3, jc = rnd() % 3;
        int b = adj[a][ja], d = adj[c][jc];
        if (b == d) continue;
        if (has_edge(a, d) || has_edge(c, b)) continue;
        /* apply */
        repl(a, b, d); repl(c, d, b); repl(b, a, c); repl(d, c, a);
        long nc = cost_all();
        if (nc <= cur || urand() < exp(-(double)(nc - cur) / T)) {
            cur = nc;
            if (cur < best) {
                best = cur;
                fprintf(stderr, "it %ld T %.3f cost %ld\n", it, T, cur);
            }
        } else {
            /* revert: (a,d)->(a,b), (c,b)->(c,d) */
            repl(a, d, b); repl(c, b, d); repl(b, c, a); repl(d, a, c);
        }
    }
    fprintf(stderr, "final cost %ld best %ld\n", cur, best);
    if (cur == 0) { write_graph(out); printf("SOLVED n %d\n", n); }
    else printf("UNSOLVED best %ld\n", best);
    return 0;
}
