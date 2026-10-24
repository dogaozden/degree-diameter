/* For a vertex-transitive-per-side bipartite graph (edge list), count non-backtracking walks of length l <= L from a
   source s to every vertex (l of the right parity), and report the distribution of the total count per target.
   usage: walkcount EDGES L src */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int main(int c, char **v) {
    FILE *f = fopen(v[1], "r"); int L = atoi(v[2]); long s = atol(v[3]);
    long n, m = 0, cap = 1 << 20; if (fscanf(f, "%ld", &n) != 1) return 1;
    long *U = malloc(cap * 8), *W = malloc(cap * 8), a, b;
    while (fscanf(f, "%ld %ld", &a, &b) == 2) { if (m == cap) { cap *= 2; U = realloc(U, cap * 8); W = realloc(W, cap * 8); } U[m] = a; W[m] = b; m++; }
    long *deg = calloc(n + 1, 8); for (long i = 0; i < m; i++) { deg[U[i]]++; deg[W[i]]++; }
    long *st = calloc(n + 1, 8); for (long i = 0; i < n; i++) st[i + 1] = st[i] + deg[i];
    long *adj = malloc(2 * m * 8), *pos = calloc(n, 8);
    for (long i = 0; i < m; i++) { adj[st[U[i]] + pos[U[i]]++] = W[i]; adj[st[W[i]] + pos[W[i]]++] = U[i]; }
    /* state = directed edge (arc) index into adj: arc j goes from x (owner) to adj[j] */
    long A = 2 * m; long *owner = malloc(A * 8);
    for (long x = 0; x < n; x++) for (long j = st[x]; j < st[x + 1]; j++) owner[j] = x;
    double *cur = calloc(A, 8), *nxt = calloc(A, 8), *tot = calloc(n, 8);
    for (long j = st[s]; j < st[s + 1]; j++) cur[j] = 1;
    for (int l = 1; l <= L; l++) {
        for (long j = 0; j < A; j++) if (cur[j] != 0) tot[adj[j]] += cur[j];
        if (l == L) break;
        memset(nxt, 0, A * 8);
        for (long j = 0; j < A; j++) if (cur[j] != 0) {
            long y = adj[j], x = owner[j];
            for (long k = st[y]; k < st[y + 1]; k++) if (adj[k] != x) nxt[k] += cur[j];
        }
        double *t = cur; cur = nxt; nxt = t;
    }
    /* distribution over the other side (odd lengths) and same side (even lengths) */
    /* side of a vertex = parity of BFS distance */
    int *dist = malloc(n * sizeof(int)); for (long i = 0; i < n; i++) dist[i] = -1;
    long *q = malloc(n * 8); long h = 0, t2 = 0; dist[s] = 0; q[t2++] = s;
    while (h < t2) { long x = q[h++]; for (long k = st[x]; k < st[x + 1]; k++) if (dist[adj[k]] < 0) { dist[adj[k]] = dist[x] + 1; q[t2++] = adj[k]; } }
    for (int par = 0; par < 2; par++) {
        double mn = 1e300; long cnt0 = 0; double sum = 0; long nn = 0;
        for (int d = par; d <= 2 * L; d += 2) {
            double mnd = 1e300, mxd = 0; long nd = 0;
            for (long i = 0; i < n; i++) if (dist[i] == d && i != s) { nd++; if (tot[i] < mnd) mnd = tot[i]; if (tot[i] > mxd) mxd = tot[i]; }
            if (nd) printf("parity %d distance %d: %ld vertices, walks of length <= %d: min %.0f max %.0f\n", par, d, nd, L, mnd, mxd);
        }
    }
    return 0;
}
