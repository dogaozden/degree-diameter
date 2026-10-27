/* verify_lift.c (card c7): independent check of a cyclic lift solution from lift_anneal.
 * Builds the explicit lift (vertex x*m+g), checks simple, regular, bipartite (side parity), connected, then runs
 * plain (non bit-parallel) BFS from every (x,0) and from NS random (x,g).  Prints max eccentricity.
 * Optional 4th argument: write the explicit edge list in apsp.c format ("n" then "a b" lines) for an all-pairs run.
 * usage: verify_lift base.txt sol.sol [NS] [edges_out]
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

int main(int argc, char **argv) {
    FILE *f = fopen(argv[1], "r"); int NB, E;
    if (fscanf(f, "%d %d", &NB, &E) != 2) return 2;
    int *eu = malloc(E * 4), *ev = malloc(E * 4), *et = malloc(E * 4);
    for (int e = 0; e < E; e++) if (fscanf(f, "%d %d %d", &eu[e], &ev[e], &et[e]) != 3) return 2;
    fclose(f);
    FILE *g = fopen(argv[2], "r"); int m, D;
    if (fscanf(g, "%d %d", &m, &D) != 2) return 3;
    int *w = malloc(E * 4);
    for (int e = 0; e < E; e++) if (fscanf(g, "%d", &w[e]) != 1) return 3;
    fclose(g);
    int NS = argc >= 4 ? atoi(argv[3]) : 200;
    /* side of base vertices: u of each edge is side 0 */
    int *side = malloc(NB * 4); for (int x = 0; x < NB; x++) side[x] = -1;
    /* BFS 2-colouring */
    int *deg = calloc(NB, 4); for (int e = 0; e < E; e++) { deg[eu[e]]++; deg[ev[e]]++; }
    int *st = malloc((NB + 1) * 4); st[0] = 0; for (int x = 0; x < NB; x++) st[x + 1] = st[x] + deg[x];
    int *by = malloc(2 * E * 4), *be = malloc(2 * E * 4), *fl = calloc(NB, 4);
    for (int e = 0; e < E; e++) { int u = eu[e], v = ev[e];
        by[st[u] + fl[u]] = v; be[st[u] + fl[u]++] = e; by[st[v] + fl[v]] = u; be[st[v] + fl[v]++] = e; }
    int *qu = malloc(NB * 4); int qh = 0, qt = 0; side[0] = 0; qu[qt++] = 0;
    while (qh < qt) { int x = qu[qh++]; for (int k = st[x]; k < st[x + 1]; k++) { int y = by[k]; if (side[y] < 0) { side[y] = 1 - side[x]; qu[qt++] = y; } } }
    for (int e = 0; e < E; e++) if (side[eu[e]] != 0 || side[ev[e]] != 1) { printf("base not bipartite\n"); return 4; }
    for (int x = 0; x < NB; x++) if (deg[x] != 10) { printf("base degree %d at %d\n", deg[x], x); return 4; }
    long n = (long)NB * m;
    /* explicit lift adjacency, degree 10 */
    int *adj = malloc(n * 10 * sizeof(int));
    for (int x = 0; x < NB; x++) { int c = 0; (void)c; }
    int *cnt = calloc(n, sizeof(int));
    for (int e = 0; e < E; e++) {
        int u = eu[e], v = ev[e];
        for (int gg = 0; gg < m; gg++) {
            long a = (long)u * m + gg, b = (long)v * m + (gg + w[e]) % m;
            adj[a * 10 + cnt[a]++] = (int)b;
            adj[b * 10 + cnt[b]++] = (int)a;
        }
    }
    int bad = 0;
    for (long x = 0; x < n; x++) {
        if (cnt[x] != 10) { bad = 1; break; }
        for (int i = 0; i < 10; i++) for (int j = i + 1; j < 10; j++) if (adj[x * 10 + i] == adj[x * 10 + j]) bad = 2;
    }
    printf("n=%ld m=%d D(target)=%d  simple+10-regular: %s\n", n, m, D, bad == 0 ? "yes" : (bad == 1 ? "NO (degree)" : "NO (multi-edge)"));
    if (bad) return 5;
    if (argc >= 5) {
        FILE *o = fopen(argv[4], "w"); fprintf(o, "%ld\n", n);
        for (long x = 0; x < n; x++) for (int i = 0; i < 10; i++) if (adj[x * 10 + i] > x) fprintf(o, "%ld %d\n", x, adj[x * 10 + i]);
        fclose(o); printf("edge list written: %s\n", argv[4]);
    }
    /* plain BFS from (x,0) for every base x, and NS random sources */
    int *dist = malloc(n * 4); int *queue = malloc(n * 4);
    int maxecc = 0; long unreached_total = 0; uint64_t rr = 1234567;
    long nsrc = NB + NS;
    for (long si = 0; si < nsrc; si++) {
        long s;
        if (si < NB) s = (long)si * m; else { rr ^= rr << 13; rr ^= rr >> 7; rr ^= rr << 17; s = (long)(rr % NB) * m + (long)(rr / NB % m); }
        for (long x = 0; x < n; x++) dist[x] = -1;
        dist[s] = 0; qh = 0; qt = 0; queue[qt++] = (int)s;
        int ecc = 0;
        while (qh < qt) { int x = queue[qh++]; for (int i = 0; i < 10; i++) { int y = adj[(long)x * 10 + i]; if (dist[y] < 0) { dist[y] = dist[x] + 1; if (dist[y] > ecc) ecc = dist[y]; queue[qt++] = y; } } }
        if (qt != n) unreached_total += n - qt;
        if (ecc > maxecc) maxecc = ecc;
    }
    printf("sources: %d base (x,0) + %d random (x,g); connected=%s; max eccentricity = %d (diameter %s D=%d)\n",
           NB, NS, unreached_total ? "NO" : "yes", maxecc, maxecc <= D ? "<=" : ">", D);
    return 0;
}
