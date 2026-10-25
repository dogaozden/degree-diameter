/* exact_cover.c (card c8, squad round 1, cell 12-5).
   Exact lift-level coverage check for a per-edge route-chart controller (mlift_ejoint output).
   The lift is built exactly as research/d12D5/elift.py: A-vertex (a,x) -- B-vertex (b, A_e x + lam*b_e) for every
   controller line "a b e", x in F_3^4, lam in F_3; A-vertex id a*81+id(x), B-vertex id nA+b*81+id(y), id(v)=v0+3v1+9v2+27v3.
   Bipartite lift: diameter <= 5 iff every same-side pair is at lift distance <= 4 (a cross pair p,q has a neighbour q'
   on p's side with dist(p,q') <= 4). Counts:
     uncovered  = ordered same-side lift pairs (p,q), p != q, at distance > 4 (or unreachable), over the WHOLE lift.
     pair_cost  = number of (side, base vertex i, controller vertex c) such that some lift source (i,z) of block i has an
                  uncovered lift vertex over the fibre of c. This is the controller-level quantity that mlift_ejoint
                  prints as best_cost (its criterion is sufficient, so pair_cost <= best_cost is expected).
   Source reduction: the voltage group acts on the lift by (a,x) -> (a*h, x) (right multiplication inside each block), so
   one source per (side, block i, z) suffices; a block is N consecutive controller vertices i*N .. i*N+N-1.
   usage: exact_cover CONTROLLER ECHART N [all]      ('all' = every lift vertex as a source, for validation)
   Prints the full distance histogram (same numbers as bfs_all in rep-free mode). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define NV 81
static void vecof(int id, int *v) { for (int r = 0; r < 4; r++) { v[r] = id % 3; id /= 3; } }
static int idof(const int *v) { return v[0] + 3 * v[1] + 9 * v[2] + 27 * v[3]; }
static int md3(int x) { return ((x % 3) + 3) % 3; }

int main(int argc, char **argv) {
    if (argc < 4) { fprintf(stderr, "usage: exact_cover CONTROLLER ECHART N [all]\n"); return 1; }
    int allmode = argc > 4 && strcmp(argv[4], "all") == 0;
    int N = atoi(argv[3]);
    FILE *f = fopen(argv[1], "r"); if (!f) { perror(argv[1]); return 2; }
    int cap = 1 << 12, nr = 0, a, b, e;
    int *ca = malloc(cap * sizeof(int)), *cb = malloc(cap * sizeof(int)), *ce = malloc(cap * sizeof(int));
    while (fscanf(f, "%d %d %d", &a, &b, &e) == 3) {
        if (nr == cap) { cap *= 2; ca = realloc(ca, cap * sizeof(int)); cb = realloc(cb, cap * sizeof(int)); ce = realloc(ce, cap * sizeof(int)); }
        ca[nr] = a; cb[nr] = b; ce[nr] = e; nr++;
    }
    fclose(f);
    int m = 0, ne = 0;
    for (int r = 0; r < nr; r++) {
        if (ca[r] + 1 > m) m = ca[r] + 1;
        if (cb[r] + 1 > m) m = cb[r] + 1;
        if (ce[r] + 1 > ne) ne = ce[r] + 1;
    }
    if (nr != 4 * m) { fprintf(stderr, "controller has %d lines, expected 4m = %d\n", nr, 4 * m); return 3; }
    if (N <= 0 || m % N) { fprintf(stderr, "N=%d does not divide m=%d\n", N, m); return 3; }
    int k = m / N;
    /* per-edge chart: 16 entries of A_e row-major, then 4 entries of b_e */
    f = fopen(argv[2], "r"); if (!f) { perror(argv[2]); return 2; }
    int *AE = malloc(ne * 16 * sizeof(int)), *BE = malloc(ne * 4 * sizeof(int));
    for (int i = 0; i < ne; i++) {
        for (int t = 0; t < 16; t++) { int x; if (fscanf(f, "%d", &x) != 1) { fprintf(stderr, "short echart\n"); return 4; } AE[i * 16 + t] = md3(x); }
        for (int t = 0; t < 4; t++) { int x; if (fscanf(f, "%d", &x) != 1) { fprintf(stderr, "short echart\n"); return 4; } BE[i * 4 + t] = md3(x); }
    }
    fclose(f);
    /* lift */
    int nA = NV * m, V = 2 * nA;
    int *adj = malloc((size_t)V * 12 * sizeof(int)), *deg = calloc(V, sizeof(int));
    for (int r = 0; r < nr; r++) {
        int aa = ca[r], bb = cb[r], ee = ce[r];
        for (int x = 0; x < NV; x++) {
            int xv[4], y0[4]; vecof(x, xv);
            for (int i = 0; i < 4; i++) { int s = 0; for (int c = 0; c < 4; c++) s += AE[ee * 16 + 4 * i + c] * xv[c]; y0[i] = s % 3; }
            for (int lam = 0; lam < 3; lam++) {
                int yv[4]; for (int i = 0; i < 4; i++) yv[i] = (y0[i] + lam * BE[ee * 4 + i]) % 3;
                int u = aa * NV + x, w = nA + bb * NV + idof(yv);
                if (deg[u] >= 12 || deg[w] >= 12) { fprintf(stderr, "degree overflow\n"); return 5; }
                adj[u * 12 + deg[u]++] = w; adj[w * 12 + deg[w]++] = u;
            }
        }
    }
    for (int v = 0; v < V; v++) {
        if (deg[v] != 12) { fprintf(stderr, "lift degree %d at vertex %d\n", deg[v], v); return 5; }
        for (int i = 0; i < 12; i++) for (int j = i + 1; j < 12; j++) if (adj[v * 12 + i] == adj[v * 12 + j]) { fprintf(stderr, "repeated lift edge\n"); return 5; }
    }
    /* sources: rep mode = (side, block i, z) with controller vertex i*N; all mode = every lift vertex */
    int *dist = malloc(V * sizeof(int)), *q = malloc(V * sizeof(int));
    int *cnt = malloc(m * sizeof(int));
    int *zcnt = calloc(2 * k * m, sizeof(int));  /* (side,block,fibre c): number of sources with an uncovered point over c */
    long long *ucnt = calloc(2 * k * m, sizeof(long long)); /* same pairs: total uncovered points over c, summed over sources */
    long long uncovered = 0, unreached = 0, hist[128] = {0};
    int diam = 0, nsrc = 0;
    int nsrc_total = allmode ? V : 2 * k * NV;
    for (int idx = 0; idx < nsrc_total; idx++) {
        int u;
        if (allmode) u = idx;
        else {
            int s = idx / (k * NV), rem = idx % (k * NV), i = rem / NV, z = rem % NV;
            u = (s == 0 ? 0 : nA) + (i * N) * NV + z;
        }
        int s = u >= nA ? 1 : 0, lo = s == 0 ? 0 : nA, hi = s == 0 ? nA : V;
        long long w = allmode ? 1 : N;   /* orbit size of the source under the voltage group */
        for (int v = 0; v < V; v++) dist[v] = -1;
        int h = 0, t = 0; dist[u] = 0; q[t++] = u;
        while (h < t) { int x = q[h++]; for (int j = 0; j < 12; j++) { int y = adj[x * 12 + j]; if (dist[y] < 0) { dist[y] = dist[x] + 1; q[t++] = y; } } }
        unreached += w * (V - t);
        int ecc = 0;
        for (int j = 0; j < t; j++) { int d = dist[q[j]]; hist[d] += w; if (d > ecc) ecc = d; }
        if (ecc > diam) diam = ecc;
        for (int c = 0; c < m; c++) cnt[c] = 0;
        long long un = 0;
        for (int v = lo; v < hi; v++) if (dist[v] < 0 || dist[v] > 4) { un++; cnt[(v - lo) / NV]++; }
        uncovered += w * un;
        int blk = ((u - lo) / NV) / N;   /* block of the source's controller vertex */
        /* pair flags use the block's first source (controller vertex blk*N), as in mlift_ejoint's cost; in all mode the
           other sources of a block are translates under the voltage group and are not flagged separately */
        if (((u - lo) / NV) % N == 0) for (int c = 0; c < m; c++) if (cnt[c]) { zcnt[(s * k + blk) * m + c]++; ucnt[(s * k + blk) * m + c] += cnt[c]; }
        nsrc++;
    }
    long long pair_cost = 0, pair_z = 0;
    for (int j = 0; j < 2 * k * m; j++) if (zcnt[j]) { pair_cost++; pair_z += zcnt[j]; }
    if (getenv("DETAIL")) { /* flagged pairs: side block fibre  #sources(of 81) with uncovered  #uncovered points summed over sources */
        for (int j = 0; j < 2 * k * m; j++) if (zcnt[j]) printf("  flag side=%c block=%d fibre=%d z_count=%d uncovered_points=%lld\n", j / (k * m) ? 'B' : 'A', (j / m) % k, j % m, zcnt[j], ucnt[j]); }
    printf("lift: m=%d k=%d N=%d lift_vertices=%d edges=%d simple 12-regular\n", m, k, N, V, V * 6);
    printf("mode=%s sources=%d\n", allmode ? "all" : "block-reps", nsrc);
    printf("uncovered_ordered_same_side_pairs(dist>4 or unreached) = %lld  (unreached=%lld)\n", uncovered, unreached);
    printf("pair_cost (side,block,fibre) = %lld  [sum of z-counts = %lld]  diameter=%d\n", pair_cost, pair_z, diam);
    printf("VERDICT: %s\n", (uncovered == 0 && unreached == 0) ? "COVERED (lift diameter <= 5)" : "NOT covered");
    printf("distance histogram (ordered pairs):\n");
    for (int d = 0; d <= diam; d++) printf("  dist %d: %lld\n", d, hist[d]);
    return 0;
}
