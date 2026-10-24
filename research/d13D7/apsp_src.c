/* apsp_src.c: apsp_wide.c (512 sources per batch, OpenMP) with the BFS sources restricted to the vertex ids in
   SRCFILE (one per line).  Global checks (simple, max degree, bipartite, connected) as in apsp.c; the eccentricities
   are exact for the listed sources.  Used for (2r+1)-copy graphs, where (x, i) -> (x, i+1) (hubs fixed) is an
   automorphism, with SRCFILE = all level-0 vertices and all hubs: then the maximum eccentricity is the diameter.
   Usage: apsp_src EDGES d D SRCFILE */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <omp.h>
#define W 8
int main(int c, char **v) {
    FILE *f = fopen(v[1], "r"); int d = atoi(v[2]), D = atoi(v[3]); long n, m = 0, cap = 1 << 20;
    if (!f || fscanf(f, "%ld", &n) != 1) return 2;
    long *U = malloc(cap * 8), *Wt = malloc(cap * 8); long a, b;
    while (fscanf(f, "%ld %ld", &a, &b) == 2) { if (m == cap) { cap *= 2; U = realloc(U, cap * 8); Wt = realloc(Wt, cap * 8); } U[m] = a; Wt[m] = b; m++; }
    long *deg = calloc(n + 1, 8);
    for (long i = 0; i < m; i++) { if (U[i] == Wt[i] || U[i] < 0 || Wt[i] < 0 || U[i] >= n || Wt[i] >= n) { printf("BAD edge %ld\n", i); return 1; } deg[U[i]]++; deg[Wt[i]]++; }
    long *st = calloc(n + 1, 8); for (long i = 0; i < n; i++) st[i + 1] = st[i] + deg[i];
    int32_t *adj = malloc(2 * m * 4); long *pos = calloc(n, 8);
    for (long i = 0; i < m; i++) { adj[st[U[i]] + pos[U[i]]++] = Wt[i]; adj[st[Wt[i]] + pos[Wt[i]]++] = U[i]; }
    free(U); free(Wt);
    long maxd = 0, mind = n;
    for (long x = 0; x < n; x++) { long k = deg[x]; if (k > maxd) maxd = k; if (k < mind) mind = k;
        for (long i = st[x]; i < st[x + 1]; i++) for (long j = i + 1; j < st[x + 1]; j++) if (adj[i] == adj[j]) { printf("RESULT INVALID repeated edge at %ld\n", x); return 1; } }
    int *col = malloc(n * sizeof(int)); for (long i = 0; i < n; i++) col[i] = -1;
    long *qu = malloc(n * 8); long h = 0, t = 0; col[0] = 0; qu[t++] = 0; int bip = 1;
    while (h < t) { long x = qu[h++]; for (long i = st[x]; i < st[x + 1]; i++) { long y = adj[i]; if (col[y] < 0) { col[y] = 1 - col[x]; qu[t++] = y; } else if (col[y] == col[x]) bip = 0; } }
    if (t != n) { printf("RESULT INVALID disconnected (%ld of %ld)\n", t, n); return 1; }
    long ns_all = 0; long *srcs = malloc(sizeof(long) * n); { FILE *g = fopen(v[4], "r"); long x; while (g && fscanf(g, "%ld", &x) == 1) { if (x < 0 || x >= n) { printf("bad source\n"); return 1; } srcs[ns_all++] = x; } if (g) fclose(g); }
    fprintf(stderr, "%ld sources\n", ns_all);
    int diam = 0, bad = 0; long done = 0, nb = (ns_all + 64 * W - 1) / (64 * W);
    #pragma omp parallel reduction(max:diam) reduction(|:bad)
    {
    uint64_t *vis = aligned_alloc(64, n * 8 * W), *fr = aligned_alloc(64, n * 8 * W), *nx = aligned_alloc(64, n * 8 * W);
    #pragma omp for schedule(dynamic, 1)
    for (long bi = 0; bi < nb; bi++) {
        long s0 = bi * 64 * W; int ns = (ns_all - s0 < 64 * W) ? (int)(ns_all - s0) : 64 * W;
        memset(vis, 0, n * 8 * W); memset(fr, 0, n * 8 * W);
        uint64_t full[W];
        for (int w = 0; w < W; w++) { int lo = 64 * w; full[w] = ns >= lo + 64 ? ~0ULL : (ns > lo ? ((1ULL << (ns - lo)) - 1) : 0); }
        for (int k = 0; k < ns; k++) { long sv = srcs[s0 + k]; vis[sv * W + k / 64] |= 1ULL << (k % 64); fr[sv * W + k / 64] |= 1ULL << (k % 64); }
        int lev = 0;
        for (;;) {
            uint64_t any = 0;
            for (long x = 0; x < n; x++) {
                uint64_t *vx = vis + x * W, *ox = nx + x * W; int isfull = 1;
                for (int w = 0; w < W; w++) if (vx[w] != full[w]) { isfull = 0; break; }
                if (isfull) { for (int w = 0; w < W; w++) ox[w] = 0; continue; }
                uint64_t acc[W]; for (int w = 0; w < W; w++) acc[w] = 0;
                for (long i = st[x]; i < st[x + 1]; i++) { const uint64_t *fy = fr + (long)adj[i] * W; for (int w = 0; w < W; w++) acc[w] |= fy[w]; }
                for (int w = 0; w < W; w++) { acc[w] &= ~vx[w]; ox[w] = acc[w]; vx[w] |= acc[w]; any |= acc[w]; }
            }
            if (!any) break;
            lev++; uint64_t *tmp = fr; fr = nx; nx = tmp;
        }
        for (long x = 0; x < n && !bad; x++) for (int w = 0; w < W; w++) if (vis[x * W + w] != full[w]) { bad = 1; break; }
        if (lev > diam) diam = lev;
        long dn;
        #pragma omp atomic capture
        dn = ++done;
        if (dn % 100 == 0) fprintf(stderr, "%ld/%ld batches, batch diam %d\n", dn, nb, lev);
    }
    free(vis); free(fr); free(nx);
    }
    if (bad) { printf("RESULT INVALID unreached\n"); return 1; }
    printf("n=%ld edges=%ld degree min=%ld max=%ld bipartite=%s diameter=%d\n", n, m, mind, maxd, bip ? "yes" : "no", diam);
    if (bip && maxd <= d && diam <= D) printf("RESULT VALID d=%d D=%d n=%ld (eccentricities of the %ld listed sources)\n", d, D, n, ns_all); else printf("RESULT INVALID\n");
    return 0;
}
