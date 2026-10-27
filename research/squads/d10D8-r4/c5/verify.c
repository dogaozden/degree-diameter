/* r2-c3 independent checker (no bitmasks): plain BFS on the voltage lift of GH(q) + 2 matchings.
   usage: verify hexbin solfile D      (group must be "cyc m" in the solution's group line)
   Lift vertices (x, h), x < 2N (points 0..N-1, lines N..2N-1), h in Z_m. Edges exactly as lift3.c build_adj:
   point p -- line l with voltage hv[l*Q1+k] (p = k-th point of l); p -- sigma_t(p) with voltage mv_t[p].
   The lift is abelian-regular, so eccentricities at (x,0) for all x < 2N give the diameter. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: verify hexbin solfile [D]\n"); return 1; }
    FILE *f = fopen(argv[1], "rb"); if (!f) return 1;
    int32_t h[3]; if (fread(h, 4, 3, f) != 3) return 1;
    int q = h[0], N = h[1], Q1 = q + 1;
    int32_t *pl = malloc(4L * N * Q1); if (fread(pl, 4, (size_t)N * Q1, f) != (size_t)N * Q1) return 1; fclose(f);
    FILE *s = fopen(argv[2], "r"); if (!s) return 1;
    int qq, J, m, D0; long cost; char line[512], kind[16] = ""; int ga = 0;
    if (fscanf(s, "%d %d %d %d %ld", &qq, &J, &m, &D0, &cost) != 5) return 1;
    fgets(line, sizeof line, s); fgets(line, sizeof line, s);
    if (sscanf(line, "%15s %d", kind, &ga) != 2 || strcmp(kind, "cyc") || ga != m) { fprintf(stderr, "need cyc %d\n", m); return 1; }
    if (qq != q) { fprintf(stderr, "q mismatch\n"); return 1; }
    int D = argc > 3 ? atoi(argv[3]) : 8;
    int *sig = malloc(sizeof(int) * J * N), *mv = malloc(sizeof(int) * J * N), *hv = malloc(sizeof(int) * N * Q1);
    for (int i = 0; i < J * N; i++) if (fscanf(s, "%d", &sig[i]) != 1) return 1;
    for (int i = 0; i < J * N; i++) if (fscanf(s, "%d", &mv[i]) != 1) return 1;
    for (int i = 0; i < N * Q1; i++) if (fscanf(s, "%d", &hv[i]) != 1) return 1;
    fclose(s);
    int V = 2 * N, Dg = Q1 + J;
    int *nb = malloc(sizeof(int) * V * Dg), *nv = malloc(sizeof(int) * V * Dg), *cnt = calloc(V, sizeof(int));
    for (int l = 0; l < N; l++) for (int k = 0; k < Q1; k++) {
        int p = pl[l * Q1 + k], g = hv[l * Q1 + k] % m;
        nb[p * Dg + cnt[p]] = N + l; nv[p * Dg + cnt[p]++] = g;
        nb[(N + l) * Dg + cnt[N + l]] = p; nv[(N + l) * Dg + cnt[N + l]++] = (m - g) % m;
    }
    for (int t = 0; t < J; t++) for (int p = 0; p < N; p++) {
        int l = sig[t * N + p], g = mv[t * N + p] % m;
        nb[p * Dg + cnt[p]] = N + l; nv[p * Dg + cnt[p]++] = g;
        nb[(N + l) * Dg + cnt[N + l]] = p; nv[(N + l) * Dg + cnt[N + l]++] = (m - g) % m;
    }
    for (int v = 0; v < V; v++) if (cnt[v] != Dg) { fprintf(stderr, "degree %d at %d\n", cnt[v], v); return 1; }
    int VM = V * m;
    int *dist = malloc(sizeof(int) * VM), *queue = malloc(sizeof(int) * VM);
    long unreached = 0; int worst_src = -1; long worst = 0;
    for (int x = 0; x < V; x++) {
        for (int i = 0; i < VM; i++) dist[i] = -1;
        int src = x * m; dist[src] = 0; int qh = 0, qt = 0; queue[qt++] = src;
        while (qh < qt) {
            int u = queue[qh++]; int d = dist[u]; if (d >= D) continue;
            int v = u / m, hh = u % m;
            for (int i = 0; i < Dg; i++) {
                int w = nb[v * Dg + i] * m + (hh + nv[v * Dg + i]) % m;
                if (dist[w] < 0) { dist[w] = d + 1; queue[qt++] = w; }
            }
        }
        long bad = VM - qt; unreached += bad; if (bad > worst) { worst = bad; worst_src = x; }
    }
    printf("VERIFY q=%d vertices=%d lift=%d D=%d unreached_pairs=%ld worst_source=%d (%ld) %s\n", q, V, VM, D,
           unreached, worst_src, worst, unreached == 0 ? "DIAMETER_OK" : "FAIL");
    return 0;
}
