/* Z_k voltage lift of W(16) (base: 8738 vertices, 17-regular, diameter 4).
   Lift vertex = base*k + g. Cost = number of ordered pairs (s,t), s in a source sample of base vertices
   (fibre 0), t any lift vertex, with lift distance > 5. Hill-climbs voltages on non-tree edges.
   Usage: zlift W16.edges k seed iters sample_size [out.edges] */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
static int nb, mb, K;
static int *eu, *ev, *ew;          /* base edges, voltage ew[e] in Z_K for u->v */
static int *adjs, *adjt, *adje;    /* CSR base adjacency: target, edge id, sign */
static int *ast;
static int *dist; static int *queue;
static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void){ rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int *tree;
/* voltage of directed traversal from u along adjacency slot i */
static inline int volt(int e, int forward){ int g = ew[e]; return forward ? g : (K - g) % K; }
static long cost_from(int s){ /* BFS on lift from (s,0), depth<=5; returns #targets with dist>5 */
    long N = (long)nb * K; for (long i = 0; i < N; i++) dist[i] = -1;
    long h = 0, t = 0; long src = (long)s * K; dist[src] = 0; queue[t++] = src; long reached = 1;
    while (h < t) { long x = queue[h++]; int dx = dist[x]; if (dx == 5) continue;
        int u = x / K, g = x % K;
        for (int i = ast[u]; i < ast[u + 1]; i++) {
            int v = adjt[i]; int ff = (adje[i] >= 0);
            int e = ff ? adje[i] : -adje[i] - 1;
            int gg = (g + volt(e, ff)) % K; long y = (long)v * K + gg;
            if (dist[y] < 0) { dist[y] = dx + 1; queue[t++] = y; reached++; }
        }
    }
    return N - reached;
}
static long cost(int *samp, int ns){ long c = 0; for (int i = 0; i < ns; i++) c += cost_from(samp[i]); return c; }
int main(int argc, char **argv){
    FILE *f = fopen(argv[1], "r"); K = atoi(argv[2]); rs ^= (uint64_t)atol(argv[3]) * 2654435761ULL + 1; long iters = atol(argv[4]); int ns = atoi(argv[5]);
    if (fscanf(f, "%d", &nb) != 1) return 2;
    eu = malloc(sizeof(int) * 80000); ev = malloc(sizeof(int) * 80000); ew = calloc(80000, sizeof(int));
    mb = 0; while (fscanf(f, "%d %d", &eu[mb], &ev[mb]) == 2) mb++;
    int *deg = calloc(nb + 1, sizeof(int)); for (int e = 0; e < mb; e++) { deg[eu[e]]++; deg[ev[e]]++; }
    ast = calloc(nb + 1, sizeof(int)); for (int i = 0; i < nb; i++) ast[i + 1] = ast[i] + deg[i];
    adjt = malloc(sizeof(int) * 2 * mb); adje = malloc(sizeof(int) * 2 * mb); int *pos = calloc(nb, sizeof(int));
    for (int e = 0; e < mb; e++) {
        int u = eu[e], v = ev[e];
        adjt[ast[u] + pos[u]] = v; adje[ast[u] + pos[u]] = e; pos[u]++;   /* forward: u->v, sign + */
        adjt[ast[v] + pos[v]] = u; adje[ast[v] + pos[v]] = -e - 1; pos[v]++; /* backward */
    }
    /* spanning tree (BFS from 0) gets voltage 0 */
    tree = calloc(mb, sizeof(int)); int *seen = calloc(nb, sizeof(int)); int *q = malloc(sizeof(int) * nb);
    int h = 0, t = 0; q[t++] = 0; seen[0] = 1;
    while (h < t) { int u = q[h++]; for (int i = ast[u]; i < ast[u + 1]; i++) { int v = adjt[i]; if (!seen[v]) { seen[v] = 1; q[t++] = v; tree[abs(adje[i]) >= 0 ? (adje[i] >= 0 ? adje[i] : -adje[i]-1) : 0] = 1; } } }
    int *free_e = malloc(sizeof(int) * mb); int nf = 0; for (int e = 0; e < mb; e++) if (!tree[e]) free_e[nf++] = e;
    for (int i = 0; i < nf; i++) ew[free_e[i]] = (int)(rnd() % K);
    dist = malloc(sizeof(int) * (size_t)nb * K); queue = malloc(sizeof(int) * (size_t)nb * K);
    /* fixed source sample (random base vertices) */
    int *samp = malloc(sizeof(int) * ns); for (int i = 0; i < ns; i++) samp[i] = (int)(rnd() % nb);
    long cur = cost(samp, ns); printf("init cost(sample %d)=%ld\n", ns, cur); fflush(stdout);
    for (long it = 0; it < iters && cur > 0; it++) {
        int e = free_e[rnd() % nf]; int old = ew[e]; int nw = (int)(rnd() % K); if (nw == old) continue;
        ew[e] = nw; long c = cost(samp, ns);
        if (c <= cur) { if (c < cur && it % 20 == 0) { printf("it %ld cost %ld\n", it, c); fflush(stdout);} cur = c; } else ew[e] = old;
    }
    /* full evaluation over all base sources */
    long full = 0; for (int s = 0; s < nb; s++) full += cost_from(s);
    printf("final sample cost %ld, full cost (all %d fibre-0 sources, ordered pairs) %ld\n", cur, nb, full);
    if (argc > 6) { FILE *o = fopen(argv[6], "w"); long N = (long)nb * K; fprintf(o, "%ld\n", N);
        for (int e = 0; e < mb; e++) for (int g = 0; g < K; g++) fprintf(o, "%ld %ld\n", (long)eu[e]*K+g, (long)ev[e]*K+((g+ew[e])%K));
        fclose(o); printf("wrote %s\n", argv[6]); }
    return 0;
}
