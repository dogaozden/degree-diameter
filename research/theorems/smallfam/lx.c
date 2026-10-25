/* lx.c: exhaustive search for regular voltage lifts of a small bipartite base multigraph, diameter <= D.

   Lift of base B (vertices 0..k-1, white/black given by the edge list, edges e = {w, b} with voltage a_e in G):
     vertices (u, g); edges (w, g) ~ (b, a_e g).  Right multiplication by G is an automorphism group, so
     diam = max_u ecc((u, e)): one BFS per base vertex.
   G: "tab FILE" (multiplication table as for hx.c) or "meta m k r".
   BASE file: first line "k", then one line per edge "w b" or "w b = e" (voltage fixed to the identity: the gauge
   tree).  Free edges are numbered in file order.  The PLAN file gives the voltage of the first free edge (one index
   per line, e.g. Aut(G)-orbit representatives); the other free edges run over all of G.  Parallel edges must carry
   distinct voltages (else the lift has a multi-edge); this is enforced.
   Usage: lx tab FILE BASE D PLAN [MAXPRINT]  |  lx meta m k r BASE D PLAN [MAXPRINT]
   Env THREADS.  Output: "SOL v1 v2 ..." lines (free-edge voltages, element indices) and a DONE summary with the best
   cost (number of (source, target) pairs at distance > D, summed over sources; a failing first source stops early and
   its cost is multiplied by the number of base vertices).
*/
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#ifdef _OPENMP
#include <omp.h>
#endif

static int N, E, *T, *INV, ISMETA = 0, MM, KK, *RP, D;
static int K, NE, EW[64], EB[64], FIX[64], NF, FREE[64];
static int **LM;
static int DEG[16], ADJE[16][16];  /* base incidence: for vertex u, list of edge ids */
static int COLOR[16];               /* 0 white, 1 black */

static inline int mul(int x, int y) {
    if (!ISMETA) return T[(size_t)x * N + y];
    int a = x / KK, j = x % KK, b = y / KK, l = y % KK;
    return (int)((a + (long long)RP[j] * b) % MM) * KK + (j + l) % KK;
}

typedef struct { int *dist, *q; } work;

/* BFS from (src, e) in the lift with voltages V[edge]; returns number of lift vertices at distance > D */
static int bfs_unc(int src, const int *V, work *w) {
    int n = K * N, *dist = w->dist, *q = w->q;
    for (int i = 0; i < n; i++) dist[i] = -1;
    int head = 0, tail = 0;
    dist[src * N + E] = 0; q[tail++] = src * N + E;
    int reached = 1;
    while (head < tail) {
        int v = q[head++], u = v / N, g = v % N, d = dist[v];
        if (d >= D) continue;
        for (int t = 0; t < DEG[u]; t++) {
            int e = ADJE[u][t], x, h;
            if (COLOR[u] == 0) { x = EB[e]; h = LM[V[e]][g]; }
            else { x = EW[e]; h = LM[INV[V[e]]][g]; }
            int vv = x * N + h;
            if (dist[vv] < 0) { dist[vv] = d + 1; q[tail++] = vv; reached++; }
        }
    }
    return n - reached;
}

static int cost_of(const int *V, work *w) {
    int c = 0;
    for (int u = 0; u < K; u++) {
        int cu = bfs_unc(u, V, w);
        if (cu > 0) { if (u == 0) return cu * K; c += cu; }
    }
    return c;
}

int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: lx tab FILE BASE D PLAN [MAXPRINT] | lx meta m k r BASE D PLAN [MAXPRINT]\n"); return 2; }
    int ai = 1;
    if (!strcmp(argv[ai], "meta")) {
        ISMETA = 1; MM = atoi(argv[ai + 1]); KK = atoi(argv[ai + 2]); int r = atoi(argv[ai + 3]); ai += 4;
        N = MM * KK; E = 0; RP = malloc(sizeof(int) * KK); RP[0] = 1 % MM;
        for (int j = 1; j < KK; j++) RP[j] = (int)((long long)RP[j - 1] * r % MM);
        if ((long long)RP[KK - 1] * r % MM != 1 % MM) { fprintf(stderr, "r^k != 1\n"); return 2; }
    } else {
        FILE *f = fopen(argv[ai + 1], "r"); if (!f) { perror("tab"); return 2; }
        if (fscanf(f, "%d %d", &N, &E) != 2) return 2;
        T = malloc(sizeof(int) * (size_t)N * N);
        for (size_t i = 0; i < (size_t)N * N; i++) if (fscanf(f, "%d", &T[i]) != 1) return 2;
        fclose(f); ai += 2;
    }
    const char *basef = argv[ai]; D = atoi(argv[ai + 1]); const char *planf = argv[ai + 2];
    int maxprint = argc > ai + 3 ? atoi(argv[ai + 3]) : 20;
    /* base */
    FILE *bf = fopen(basef, "r"); if (!bf) { perror("base"); return 2; }
    char line[256]; NE = 0; K = -1;
    while (fgets(line, sizeof line, bf)) {
        if (line[0] == '#' || line[0] == '\n') continue;
        if (K < 0) { K = atoi(line); continue; }
        int w, b; char eq[8] = "";
        int got = sscanf(line, "%d %d %7s", &w, &b, eq);
        if (got < 2) continue;
        EW[NE] = w; EB[NE] = b; FIX[NE] = (got == 3 && eq[0] == '='); NE++;
    }
    fclose(bf);
    for (int u = 0; u < K; u++) { DEG[u] = 0; COLOR[u] = -1; }
    for (int e = 0; e < NE; e++) {
        COLOR[EW[e]] = 0; COLOR[EB[e]] = 1;
        ADJE[EW[e]][DEG[EW[e]]++] = e; ADJE[EB[e]][DEG[EB[e]]++] = e;
    }
    NF = 0; for (int e = 0; e < NE; e++) if (!FIX[e]) FREE[NF++] = e;
    /* group tables */
    INV = malloc(sizeof(int) * N); LM = malloc(sizeof(int *) * N);
    for (int x = 0; x < N; x++) { LM[x] = malloc(sizeof(int) * N); for (int g = 0; g < N; g++) { LM[x][g] = mul(x, g); if (LM[x][g] == E) INV[x] = g; } }
    /* plan */
    FILE *pf = fopen(planf, "r"); if (!pf) { perror("plan"); return 2; }
    int cap = 1024, np = 0, *P = malloc(sizeof(int) * cap), a;
    while (fscanf(pf, "%d", &a) == 1) { if (np == cap) { cap *= 2; P = realloc(P, sizeof(int) * cap); } P[np++] = a; }
    fclose(pf);
    long long tested = 0, nsol = 0; int best = 1 << 30, bestV[64] = {0};
    int threads = getenv("THREADS") ? atoi(getenv("THREADS")) : 1;
#ifdef _OPENMP
    omp_set_num_threads(threads);
#endif
    (void)threads;
#pragma omp parallel
    {
        work w; w.dist = malloc(sizeof(int) * K * N); w.q = malloc(sizeof(int) * K * N);
        int V[64]; long long my_t = 0, my_s = 0; int my_best = 1 << 30, my_bestV[64] = {0};
#pragma omp for schedule(dynamic, 1)
        for (int pi = 0; pi < np; pi++) {
            for (int e = 0; e < NE; e++) V[e] = E;
            V[FREE[0]] = P[pi];
            int idx[64]; for (int t = 1; t < NF; t++) idx[t] = 0;
            for (;;) {
                for (int t = 1; t < NF; t++) V[FREE[t]] = idx[t];
                /* parallel edges distinct */
                int okp = 1;
                for (int e = 0; e < NE && okp; e++) for (int f2 = e + 1; f2 < NE; f2++)
                    if (EW[e] == EW[f2] && EB[e] == EB[f2] && V[e] == V[f2]) { okp = 0; break; }
                if (okp) {
                    int c = cost_of(V, &w); my_t++;
                    if (c < my_best) { my_best = c; memcpy(my_bestV, V, sizeof(int) * NE); }
                    if (c == 0) {
                        my_s++;
#pragma omp critical
                        { if (nsol + my_s <= maxprint) { printf("SOL"); for (int t = 0; t < NF; t++) printf(" %d", V[FREE[t]]); printf("\n"); fflush(stdout); } }
                    }
                }
                int t = NF - 1;
                while (t >= 1 && idx[t] == N - 1) { idx[t] = 0; t--; }
                if (t < 1) break;
                idx[t]++;
            }
        }
#pragma omp critical
        { tested += my_t; nsol += my_s; if (my_best < best) { best = my_best; memcpy(bestV, my_bestV, sizeof(int) * NE); } }
        free(w.dist); free(w.q);
    }
    printf("DONE tested %lld solutions %lld best_cost %d best_voltages", tested, nsol, best);
    for (int t = 0; t < NF; t++) printf(" %d", bestV[FREE[t]]);
    printf("\n");
    return 0;
}
