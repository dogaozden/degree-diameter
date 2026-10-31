/* c8: 3+3 orbit cyclic voltage lift, simulated annealing.
   Base: 3 orbits A0..A2 and 3 orbits B0..B2, each of size m (cyclic group Z_m acting by translation).
   Base multigraph: 18 base edges (ea[k], eb[k], eg[k]); every A-orbit and every B-orbit is used 6 times,
   so the lift is 6-regular, bipartite, N = 6m vertices.
   Lifted edges: A(a,x) -- B(b,(x+g) mod m) for every base edge (a,b,g) and every x in Z_m.
   Score = number of unordered vertex pairs at distance > 5 (0 = bipartite diameter-5 graph on N vertices).
   Usage: lift33 m iters seed T0 T1 restarts outdir
*/
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <limits.h>

#define NB 18

static int m, N;
static int ea[NB], eb[NB], eg[NB];
static int *adj, *deg, *vis, *q;
static int stampc = 0;
static uint64_t rs;

static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline double urand(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
static inline int irand(int n) { return (int)(rnd() % (uint64_t)n); }

static int valid_state(void) {
    int ca[3] = {0, 0, 0}, cb[3] = {0, 0, 0};
    for (int k = 0; k < NB; k++) { ca[ea[k]]++; cb[eb[k]]++; }
    for (int i = 0; i < 3; i++) if (ca[i] != 6 || cb[i] != 6) return 0;
    for (int k = 0; k < NB; k++) for (int l = k + 1; l < NB; l++)
        if (ea[k] == ea[l] && eb[k] == eb[l] && eg[k] == eg[l]) return 0;
    return 1;
}

static int bfs_reach5(int src) {
    stampc++;
    int qh = 0, qt = 0;
    q[qt++] = src; vis[src] = stampc;
    for (int lev = 0; lev < 5; lev++) {
        int end = qt;
        if (qh == end) break;
        for (; qh < end; qh++) {
            int u = q[qh];
            for (int j = 0; j < 6; j++) {
                int v = adj[u * 6 + j];
                if (vis[v] != stampc) { vis[v] = stampc; q[qt++] = v; }
            }
        }
    }
    return qt;
}

/* returns number of unordered pairs at distance > 5 */
static long evaluate(void) {
    memset(deg, 0, N * sizeof(int));
    for (int k = 0; k < NB; k++) {
        for (int x = 0; x < m; x++) {
            int u = ea[k] * m + x;
            int v = 3 * m + eb[k] * m + (x + eg[k]) % m;
            adj[u * 6 + deg[u]++] = v;
            adj[v * 6 + deg[v]++] = u;
        }
    }
    long ordered = 0;
    for (int o = 0; o < 6; o++) {
        int src = (o < 3) ? o * m : 3 * m + (o - 3) * m;   /* representative of each orbit */
        int reach = bfs_reach5(src);
        ordered += (long)m * (N - reach);
    }
    return ordered / 2;
}

static void write_state(const char *path, long score) {
    FILE *f = fopen(path, "w");
    if (!f) return;
    fprintf(f, "m %d score %ld\n", m, score);
    for (int k = 0; k < NB; k++) fprintf(f, "%d %d %d\n", ea[k], eb[k], eg[k]);
    fclose(f);
}

static void write_edges(const char *path) {
    FILE *f = fopen(path, "w");
    if (!f) return;
    fprintf(f, "%d\n", N);
    for (int k = 0; k < NB; k++)
        for (int x = 0; x < m; x++)
            fprintf(f, "%d %d\n", ea[k] * m + x, 3 * m + eb[k] * m + (x + eg[k]) % m);
    fclose(f);
}

int main(int argc, char **argv) {
    if (argc < 8) { fprintf(stderr, "usage: lift33 m iters seed T0 T1 restarts outdir\n"); return 1; }
    m = atoi(argv[1]);
    long iters = atol(argv[2]);
    rs = (uint64_t)atoll(argv[3]) * 2654435761ULL + 88172645463325252ULL;
    double T0 = atof(argv[4]), T1 = atof(argv[5]);
    int restarts = atoi(argv[6]);
    const char *outdir = argv[7];
    N = 6 * m;
    adj = malloc(sizeof(int) * N * 6);
    deg = malloc(sizeof(int) * N);
    vis = calloc(N, sizeof(int));
    q = malloc(sizeof(int) * N);

    long gbest = LONG_MAX;
    int bA[NB], bB[NB], bG[NB];
    for (int r = 0; r < restarts; r++) {
        /* random valid initial state */
        do {
            for (int k = 0; k < NB; k++) ea[k] = k / 6;
            int pool[NB];
            for (int k = 0; k < NB; k++) pool[k] = k / 6;
            for (int k = NB - 1; k > 0; k--) { int j = irand(k + 1); int t = pool[j]; pool[j] = pool[k]; pool[k] = t; }
            for (int k = 0; k < NB; k++) { eb[k] = pool[k]; eg[k] = irand(m); }
        } while (!valid_state());
        long cur = evaluate();
        long best = cur;
        for (long it = 0; it < iters && cur > 0; it++) {
            double T = T0 * pow(T1 / T0, (double)it / (double)iters);
            int sa[NB], sb[NB], sg[NB];
            memcpy(sa, ea, sizeof ea); memcpy(sb, eb, sizeof eb); memcpy(sg, eg, sizeof eg);
            int r0 = irand(10);
            if (r0 < 6) {
                int k = irand(NB);
                eg[k] = irand(m);
            } else if (r0 < 8) {
                int k = irand(NB), l = irand(NB);
                if (k == l) continue;
                int t = eb[k]; eb[k] = eb[l]; eb[l] = t;
            } else {
                int k = irand(NB), l = irand(NB);
                if (k == l) continue;
                int t = ea[k]; ea[k] = ea[l]; ea[l] = t;
            }
            if (!valid_state()) { memcpy(ea, sa, sizeof ea); memcpy(eb, sb, sizeof eb); memcpy(eg, sg, sizeof eg); continue; }
            long nw = evaluate();
            if (nw <= cur || urand() < exp(-(double)(nw - cur) / T)) {
                cur = nw;
                if (cur < best) best = cur;
                if (cur < gbest) {
                    gbest = cur;
                    memcpy(bA, ea, sizeof ea); memcpy(bB, eb, sizeof eb); memcpy(bG, eg, sizeof eg);
                    fprintf(stderr, "m=%d restart=%d it=%ld T=%.3f new global best %ld\n", m, r, it, T, gbest);
                }
            } else {
                memcpy(ea, sa, sizeof ea); memcpy(eb, sb, sizeof eb); memcpy(eg, sg, sizeof eg);
            }
            if (it % 200000 == 0 && it > 0)
                fprintf(stderr, "m=%d restart=%d it=%ld T=%.3f cur=%ld best=%ld gbest=%ld\n", m, r, it, T, cur, best, gbest);
        }
        fprintf(stderr, "m=%d restart %d finished: best %ld (global %ld)\n", m, r, best, gbest);
        if (gbest == 0) break;
    }
    memcpy(ea, bA, sizeof ea); memcpy(eb, bB, sizeof eb); memcpy(eg, bG, sizeof eg);
    char path[512];
    snprintf(path, sizeof path, "%s/state_m%d.txt", outdir, m);
    write_state(path, gbest);
    if (gbest == 0) {
        snprintf(path, sizeof path, "%s/edges_m%d.txt", outdir, m);
        write_edges(path);
        printf("FOUND m=%d N=%d edges file %s\n", m, N, path);
    }
    printf("m=%d N=%d best_bad_pairs=%ld\n", m, N, gbest);
    return 0;
}
