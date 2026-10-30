/* rep.c: near-miss repair for bipartite (6,5) graphs (card c7).
 * usage: rep IN.edges OUT.edges      env: KA KB (vertices deleted per colour class, default 9 9),
 *        SECS (default 60), SEED (1), T0 (2.0), T1 (0.05), D (5), PSW (0.8: prob. of a switch move)
 * 1. colour the input graph (must be bipartite); 2. greedily delete KA / KB vertices with the most bad partners
 *    (bad = unordered pairs at distance > D), random tie-break; 3. anneal over edge switches (keep degrees, bipartite,
 *    simple) and free-slot additions, cost = bad pairs on the alive vertices (full bit-parallel recount per move).
 * Writes the best graph (relabelled 0..m-1) as an edge list and prints the final bad count. */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <time.h>
#define MAXN 1024
#define DEG 6

static int n, D = 5;
static int col[MAXN], adj[MAXN][DEG], deg[MAXN], alive[MAXN];
static int badV[MAXN];
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline int ri(int k) { return (int)(rnd() % (uint64_t)k); }
static inline double ru(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int L[MAXN], pos[MAXN], m, nbc[MAXN][DEG], nd[MAXN];
static uint64_t vis[MAXN], fr[MAXN], nx[MAXN];

/* bad pairs among alive vertices; fills badV for alive vertices */
static long eval(void) {
    m = 0;
    for (int v = 0; v < n; v++) if (alive[v]) { pos[v] = m; L[m++] = v; }
    for (int i = 0; i < m; i++) { int v = L[i]; nd[i] = 0; for (int j = 0; j < deg[v]; j++) nbc[i][nd[i]++] = pos[adj[v][j]]; }
    for (int i = 0; i < m; i++) badV[L[i]] = 0;
    long tot = 0;
    for (int s0 = 0; s0 < m; s0 += 64) {
        int ns = m - s0 < 64 ? m - s0 : 64;
        uint64_t full = ns == 64 ? ~0ULL : ((1ULL << ns) - 1);
        for (int x = 0; x < m; x++) { vis[x] = 0; fr[x] = 0; }
        for (int k = 0; k < ns; k++) { vis[s0 + k] |= 1ULL << k; fr[s0 + k] |= 1ULL << k; }
        for (int lev = 1; lev <= D; lev++) {
            int any = 0;
            for (int x = 0; x < m; x++) {
                uint64_t acc = 0;
                for (int j = 0; j < nd[x]; j++) acc |= fr[nbc[x][j]];
                acc &= ~vis[x]; nx[x] = acc; if (acc) any = 1;
            }
            for (int x = 0; x < m; x++) { vis[x] |= nx[x]; fr[x] = nx[x]; }
            if (!any) break;
        }
        for (int x = 0; x < m; x++) {
            int c = __builtin_popcountll(full & ~vis[x]);
            badV[L[x]] += c; tot += c;
        }
    }
    return tot / 2;
}

static int hasEdge(int a, int b) { for (int j = 0; j < deg[a]; j++) if (adj[a][j] == b) return 1; return 0; }
static void addEdge(int a, int b) { adj[a][deg[a]++] = b; adj[b][deg[b]++] = a; }
static void remEdge1(int a, int b) { for (int j = 0; j < deg[a]; j++) if (adj[a][j] == b) { adj[a][j] = adj[a][--deg[a]]; return; } }
static void removeEdge(int a, int b) { remEdge1(a, b); remEdge1(b, a); }
static void deleteVertex(int v) {
    for (int j = 0; j < deg[v]; j++) remEdge1(adj[v][j], v);
    deg[v] = 0; alive[v] = 0;
}

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: rep IN.edges OUT.edges\n"); return 2; }
    FILE *f = fopen(argv[1], "r"); if (!f) return 2;
    long nn; if (fscanf(f, "%ld", &nn) != 1) return 2; n = (int)nn;
    int *eu = malloc(sizeof(int) * 4096), *ev = malloc(sizeof(int) * 4096), ne = 0, cap = 4096, a, b;
    while (fscanf(f, "%d %d", &a, &b) == 2) {
        if (ne == cap) { cap *= 2; eu = realloc(eu, sizeof(int) * cap); ev = realloc(ev, sizeof(int) * cap); }
        eu[ne] = a; ev[ne] = b; ne++;
    }
    fclose(f);
    for (int v = 0; v < n; v++) { deg[v] = 0; alive[v] = 1; }
    for (int i = 0; i < ne; i++) { addEdge(eu[i], ev[i]); }
    for (int v = 0; v < n; v++) if (deg[v] > DEG) { fprintf(stderr, "degree > 6\n"); return 2; }
    /* bipartition */
    for (int v = 0; v < n; v++) col[v] = -1;
    int q[MAXN], h = 0, t = 0;
    for (int s = 0; s < n; s++) if (col[s] < 0) {
        col[s] = 0; q[t++] = s;
        while (h < t) { int x = q[h++]; for (int j = 0; j < deg[x]; j++) { int y = adj[x][j];
            if (col[y] < 0) { col[y] = 1 - col[x]; q[t++] = y; } else if (col[y] == col[x]) { fprintf(stderr, "not bipartite\n"); return 2; } } }
    }
    int KA = getenv("KA") ? atoi(getenv("KA")) : 9, KB = getenv("KB") ? atoi(getenv("KB")) : 9;
    double SECS = getenv("SECS") ? atof(getenv("SECS")) : 60;
    rs ^= (uint64_t)(getenv("SEED") ? atoll(getenv("SEED")) : 1) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 10; i++) rnd();
    double T0 = getenv("T0") ? atof(getenv("T0")) : 2.0, T1 = getenv("T1") ? atof(getenv("T1")) : 0.05;
    double PSW = getenv("PSW") ? atof(getenv("PSW")) : 0.8;
    if (getenv("D")) D = atoi(getenv("D"));

    /* 2. greedy deletion */
    int Kc[2] = {KA, KB};
    for (int side = 0; side < 2; side++) for (int r = 0; r < Kc[side]; r++) {
        eval();
        int best = -1, bv = -1, cnt = 0;
        for (int v = 0; v < n; v++) if (alive[v] && col[v] == side) {
            if (badV[v] > bv) { bv = badV[v]; best = v; cnt = 1; }
            else if (badV[v] == bv && ri(++cnt) == 0) best = v;
        }
        deleteVertex(best);
    }
    long cur = eval();
    fprintf(stderr, "after deletion: alive=%d bad=%ld\n", m, cur);
    long best = cur;
    static int bestAdj[MAXN][DEG], bestDeg[MAXN], bestAlive[MAXN];
    memcpy(bestAdj, adj, sizeof adj); memcpy(bestDeg, deg, sizeof deg); memcpy(bestAlive, alive, sizeof alive);

    /* 3. anneal */
    clock_t c0 = clock(); double it = 0; long acc = 0, tries = 0; double lastrep = 0;
    int *Av = malloc(sizeof(int) * n), *Bv = malloc(sizeof(int) * n);
    while (1) {
        double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
        if (el >= SECS) break;
        double frac = el / SECS, T = T0 * pow(T1 / T0, frac);
        int na = 0, nb = 0, fa = 0, fb = 0;
        for (int v = 0; v < n; v++) if (alive[v]) {
            if (col[v] == 0) { Av[na++] = v; if (deg[v] < DEG) fa++; }
            else { Bv[nb++] = v; if (deg[v] < DEG) fb++; }
        }
        int mv = 0;
        if (fa > 0 && fb > 0 && ru() < 0.5) {
            /* free-slot addition (never increases bad) */
            int x, y, tries2 = 0;
            do { x = Av[ri(na)]; } while (deg[x] >= DEG && ++tries2 < 100000);
            tries2 = 0;
            do { y = Bv[ri(nb)]; } while (deg[y] >= DEG && ++tries2 < 100000);
            if (deg[x] < DEG && deg[y] < DEG && !hasEdge(x, y)) {
                addEdge(x, y); long nw = eval();
                if (nw <= cur) { cur = nw; mv = 1; }
                else { removeEdge(x, y); }
            }
            (void)mv;
        } else {
            int x = Av[ri(na)]; if (deg[x] == 0) continue;
            int y = adj[x][ri(deg[x])];
            int z = Av[ri(na)]; if (deg[z] == 0 || z == x) continue;
            int w = adj[z][ri(deg[z])]; if (w == y) continue;
            if (hasEdge(x, w) || hasEdge(z, y)) continue;
            removeEdge(x, y); removeEdge(z, w); addEdge(x, w); addEdge(z, y);
            long nw = eval(); tries++;
            if (nw <= cur || ru() < exp(-(double)(nw - cur) / T)) { cur = nw; acc++; }
            else { removeEdge(x, w); removeEdge(z, y); addEdge(x, y); addEdge(z, w); }
        }
        it++;
        if (cur < best) {
            best = cur;
            memcpy(bestAdj, adj, sizeof adj); memcpy(bestDeg, deg, sizeof deg); memcpy(bestAlive, alive, sizeof alive);
        }
        if (el - lastrep > 10) { lastrep = el; fprintf(stderr, "t=%.0f T=%.3f cur=%ld best=%ld it=%.0f acc=%ld\n", el, T, cur, best, it, acc); }
    }
    /* write best */
    memcpy(adj, bestAdj, sizeof adj); memcpy(deg, bestDeg, sizeof deg); memcpy(alive, bestAlive, sizeof alive);
    long fin = eval();
    int rel[MAXN], k = 0;
    for (int v = 0; v < n; v++) rel[v] = alive[v] ? k++ : -1;
    FILE *o = fopen(argv[2], "w"); if (!o) return 2;
    int ecount = 0; for (int v = 0; v < n; v++) if (alive[v]) ecount += deg[v];
    fprintf(o, "%d\n", k);
    for (int v = 0; v < n; v++) if (alive[v] && col[v] == 0)
        for (int j = 0; j < deg[v]; j++) fprintf(o, "%d %d\n", rel[v], rel[adj[v][j]]);
    fclose(o);
    fprintf(stderr, "RESULT best=%ld check=%ld n=%d edges=%d iters=%.0f acc=%ld\n", best, fin, k, ecount / 2, it, acc);
    printf("RESULT best=%ld n=%d\n", best, k);
    return 0;
}
