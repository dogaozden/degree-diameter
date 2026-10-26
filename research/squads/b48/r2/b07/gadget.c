/* b07: local gadget search. Take a valid bipartite 4-regular seed on n0 = 2184 vertices and
 * (edge mode) delete f seed edges near an anchor edge, or (vertex mode) delete one vertex with its 4 edges.
 * Add two new vertices (one A, one B; vertex mode: 3 new, one extra on the removed vertex's side) and
 * re-attach all freed slots by a bipartite perfect matching pi between A-slots and B-slots.
 * Energy = far pairs (unordered, dist > 8) + 100 * multi-edges. Simulated annealing over (F, pi) with restarts.
 * usage: gadget SEED.edges mode(e|v) f R seconds rngseed OUT.edges steps T0 T1 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXI 2200
#define MAXE 5000
#define MAXPOOL 4000
#define MAXL 64
#define W 35
#define NEWBASE 2184

static int n0, ne;
static int eu[MAXE], ev[MAXE];
static int sadj[MAXI][4], sdeg[MAXI];
static int side[MAXI];
static int NI = 2186, NP = 2186;
static int mode_v = 0;
static int f = 3, R = 2;
static int Fi[MAXL];
static int rv = -1;
static int newA[3], nnA, newB[3], nnB;
static int Asl[MAXL], Bsl[MAXL], L;
static int pi_[MAXL];
static int pool[MAXPOOL], npool;
static int adj[MAXI][4], deg[MAXI];
static int present[MAXI];
static uint64_t Bx[2][MAXI][W];
static int lastDup;
static long lastFar;

static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline double urand(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
static inline int irand(int m) { return (int)(rnd() % (uint64_t)m); }
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }

static int aend(int e) { return side[eu[e]] == 0 ? eu[e] : ev[e]; }
static int bend(int e) { return side[eu[e]] == 1 ? eu[e] : ev[e]; }

static int inF(int e) { for (int k = 0; k < f; k++) if (Fi[k] == e) return 1; return 0; }

static void build_slots(void) {
    int la = 0, lb = 0;
    for (int k = 0; k < f; k++) {
        int e = Fi[k], a = aend(e), b = bend(e);
        if (a != rv) Asl[la++] = a;
        if (b != rv) Bsl[lb++] = b;
    }
    for (int i = 0; i < nnA; i++) for (int t = 0; t < 4; t++) Asl[la++] = newA[i];
    for (int i = 0; i < nnB; i++) for (int t = 0; t < 4; t++) Bsl[lb++] = newB[i];
    if (la != lb) { fprintf(stderr, "slot mismatch %d %d\n", la, lb); exit(1); }
    L = la;
}

static long evaluate(void) {
    int dup = 0, bad = 0;
    for (int v = 0; v < NI; v++) {
        deg[v] = 0;
        present[v] = (v < n0 && v != rv) || (v >= n0);
    }
    for (int e = 0; e < ne; e++) {
        if (inF(e)) continue;
        int u = eu[e], v = ev[e];
        if (deg[u] >= 4 || deg[v] >= 4) { bad = 1; continue; }
        adj[u][deg[u]++] = v; adj[v][deg[v]++] = u;
    }
    for (int k = 0; k < L; k++) {
        int a = Asl[k], b = Bsl[pi_[k]];
        int found = 0;
        for (int j = 0; j < deg[a]; j++) if (adj[a][j] == b) { found = 1; break; }
        if (found) { dup++; continue; }
        if (deg[a] >= 4 || deg[b] >= 4) { bad = 1; continue; }
        adj[a][deg[a]++] = b; adj[b][deg[b]++] = a;
    }
    for (int v = 0; v < NI; v++) if (present[v] && deg[v] != 4) bad = 1;
    lastDup = dup;
    if (bad) return 1000000;
    /* bitset balls of radius 8 */
    int cur = 0;
    for (int v = 0; v < NI; v++) {
        for (int w = 0; w < W; w++) Bx[0][v][w] = 0;
        if (present[v]) Bx[0][v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int it = 0; it < 8; it++) {
        int nx = cur ^ 1;
        for (int v = 0; v < NI; v++) {
            if (!present[v]) continue;
            for (int w = 0; w < W; w++) Bx[nx][v][w] = Bx[cur][v][w];
            for (int j = 0; j < deg[v]; j++) {
                int u = adj[v][j];
                for (int w = 0; w < W; w++) Bx[nx][v][w] |= Bx[cur][u][w];
            }
        }
        cur = nx;
    }
    long S = 0;
    for (int v = 0; v < NI; v++) {
        if (!present[v]) continue;
        for (int w = 0; w < W; w++) S += __builtin_popcountll(Bx[cur][v][w]);
    }
    long total = (long)NP * (NP - 1) / 2;
    long within = (S - NP) / 2;
    lastFar = total - within;
    return lastFar + 100L * dup;
}

static void write_graph(const char *path) {
    static int id[MAXI];
    int c = 0;
    for (int v = 0; v < NI; v++) id[v] = present[v] ? c++ : -1;
    FILE *fp = fopen(path, "w");
    if (!fp) return;
    fprintf(fp, "%d\n", c);
    for (int v = 0; v < NI; v++) {
        if (!present[v]) continue;
        for (int j = 0; j < deg[v]; j++) {
            int u = adj[v][j];
            if (u > v) fprintf(fp, "%d %d\n", id[v], id[u]);
        }
    }
    fclose(fp);
}

int main(int argc, char **argv) {
    if (argc < 11) { fprintf(stderr, "usage: gadget SEED mode f R seconds rngseed OUT steps T0 T1\n"); return 1; }
    FILE *fp = fopen(argv[1], "r");
    if (!fp) { perror("seed"); return 1; }
    if (fscanf(fp, "%d", &n0) != 1) return 1;
    ne = 0;
    while (fscanf(fp, "%d %d", &eu[ne], &ev[ne]) == 2) ne++;
    fclose(fp);
    mode_v = (argv[2][0] == 'v');
    f = atoi(argv[3]); R = atoi(argv[4]);
    double secs = atof(argv[5]);
    rs ^= (uint64_t)atoll(argv[6]) * 0x9E3779B97F4A7C15ULL; if (!rs) rs = 1;
    const char *outp = argv[7];
    int steps = atoi(argv[8]);
    double T0 = atof(argv[9]), T1 = atof(argv[10]);
    if (f > MAXL / 2 - 2) { fprintf(stderr, "f too big\n"); return 1; }

    /* adjacency and bipartition */
    for (int v = 0; v < n0; v++) sdeg[v] = 0;
    for (int e = 0; e < ne; e++) {
        sadj[eu[e]][sdeg[eu[e]]++] = ev[e];
        sadj[ev[e]][sdeg[ev[e]]++] = eu[e];
    }
    for (int v = 0; v < n0; v++) side[v] = -1;
    {
        static int q[MAXI]; int h = 0, t = 0;
        side[0] = 0; q[t++] = 0;
        while (h < t) { int v = q[h++]; for (int j = 0; j < sdeg[v]; j++) { int u = sadj[v][j]; if (side[u] < 0) { side[u] = 1 - side[v]; q[t++] = u; } } }
    }
    for (int e = 0; e < ne; e++) if (side[eu[e]] == side[ev[e]]) { fprintf(stderr, "seed not bipartite\n"); return 1; }
    fprintf(stderr, "seed n=%d edges=%d\n", n0, ne);

    double deadline = now() + secs;
    long bestE = 1L << 60, bestFar = 1L << 60; int bestDup = -1;
    static int dist[MAXI];
    static int q2[MAXI];
    int restarts = 0;
    while (now() < deadline) {
        restarts++;
        /* set up the gadget type */
        if (mode_v) {
            rv = irand(n0);
            f = 0;
            for (int e = 0; e < ne; e++) if (eu[e] == rv || ev[e] == rv) Fi[f++] = e;
            if (side[rv] == 0) { nnA = 2; newA[0] = NEWBASE; newA[1] = NEWBASE + 1; nnB = 1; newB[0] = NEWBASE + 2; NI = NEWBASE + 3; }
            else { nnA = 1; newA[0] = NEWBASE; nnB = 2; newB[0] = NEWBASE + 1; newB[1] = NEWBASE + 2; NI = NEWBASE + 3; }
            npool = 0;
        } else {
            rv = -1;
            nnA = 1; newA[0] = NEWBASE; nnB = 1; newB[0] = NEWBASE + 1; NI = NEWBASE + 2;
            int e0 = irand(ne);
            /* BFS from the endpoints of e0 */
            for (int v = 0; v < n0; v++) dist[v] = -1;
            int h = 0, t = 0;
            dist[eu[e0]] = 0; q2[t++] = eu[e0];
            dist[ev[e0]] = 0; q2[t++] = ev[e0];
            while (h < t) { int v = q2[h++]; if (dist[v] >= R) continue; for (int j = 0; j < sdeg[v]; j++) { int u = sadj[v][j]; if (dist[u] < 0) { dist[u] = dist[v] + 1; q2[t++] = u; } } }
            npool = 0;
            for (int e = 0; e < ne && npool < MAXPOOL; e++) if (dist[eu[e]] >= 0 && dist[ev[e]] >= 0) pool[npool++] = e;
            Fi[0] = e0;
            for (int k = 1; k < f; k++) {
                int e;
                /* ensure distinct */
                int ok;
                do { e = pool[irand(npool)]; ok = 1; for (int j = 0; j < k; j++) if (Fi[j] == e) ok = 0; } while (!ok);
                Fi[k] = e;
            }
        }
        build_slots();
        for (int i = 0; i < L; i++) pi_[i] = i;
        for (int i = L - 1; i > 0; i--) { int j = irand(i + 1); int tmp = pi_[i]; pi_[i] = pi_[j]; pi_[j] = tmp; }
        long curE = evaluate();
        long rBest = curE;
        double t0 = now();
        for (int step = 0; step < steps; step++) {
            if ((step & 63) == 0 && now() > deadline) break;
            double T = T0 * pow(T1 / T0, (double)step / steps);
            if (!mode_v && urand() < 0.4) {
                int k = irand(f);
                int e;
                do { e = pool[irand(npool)]; } while (inF(e));
                int old = Fi[k];
                Fi[k] = e; build_slots();
                long nE = evaluate();
                if (nE <= curE || urand() < exp(-(double)(nE - curE) / T)) {
                    curE = nE;
                    if (curE < bestE) { bestE = curE; bestFar = lastFar; bestDup = lastDup; write_graph(outp); }
                } else { Fi[k] = old; build_slots(); }
            } else {
                int i = irand(L), j = irand(L);
                if (i == j) continue;
                int tmp = pi_[i]; pi_[i] = pi_[j]; pi_[j] = tmp;
                long nE = evaluate();
                if (nE <= curE || urand() < exp(-(double)(nE - curE) / T)) {
                    curE = nE;
                    if (curE < bestE) { bestE = curE; bestFar = lastFar; bestDup = lastDup; write_graph(outp); }
                } else { tmp = pi_[i]; pi_[i] = pi_[j]; pi_[j] = tmp; }
            }
            if (curE < rBest) rBest = curE;
        }
        (void)t0;
        printf("restart %d mode=%s f=%d rv=%d pool=%d L=%d restart_best=%ld global_best_far=%ld global_dup=%d\n",
               restarts, mode_v ? "v" : "e", f, rv, npool, L, rBest, bestFar, bestDup);
        fflush(stdout);
        if (bestE == 0) break;
    }
    printf("RESULT best_energy=%ld far=%ld dup=%d restarts=%d n=%d file=%s\n", bestE, bestFar, bestDup, restarts, NP, outp);
    return 0;
}
