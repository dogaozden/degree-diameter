/* b05: insertion triples on the valid 2,184 seed (Haar graph Z_91 x| Z_12, S of order 4).
   Triple = 3 seed edges (a_i,b_i), a_i in side A, b_i in side B, all a distinct, all b distinct.
   New graph: delete the 3 edges, x = 2184 (side A) ~ b1,b2,b3 and y = 2185 (side B) ~ a1,a2,a3 and x.
   far = unordered pairs at distance > 8 (exact, bitset ball of radius 8 from every vertex).
   Usage:
     triples sample COUNT RNGSEED   -> one line per random triple: far e1 e2 e3 c1 c2 c3 seed-distance features
     triples eval < list            -> reads "e1 e2 e3" lines, prints far
   cls file: classes.txt (first line n, then "u v class" per seed edge). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#define N0 2184
#define NN 2186
#define W 35
#define NE 4368
#define RAD 8
static int adj0[NN][4], deg0[NN];
static int eu[NE], ev[NE], ecls[NE];
static unsigned char dist0[N0][N0];
static uint64_t BA[NN][W], BB[NN][W];
static int adj[NN][4];

static uint64_t rs;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }

static void seed_apsp(void) {
    static int q[N0];
    for (int s = 0; s < N0; s++) {
        for (int v = 0; v < N0; v++) dist0[s][v] = 255;
        int h = 0, t = 0; q[t++] = s; dist0[s][s] = 0;
        while (h < t) { int v = q[h++];
            for (int k = 0; k < deg0[v]; k++) { int u = adj0[v][k];
                if (dist0[s][u] == 255) { dist0[s][u] = dist0[s][v] + 1; q[t++] = u; } } }
    }
}

/* far pairs of the graph in adj (NN vertices, 4-regular) */
static long far_count(void) {
    uint64_t (*P)[W] = BA, (*Q)[W] = BB;
    memset(P, 0, sizeof(BA));
    for (int v = 0; v < NN; v++) P[v][v >> 6] |= 1ULL << (v & 63);
    for (int step = 0; step < RAD; step++) {
        for (int v = 0; v < NN; v++) {
            for (int k = 0; k < W; k++) Q[v][k] = P[v][k];
            for (int e = 0; e < 4; e++) { int u = adj[v][e];
                for (int k = 0; k < W; k++) Q[v][k] |= P[u][k]; }
        }
        uint64_t (*T)[W] = P; P = Q; Q = T;
    }
    long cnt = 0;
    for (int v = 0; v < NN; v++) {
        int c = 0;
        for (int k = 0; k < W; k++) c += __builtin_popcountll(P[v][k]);
        cnt += NN - c;
    }
    return cnt / 2;
}

/* build adj for triple (e[0..2]); returns 0 if invalid (shared endpoints) */
static int build(const int *e) {
    int a[3], b[3];
    for (int i = 0; i < 3; i++) { a[i] = eu[e[i]]; b[i] = ev[e[i]]; }
    for (int i = 0; i < 3; i++) for (int j = i + 1; j < 3; j++) {
        if (e[i] == e[j] || a[i] == a[j] || b[i] == b[j]) return 0; }
    memcpy(adj, adj0, sizeof(adj0));
    int x = N0, y = N0 + 1;
    for (int i = 0; i < 3; i++) {
        for (int k = 0; k < 4; k++) if (adj[a[i]][k] == b[i]) { adj[a[i]][k] = y; break; }
        for (int k = 0; k < 4; k++) if (adj[b[i]][k] == a[i]) { adj[b[i]][k] = x; break; }
    }
    adj[x][0] = b[0]; adj[x][1] = b[1]; adj[x][2] = b[2]; adj[x][3] = y;
    adj[y][0] = a[0]; adj[y][1] = a[1]; adj[y][2] = a[2]; adj[y][3] = x;
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 2) { fprintf(stderr, "usage\n"); return 2; }
    FILE *f = fopen("/home/user/degree-diameter/research/squads/b48/r2/b05/classes.txt", "r");
    int n; if (fscanf(f, "%d", &n) != 1 || n != N0) return 1;
    for (int i = 0; i < NE; i++) {
        if (fscanf(f, "%d %d %d", &eu[i], &ev[i], &ecls[i]) != 3) return 1;
        adj0[eu[i]][deg0[eu[i]]++] = ev[i];
        adj0[ev[i]][deg0[ev[i]]++] = eu[i];
    }
    fclose(f);
    seed_apsp();
    if (!strcmp(argv[1], "sample")) {
        long cnt = atol(argv[2]); rs = 88172645463325252ULL ^ (uint64_t)atol(argv[3]) * 2654435761ULL;
        for (long t = 0; t < cnt; t++) {
            int e[3];
            do { for (int i = 0; i < 3; i++) e[i] = rnd() % NE;
            } while (!build(e));
            long far = far_count();
            int a[3], b[3];
            for (int i = 0; i < 3; i++) { a[i] = eu[e[i]]; b[i] = ev[e[i]]; }
            printf("%ld %d %d %d %d %d %d", far, e[0], e[1], e[2], ecls[e[0]], ecls[e[1]], ecls[e[2]]);
            for (int i = 0; i < 3; i++) for (int j = i + 1; j < 3; j++) printf(" %d", dist0[a[i]][a[j]]);
            for (int i = 0; i < 3; i++) for (int j = i + 1; j < 3; j++) printf(" %d", dist0[b[i]][b[j]]);
            for (int i = 0; i < 3; i++) for (int j = 0; j < 3; j++) if (i != j) printf(" %d", dist0[a[i]][b[j]]);
            printf("\n");
        }
    } else if (!strcmp(argv[1], "anneal")) {
        /* anneal ITER RNGSEED T0 T1 POOL : POOL 0 = any edge, 1 = classes 260/879 only */
        long iters = atol(argv[2]); rs = 88172645463325252ULL ^ (uint64_t)atol(argv[3]) * 2654435761ULL;
        double T0 = atof(argv[4]), T1 = atof(argv[5]); int pool = atoi(argv[6]);
        static int cand[NE]; int nc = 0;
        for (int i = 0; i < NE; i++) if (!pool || ecls[i] == 260 || ecls[i] == 879) cand[nc++] = i;
        int e[3], ok = 0;
        do { for (int i = 0; i < 3; i++) e[i] = cand[rnd() % nc]; ok = build(e); } while (!ok);
        long cur = far_count(), best = cur; int be[3] = {e[0], e[1], e[2]};
        for (long t = 0; t < iters; t++) {
            double T = T0 * pow(T1 / T0, (double)t / iters);
            int ne2[3] = {e[0], e[1], e[2]};
            ne2[rnd() % 3] = cand[rnd() % nc];
            if (!build(ne2)) continue;
            long f = far_count();
            if (f <= cur || (double)(rnd() % 1000000) / 1e6 < exp(-(f - cur) / T)) {
                cur = f; e[0] = ne2[0]; e[1] = ne2[1]; e[2] = ne2[2];
                if (cur < best) { best = cur; be[0] = e[0]; be[1] = e[1]; be[2] = e[2]; }
            }
        }
        printf("BEST %ld %d %d %d classes %d %d %d\n", best, be[0], be[1], be[2], ecls[be[0]], ecls[be[1]], ecls[be[2]]);
    } else if (!strcmp(argv[1], "scan")) {
        /* scan 3 1 2 ... : for a triple, all single-edge replacements; prints min far and histogram of low values */
        int e[3] = {atoi(argv[2]), atoi(argv[3]), atoi(argv[4])};
        long base = 0; if (build(e)) base = far_count();
        long mn = 1 << 30; int cntlow = 0, bestj = -1, besti = -1;
        for (int i = 0; i < 3; i++) for (int j = 0; j < NE; j++) {
            int f2[3] = {e[0], e[1], e[2]}; f2[i] = j;
            if (!build(f2)) continue;
            long f = far_count();
            if (f < mn) { mn = f; bestj = j; besti = i; }
            if (f < base) cntlow++;
        }
        printf("BASE %ld MIN %ld at slot %d edge %d (class %d) ; replacements below base: %d\n", base, mn, besti, bestj, bestj >= 0 ? ecls[bestj] : -1, cntlow);
    } else if (!strcmp(argv[1], "eval")) {
        int e[3];
        while (scanf("%d %d %d", &e[0], &e[1], &e[2]) == 3) {
            if (!build(e)) printf("-1\n"); else printf("%ld\n", far_count());
        }
    }
    return 0;
}
