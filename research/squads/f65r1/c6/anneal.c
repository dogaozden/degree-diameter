/* c6: simulated annealing with double-edge swaps on 6-regular bipartite graphs, no symmetry.
   cost = number of same-side ordered pairs at distance > 4 (= 0 iff diameter <= 5).
   Evaluation: full bitset recount of radius-4 balls (~0.1-0.2 ms for n ~ 700).
   Usage: anneal plain IN SECONDS SEED OUT [L T0 T1]
          anneal add2  IN SECONDS SEED OUT [L T0 T1 TRIES]   (684 graph -> 686 vertices via matching surgery)  */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 768
#define W 12
#define D 6

static int n, N[MAXN][D], side[MAXN];
static int sidelist[2][MAXN], nside[2];
static unsigned char M[MAXN][MAXN];
static uint64_t R1[MAXN][W], R2[MAXN][W], R3[MAXN][W], R4[MAXN][W], SM[2][W];
static int unc[MAXN], uncOld[MAXN];

static uint64_t rng_s;
static inline uint64_t rnd(void) { rng_s ^= rng_s << 13; rng_s ^= rng_s >> 7; rng_s ^= rng_s << 17; return rng_s; }
static inline double urand(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static void build_masks(void) {
    memset(SM, 0, sizeof SM);
    for (int v = 0; v < n; v++) SM[side[v]][v >> 6] |= 1ULL << (v & 63);
    nside[0] = nside[1] = 0;
    for (int v = 0; v < n; v++) sidelist[side[v]][nside[side[v]]++] = v;
}

/* sum of unc = same-side ordered pairs at distance > 4 */
static long cost(void) {
    for (int v = 0; v < n; v++) {
        memset(R1[v], 0, sizeof R1[v]);
        R1[v][v >> 6] |= 1ULL << (v & 63);
        for (int i = 0; i < D; i++) { int u = N[v][i]; R1[v][u >> 6] |= 1ULL << (u & 63); }
    }
    for (int v = 0; v < n; v++) {
        for (int w = 0; w < W; w++) R2[v][w] = R1[v][w];
        for (int i = 0; i < D; i++) { int u = N[v][i]; for (int w = 0; w < W; w++) R2[v][w] |= R1[u][w]; }
    }
    for (int v = 0; v < n; v++) {
        for (int w = 0; w < W; w++) R3[v][w] = R2[v][w];
        for (int i = 0; i < D; i++) { int u = N[v][i]; for (int w = 0; w < W; w++) R3[v][w] |= R2[u][w]; }
    }
    for (int v = 0; v < n; v++) {
        for (int w = 0; w < W; w++) R4[v][w] = R3[v][w];
        for (int i = 0; i < D; i++) { int u = N[v][i]; for (int w = 0; w < W; w++) R4[v][w] |= R3[u][w]; }
    }
    long tot = 0;
    for (int v = 0; v < n; v++) {
        int s = side[v], c = 0;
        for (int w = 0; w < W; w++) c += __builtin_popcountll(R4[v][w] & SM[s][w]);
        unc[v] = nside[s] - c;
        tot += unc[v];
    }
    return tot;
}

static void repl(int v, int old, int nw) {
    for (int i = 0; i < D; i++) if (N[v][i] == old) { N[v][i] = nw; return; }
    fprintf(stderr, "repl failed\n"); exit(3);
}

/* (a1,b1),(a2,b2) -> (a1,b2),(a2,b1). a's on side 0, b's on side 1. */
static int do_swap(int a1, int b1, int a2, int b2) {
    if (a1 == a2 || b1 == b2) return 0;
    if (M[a1][b2] || M[a2][b1]) return 0;
    M[a1][b1] = M[b1][a1] = 0; M[a2][b2] = M[b2][a2] = 0;
    M[a1][b2] = M[b2][a1] = 1; M[a2][b1] = M[b1][a2] = 1;
    repl(a1, b1, b2); repl(b1, a1, a2); repl(a2, b2, b1); repl(b2, a2, a1);
    return 1;
}

static void clear_graph(void) {
    for (int v = 0; v < n; v++) for (int i = 0; i < D; i++) M[v][N[v][i]] = 0;
}
static void set_graph_from(int NN[MAXN][D]) {
    clear_graph();
    for (int v = 0; v < n; v++) for (int i = 0; i < D; i++) { N[v][i] = NN[v][i]; M[v][N[v][i]] = 1; }
}

static void write_graph(const char *fn, int NN[MAXN][D]) {
    char tmp[1024]; snprintf(tmp, sizeof tmp, "%s.tmp", fn);
    FILE *f = fopen(tmp, "w");
    fprintf(f, "%d\n", n);
    for (int v = 0; v < n; v++) for (int i = 0; i < D; i++) if (NN[v][i] > v) fprintf(f, "%d %d\n", v, NN[v][i]);
    fclose(f); rename(tmp, fn);
}

static int pick_vertex(int s, double pb) {
    if (urand() < pb) for (int t = 0; t < 40; t++) { int v = sidelist[s][rnd() % nside[s]]; if (unc[v] > 0) return v; }
    return sidelist[s][rnd() % nside[s]];
}

static double now(void) { return (double)clock() / CLOCKS_PER_SEC; }

int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage\n"); return 1; }
    const char *mode = argv[1], *inf = argv[2], *out = argv[5];
    double secs = atof(argv[3]);
    rng_s = 0x9E3779B97F4A7C15ULL ^ (strtoull(argv[4], 0, 10) * 0xBF58476D1CE4E5B9ULL + 1);
    long L = argc > 6 ? atol(argv[6]) : 200000;
    double T0 = argc > 7 ? atof(argv[7]) : 1.0, T1 = argc > 8 ? atof(argv[8]) : 0.05;
    int TRIES = argc > 9 ? atoi(argv[9]) : 2000;

    FILE *f = fopen(inf, "r");
    int n0; if (fscanf(f, "%d", &n0) != 1) return 2;
    static int eu[4000], ev[4000]; int m = 0, a, b;
    while (fscanf(f, "%d %d", &a, &b) == 2) { eu[m] = a; ev[m] = b; m++; }
    fclose(f);
    static int adjl[MAXN][D]; int dg[MAXN] = {0};
    for (int i = 0; i < m; i++) { adjl[eu[i]][dg[eu[i]]++] = ev[i]; adjl[ev[i]][dg[ev[i]]++] = eu[i]; }
    /* 2-colour */
    static int col[MAXN]; for (int i = 0; i < n0; i++) col[i] = -1;
    static int q[MAXN]; int h = 0, t = 0; col[0] = 0; q[t++] = 0;
    while (h < t) { int x = q[h++]; for (int i = 0; i < dg[x]; i++) { int y = adjl[x][i]; if (col[y] < 0) { col[y] = 1 - col[x]; q[t++] = y; } } }
    for (int i = 0; i < n0; i++) if (dg[i] != 6) { fprintf(stderr, "not 6-regular at %d\n", i); return 4; }

    if (strcmp(mode, "plain") == 0) {
        n = n0;
        for (int v = 0; v < n; v++) side[v] = col[v];
        for (int v = 0; v < n; v++) for (int i = 0; i < D; i++) N[v][i] = adjl[v][i];
    } else {
        /* add2: remove a 6-matching a_i b_i, add x (side 0) ~ all b_i and y (side 1) ~ all a_i */
        n = n0 + 2;
        for (int v = 0; v < n0; v++) side[v] = col[v];
        side[n0] = 0; side[n0 + 1] = 1;
        for (int v = 0; v < n0; v++) for (int i = 0; i < D; i++) N[v][i] = adjl[v][i];
        build_masks();
        static int best_idx[6], bestEN[MAXN][D];
        long bestc = -1;
        for (int tr = 0; tr < TRIES; tr++) {
            int idx[6], k = 0, ok = 1;
            int used[MAXN] = {0};
            while (k < 6) {
                int e = rnd() % m;
                int u = eu[e], w = ev[e];
                int A = side[u] == 0 ? u : w, B = side[u] == 0 ? w : u;
                if (used[A] || used[B]) continue;
                used[A] = used[B] = 1; idx[k++] = e;
            }
            (void)ok;
            /* build candidate graph */
            static int NN[MAXN][D]; static int dd[MAXN];
            for (int v = 0; v < n0; v++) { dd[v] = 0; for (int i = 0; i < D; i++) NN[v][i] = -1; }
            for (int v = n0; v < n; v++) dd[v] = 0;
            static int rem[4000]; for (int i = 0; i < m; i++) rem[i] = 0;
            for (int j = 0; j < 6; j++) rem[idx[j]] = 1;
            for (int i = 0; i < m; i++) if (!rem[i]) { int u = eu[i], w = ev[i]; NN[u][dd[u]++] = w; NN[w][dd[w]++] = u; }
            for (int j = 0; j < 6; j++) {
                int e = idx[j]; int u = eu[e], w = ev[e];
                int A = side[u] == 0 ? u : w, B = side[u] == 0 ? w : u;
                NN[B][dd[B]++] = n0; NN[n0][dd[n0]++] = B;
                NN[A][dd[A]++] = n0 + 1; NN[n0 + 1][dd[n0 + 1]++] = A;
            }
            set_graph_from(NN);
            long c = cost();
            if (bestc < 0 || c < bestc) {
                bestc = c; memcpy(best_idx, idx, sizeof idx);
                memcpy(bestEN, NN, sizeof NN);
            }
        }
        fprintf(stderr, "add2: best matching start cost %ld over %d tries\n", bestc, TRIES);
        set_graph_from(bestEN);
    }
    build_masks();
    for (int v = 0; v < n; v++) for (int i = 0; i < D; i++) if (M[v][N[v][i]] != 1) { /* sanity */ }

    /* sanity: bipartite */
    for (int v = 0; v < n; v++) for (int i = 0; i < D; i++) if (side[N[v][i]] == side[v]) { fprintf(stderr, "not bipartite\n"); return 5; }

    static int bestN[MAXN][D];
    long cur = cost(), best = cur;
    memcpy(bestN, N, sizeof N);
    fprintf(stderr, "start cost %ld (n=%d)\n", cur, n);
    write_graph(out, bestN);
    double tstart = now();
    int cycle = 0;
    while (now() - tstart < secs && best > 0) {
        cycle++;
        set_graph_from(bestN);
        cur = cost();
        long cyc_best = cur;
        long acc = 0;
        for (long s = 0; s < L && best > 0; s++) {
            double T = T0 * pow(T1 / T0, (double)s / (double)L);
            int s1 = rnd() & 1;
            int v1 = pick_vertex(s1, 0.7);
            int a1, b1, a2, b2;
            if (s1 == 0) { a1 = v1; b1 = N[v1][rnd() % D]; } else { b1 = v1; a1 = N[v1][rnd() % D]; }
            a2 = pick_vertex(0, 0.3);
            b2 = N[a2][rnd() % D];
            if (!do_swap(a1, b1, a2, b2)) continue;
            memcpy(uncOld, unc, sizeof(int) * n);
            long nc = cost();
            long d = nc - cur;
            if (d <= 0 || urand() < exp(-(double)d / T)) {
                cur = nc; acc++;
                if (cur < cyc_best) cyc_best = cur;
                if (cur < best) {
                    best = cur; memcpy(bestN, N, sizeof N);
                    fprintf(stderr, "  new best %ld at cycle %d step %ld T=%.3f t=%.0fs\n", best, cycle, s, T, now() - tstart);
                    if (best == 0) { write_graph(out, bestN); break; }
                }
            } else {
                do_swap(a1, b2, a2, b1); /* undo */
                memcpy(unc, uncOld, sizeof(int) * n);
            }
        }
        fprintf(stderr, "cycle %d done: cycle-best %ld, global best %ld, accept %.3f, t=%.0fs\n",
                cycle, cyc_best, best, (double)acc / L, now() - tstart);
        if (best < cost()) { }
        write_graph(out, bestN);
    }
    set_graph_from(bestN);
    printf("FINAL best %ld n %d cycles %d\n", best, n, cycle);
    write_graph(out, bestN);
    return 0;
}
