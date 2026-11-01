/* ls.c (deep-37, squad r1, card c2): weighted tabu / breakout local search on cubic bipartite graphs, n <= 192.
   Moves: 2-switches (a1b1, a2b2 -> a1b2, a2b1) with a in side 0, b in side 1; they keep the graph cubic,
   bipartite and simple. Cost: sum of weights of unordered pairs at distance > 7 ("far" pairs), exact via a
   7-step bit-parallel ball computation (3 x 64-bit words per vertex).
   Proposals: with FOCUS percent, a random far pair (u,v) is chosen and a new edge p-q is added with p (side 0)
   within distance 3 of u and q (side 1) within distance 3 of v; otherwise uniform random 2-switches.
   Each iteration: K candidates are evaluated, the best non-tabu one is applied; if no candidate improves the
   weighted cost, the far pairs of the current graph get weight +1 (breakout). Restart from the best graph with
   random perturbation after STAG iterations without improving the best far.
   usage: ls IN OUT SECONDS SEED [K=30] [FOCUS=70] [TENURE=12] [STAG=40000] [PERT=10]
   IN: a 168-vertex cubic bipartite graph (one random pair is inserted: two random edges removed, x and y added as
       x = 168 (side 0, adjacent to b1,b2), y = 169 (side 1, adjacent to a1,a2), plus x-y), or a 170-vertex graph.
   OUT: best graph found (edge list, n on the first line). Progress lines go to stdout. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#include <math.h>

#define MAXN 192
#define W 3
#define MAXM 300
#define MAXFAR 20000

static int n, m, side[MAXN];
static int adj[MAXN][3], aid[MAXN][3];
static int EA[MAXM], EB[MAXM];           /* edge i = (EA[i] side 0, EB[i] side 1) */
static int BEA[MAXM], BEB[MAXM];         /* best graph */
static uint64_t mask[W];
static uint64_t R[2][MAXN][W];
static int wt[MAXN][MAXN];
static int tabu_until[MAXN][MAXN];
static int fu[MAXFAR], fv[MAXFAR], nfar;
static uint64_t rs;

static uint64_t rnd(void) {
    rs += 0x9E3779B97F4A7C15ULL; uint64_t z = rs;
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL; z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
    return z ^ (z >> 31);
}
static int rndn(int k) { return (int)(rnd() % (uint64_t)k); }
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }

static void build_adj(void) {
    int dc[MAXN]; memset(dc, 0, sizeof dc);
    for (int i = 0; i < m; i++) {
        int a = EA[i], b = EB[i];
        if (dc[a] >= 3 || dc[b] >= 3) { fprintf(stderr, "degree > 3\n"); exit(1); }
        adj[a][dc[a]] = b; aid[a][dc[a]++] = i;
        adj[b][dc[b]] = a; aid[b][dc[b]++] = i;
    }
    for (int v = 0; v < n; v++) if (dc[v] != 3) { fprintf(stderr, "vertex %d has degree %d\n", v, dc[v]); exit(1); }
}

/* far pairs of the current graph; returns their number, fills fu/fv, sets *wcost = sum of weights */
static int eval(long *wcost) {
    int cur = 0;
    memset(R[0], 0, sizeof R[0]);
    for (int v = 0; v < n; v++) R[0][v][v >> 6] |= 1ULL << (v & 63);
    for (int it = 0; it < 7; it++) {
        int nx = cur ^ 1;
        for (int v = 0; v < n; v++) {
            int a = adj[v][0], b = adj[v][1], c = adj[v][2];
            for (int w = 0; w < W; w++)
                R[nx][v][w] = R[cur][v][w] | R[cur][a][w] | R[cur][b][w] | R[cur][c][w];
        }
        cur = nx;
    }
    nfar = 0; long wc = 0;
    for (int v = 0; v < n; v++)
        for (int w = 0; w < W; w++) {
            uint64_t miss = ~R[cur][v][w] & mask[w];
            while (miss) {
                int u = w * 64 + __builtin_ctzll(miss);
                miss &= miss - 1;
                if (u > v && nfar < MAXFAR) { fu[nfar] = v; fv[nfar] = u; nfar++; wc += wt[v][u]; }
            }
        }
    *wcost = wc;
    return nfar;
}

static int isadj(int a, int b) { return adj[a][0] == b || adj[a][1] == b || adj[a][2] == b; }
static void setnb(int v, int oldnb, int newnb, int id) {
    for (int k = 0; k < 3; k++) if (adj[v][k] == oldnb) { adj[v][k] = newnb; aid[v][k] = id; return; }
    fprintf(stderr, "setnb failed\n"); exit(1);
}
/* 2-switch on edges i = (a1,b1) and j = (a2,b2) -> (a1,b2), (a2,b1). Applying it again to (i,j) undoes it. */
static int do_switch(int i, int j) {
    int a1 = EA[i], b1 = EB[i], a2 = EA[j], b2 = EB[j];
    if (i == j || a1 == a2 || b1 == b2 || isadj(a1, b2) || isadj(a2, b1)) return 0;
    setnb(a1, b1, b2, i); setnb(b2, a2, a1, i); setnb(a2, b2, b1, j); setnb(b1, a1, a2, j);
    EB[i] = b2; EB[j] = b1;
    return 1;
}

/* vertices within distance rad of src (BFS), written to out, returns count */
static int ballv(int src, int rad, int *out) {
    static int d[MAXN], q[MAXN];
    for (int v = 0; v < n; v++) d[v] = -1;
    int h = 0, t = 0; q[t++] = src; d[src] = 0;
    while (h < t) {
        int x = q[h++]; if (d[x] == rad) continue;
        for (int k = 0; k < 3; k++) { int y = adj[x][k]; if (d[y] < 0) { d[y] = d[x] + 1; q[t++] = y; } }
    }
    memcpy(out, q, t * sizeof(int));
    return t;
}

static void propose(int focus, int *oi, int *oj) {
    if (nfar > 0 && rndn(100) < focus) {
        int f = rndn(nfar), u = fu[f], v = fv[f];
        int bu[MAXN], bv[MAXN];
        int nu = ballv(u, 3, bu), nv = ballv(v, 3, bv);
        int P[MAXN], Q[MAXN], np = 0, nq = 0;
        for (int k = 0; k < nu; k++) if (side[bu[k]] == 0) P[np++] = bu[k];
        for (int k = 0; k < nv; k++) if (side[bv[k]] == 1) Q[nq++] = bv[k];
        if (!np || !nq) { *oi = rndn(m); *oj = rndn(m); return; }
        int p = P[rndn(np)], q = Q[rndn(nq)];
        *oi = aid[p][rndn(3)]; *oj = aid[q][rndn(3)];
        return;
    }
    *oi = rndn(m); *oj = rndn(m);
}

static void save(const char *fn) {
    FILE *f = fopen(fn, "w"); if (!f) { perror(fn); exit(1); }
    fprintf(f, "%d\n", n);
    for (int i = 0; i < m; i++) fprintf(f, "%d %d\n", EA[i], EB[i]);
    fclose(f);
}

int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage: ls IN OUT SECONDS SEED [K FOCUS TENURE STAG PERT]\n"); return 2; }
    int K = argc > 5 ? atoi(argv[5]) : 30, FOCUS = argc > 6 ? atoi(argv[6]) : 70;
    int TEN = argc > 7 ? atoi(argv[7]) : 12, STAG = argc > 8 ? atoi(argv[8]) : 40000;
    int PERT = argc > 9 ? atoi(argv[9]) : 10;
    int MODE = argc > 10 ? atoi(argv[10]) : 0;   /* 0 tabu walk, 1 breakout only, 2 annealing */
    double T0 = argc > 11 ? atof(argv[11]) : 1.5, T1 = argc > 12 ? atof(argv[12]) : 0.15;
    long RUNLEN = argc > 13 ? atol(argv[13]) : 2000000;
    double secs = atof(argv[3]);
    rs = (uint64_t)atoll(argv[4]) * 7919ULL + 12345ULL;

    FILE *f = fopen(argv[1], "r"); if (!f) { perror(argv[1]); return 2; }
    int n0; if (fscanf(f, "%d", &n0) != 1) return 2;
    int A[MAXM], B[MAXM], m0 = 0, a, b;
    while (fscanf(f, "%d %d", &a, &b) == 2) { A[m0] = a; B[m0] = b; m0++; }
    fclose(f);
    /* 2-colour */
    int col[MAXN]; for (int i = 0; i < n0; i++) col[i] = -1;
    col[0] = 0;
    for (int it = 0; it < n0; it++) for (int i = 0; i < m0; i++) {
        if (col[A[i]] >= 0 && col[B[i]] < 0) col[B[i]] = 1 - col[A[i]];
        if (col[B[i]] >= 0 && col[A[i]] < 0) col[A[i]] = 1 - col[B[i]];
    }
    for (int v = 0; v < n0; v++) side[v] = col[v];
    if (n0 == 168) {
        /* insert a random pair: remove two random edges (distinct endpoints), add x=168, y=169 */
        int e1, e2;
        do { e1 = rndn(m0); e2 = rndn(m0); } while (e1 == e2);
        int a1 = side[A[e1]] == 0 ? A[e1] : B[e1], b1 = side[A[e1]] == 0 ? B[e1] : A[e1];
        int a2 = side[A[e2]] == 0 ? A[e2] : B[e2], b2 = side[A[e2]] == 0 ? B[e2] : A[e2];
        if (a1 == a2 || b1 == b2) { fprintf(stderr, "unlucky pair, rerun with other seed\n"); return 1; }
        n = 170; m = 0;
        for (int i = 0; i < m0; i++) {
            if (i == e1 || i == e2) continue;
            EA[m] = side[A[i]] == 0 ? A[i] : B[i]; EB[m] = side[A[i]] == 0 ? B[i] : A[i]; m++;
        }
        side[168] = 0; side[169] = 1;
        EA[m] = 168; EB[m] = b1; m++;
        EA[m] = 168; EB[m] = b2; m++;
        EA[m] = 168; EB[m] = 169; m++;
        EA[m] = a1; EB[m] = 169; m++;
        EA[m] = a2; EB[m] = 169; m++;
    } else {
        n = n0; m = m0;
        for (int i = 0; i < m; i++) {
            if (side[A[i]] == 0) { EA[i] = A[i]; EB[i] = B[i]; } else { EA[i] = B[i]; EB[i] = A[i]; }
        }
    }
    for (int v = 0; v < n; v++) { mask[v >> 6] |= 1ULL << (v & 63); }
    build_adj();
    for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) wt[i][j] = 1;

    long wc; int far = eval(&wc);
    int bestfar = far;
    memcpy(BEA, EA, sizeof EA); memcpy(BEB, EB, sizeof EB);
    printf("start far=%d\n", far);
    double t0 = now(), tlast = t0;
    long it = 0, lastimp = 0, nbump = 0, nrestart = 0;
    int bestsaved = 0;

    if (MODE == 2) {
        /* simulated annealing on the unweighted far count, focused 2-switch proposals, geometric cooling runs */
        long runstart = 0; double T = T0;
        far = eval(&wc);
        while (1) {
            it++;
            if ((it & 4095) == 0) { double t = now(); if (t - t0 > secs) break;
                if (t - tlast > 30) { tlast = t; printf("t=%.0f it=%ld best=%d cur=%d T=%.3f\n", t - t0, it, bestfar, far, T); fflush(stdout); } }
            long frac_it = it - runstart;
            if (frac_it >= RUNLEN) { runstart = it; frac_it = 0; memcpy(EA, BEA, sizeof EA); memcpy(EB, BEB, sizeof EB); build_adj(); far = eval(&wc); }
            T = T0 * pow(T1 / T0, (double)frac_it / RUNLEN);
            int i, j; propose(FOCUS, &i, &j);
            if (i == j) continue;
            int a1 = EA[i], b1 = EB[i], a2 = EA[j], b2 = EB[j];
            if (!do_switch(i, j)) continue;
            long c2; int f2 = eval(&c2);
            int d = f2 - far;
            if (d <= 0 || (double)(rnd() >> 11) / 9007199254740992.0 < exp(-d / T)) {
                far = f2;
                if (far < bestfar) {
                    bestfar = far; lastimp = it;
                    memcpy(BEA, EA, sizeof EA); memcpy(BEB, EB, sizeof EB); bestsaved = 1;
                    printf("NEW far=%d it=%ld t=%.1f T=%.3f\n", far, it, now() - t0, T); fflush(stdout);
                    save(argv[2]);
                    if (far == 0) break;
                }
            } else {
                do_switch(i, j);
            }
            (void)a1; (void)b1; (void)a2; (void)b2;
        }
        if (!bestsaved) save(argv[2]);
        printf("DONE best=%d it=%ld t=%.1f\n", bestfar, it, now() - t0);
        return 0;
    }
    while (1) {
        it++;
        if ((it & 255) == 0) { double t = now(); if (t - t0 > secs) break; if (t - tlast > 30) { tlast = t; printf("t=%.0f it=%ld best=%d cur=%d restarts=%ld\n", t - t0, it, bestfar, far, nrestart); fflush(stdout);} }
        if (it - lastimp > STAG) {
            /* restart from the best graph with a random perturbation, forget the weights */
            memcpy(EA, BEA, sizeof EA); memcpy(EB, BEB, sizeof EB); build_adj();
            for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) { wt[i][j] = 1; tabu_until[i][j] = 0; }
            int done = 0; while (done < PERT) { if (do_switch(rndn(m), rndn(m))) done++; }
            lastimp = it; nrestart++;
        }
        far = eval(&wc);
        long curw = wc;
        if (far == 0) break;
        int bi = -1, bj = -1; long bestc = -1; int bestf = 1 << 30; int nties = 0;
        for (int k = 0; k < K; k++) {
            int i, j; propose(FOCUS, &i, &j);
            if (i == j) continue;
            int a1 = EA[i], b1 = EB[i], a2 = EA[j], b2 = EB[j];
            int tb = tabu_until[a1][b2] > it || tabu_until[a2][b1] > it;
            if (!do_switch(i, j)) continue;
            long c2; int f2 = eval(&c2);
            do_switch(i, j); /* undo */
            if (tb && f2 >= bestfar) continue;
            if (bestc < 0 || c2 < bestc) { bestc = c2; bi = i; bj = j; bestf = f2; nties = 1; }
            else if (c2 == bestc) { nties++; if (rndn(nties) == 0) { bi = i; bj = j; bestf = f2; } }
        }
        if (bi < 0) continue;
        if (MODE == 1 && bestc >= curw) {
            far = eval(&wc);
            for (int q = 0; q < nfar; q++) wt[fu[q]][fv[q]]++;
            nbump++; continue;
        }
        if (bestc >= curw) {
            /* local minimum for the weights: breakout */
            far = eval(&wc);
            for (int q = 0; q < nfar; q++) wt[fu[q]][fv[q]]++;
            nbump++;
        }
        int a1 = EA[bi], b1 = EB[bi], a2 = EA[bj], b2 = EB[bj];
        do_switch(bi, bj);
        tabu_until[a1][b1] = (int)(it + TEN + rndn(TEN));
        tabu_until[a2][b2] = (int)(it + TEN + rndn(TEN));
        far = bestf;
        if (far < bestfar) {
            bestfar = far; lastimp = it;
            memcpy(BEA, EA, sizeof EA); memcpy(BEB, EB, sizeof EB);
            bestsaved = 1;
            printf("NEW far=%d it=%ld t=%.1f restarts=%ld\n", far, it, now() - t0, nrestart); fflush(stdout);
            save(argv[2]);
        }
    }
    if (!bestsaved) save(argv[2]);
    printf("DONE best=%d it=%ld bumps=%ld restarts=%ld t=%.1f\n", bestfar, it, nbump, nrestart, now() - t0);
    return 0;
}
