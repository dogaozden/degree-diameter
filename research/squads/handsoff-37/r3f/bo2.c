/* bo2.c (r3f): focused breakout tabu over 2-switches for UNSYMMETRIC cubic bipartite graphs, n = 2m.
   Cost = weighted number of violated same-side unordered pairs (distance > 6); raw = unweighted count.
   raw = 0 iff diameter <= 7 (see cards.md common rules). far (score37) >= raw; check with bin/score37.
   Usage: ./bo2 EDGES SECS SEED OUTPREFIX
   env: FR (focus radius, 1), TEN (tabu tenure, 8), WCAP (weight cap, 16), BOWALK (1), SAMPLE (random extra
        2-switch candidates per step, 0), STALL (iterations without raw improvement before a kick, 0 = never),
        PERT (number of random 2-switches in a kick, 6), RESTART (1 = kick restarts from best state).
   Output: OUTPREFIX_best.edges (best raw so far, edge list format "n" then "a b" lines).
   Build: gcc -O3 -march=native -o bo2 bo2.c */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#include <limits.h>

#define MAXN 256
#define MAXE 400
#define MAXW 4
#define MAXV 60000

static int n, NW, NE;
static int adj[MAXN][3];
static int ea[MAXE], eb[MAXE];
static int side[MAXN];
static uint64_t ball[MAXN][MAXW], tmpb[MAXN][MAXW];
static uint64_t sideM[2][MAXW];
static int wt[MAXN][MAXN];
static long tabu[MAXN][MAXN];
static int vu[MAXV], vv[MAXV], nv;
static long long rawc, wcost;
static uint64_t rng = 88172645463325252ULL;
static long iter;
static int WCAP = 16, TEN = 8, FR = 1, BOWALK = 1, SAMPLE = 0, PERT = 6, RESTART = 0;
static long STALL = 0;
static long long DELTA = -1; static long RESTORE = 100;

static inline uint64_t rnd(void) { rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; return rng; }

static void compute_ball(void) {
    for (int v = 0; v < n; v++) {
        for (int w = 0; w < NW; w++) ball[v][w] = 0;
        ball[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < 6; r++) {
        for (int v = 0; v < n; v++) {
            int a = adj[v][0], b = adj[v][1], c = adj[v][2];
            for (int w = 0; w < NW; w++) tmpb[v][w] = ball[v][w] | ball[a][w] | ball[b][w] | ball[c][w];
        }
        for (int v = 0; v < n; v++)
            for (int w = 0; w < NW; w++) ball[v][w] = tmpb[v][w];
    }
}

static void evaluate(void) {
    compute_ball();
    nv = 0; rawc = 0; wcost = 0;
    for (int u = 0; u < n; u++) {
        int s = side[u];
        for (int w = 0; w < NW; w++) {
            uint64_t x = sideM[s][w] & ~ball[u][w];
            while (x) {
                int b = __builtin_ctzll(x); x &= x - 1;
                int v = w * 64 + b;
                if (v > u) { vu[nv] = u; vv[nv] = v; nv++; rawc++; wcost += wt[u][v]; }
            }
        }
    }
}

static int is_edge(int x, int y) { return adj[x][0] == y || adj[x][1] == y || adj[x][2] == y; }
static void repl(int x, int old, int nw) {
    for (int k = 0; k < 3; k++) if (adj[x][k] == old) { adj[x][k] = nw; return; }
    fprintf(stderr, "repl failed\n"); exit(1);
}
/* 2-switch of edges i=(a1,b1), j=(a2,b2) -> i=(a1,b2), j=(a2,b1). Self-inverse. */
static void sw(int i, int j) {
    int a1 = ea[i], b1 = eb[i], a2 = ea[j], b2 = eb[j];
    ea[i] = a1; eb[i] = b2; ea[j] = a2; eb[j] = b1;
    repl(a1, b1, b2); repl(b1, a1, a2); repl(b2, a2, a1); repl(a2, b2, b1);
}

static int read_graph(const char *fn) {
    FILE *f = fopen(fn, "r"); if (!f) { perror(fn); exit(2); }
    if (fscanf(f, "%d", &n) != 1) exit(2);
    int ne = 0; int X[MAXE], Y[MAXE], a, b;
    while (fscanf(f, "%d %d", &a, &b) == 2) { if (ne >= MAXE) { fprintf(stderr, "too many edges\n"); exit(2); } X[ne] = a; Y[ne] = b; ne++; }
    fclose(f);
    int deg[MAXN] = {0};
    for (int e = 0; e < ne; e++) { deg[X[e]]++; deg[Y[e]]++; }
    for (int v = 0; v < n; v++) if (deg[v] != 3) { fprintf(stderr, "vertex %d has degree %d (need cubic)\n", v, deg[v]); exit(2); }
    /* 2-colour by BFS */
    int col[MAXN]; for (int v = 0; v < n; v++) col[v] = -1;
    int q[MAXN], qh = 0, qt = 0; int nb[MAXN][3], nd[MAXN] = {0};
    for (int e = 0; e < ne; e++) { nb[X[e]][nd[X[e]]++] = Y[e]; nb[Y[e]][nd[Y[e]]++] = X[e]; }
    for (int s = 0; s < n; s++) if (col[s] < 0) {
        col[s] = 0; q[qt++] = s;
        while (qh < qt) { int x = q[qh++]; for (int k = 0; k < 3; k++) { int y = nb[x][k];
            if (col[y] < 0) { col[y] = 1 - col[x]; q[qt++] = y; }
            else if (col[y] == col[x]) { fprintf(stderr, "not bipartite\n"); exit(2); } } }
    }
    NE = ne;
    for (int e = 0; e < ne; e++) {
        if (col[X[e]] == 0) { ea[e] = X[e]; eb[e] = Y[e]; } else { ea[e] = Y[e]; eb[e] = X[e]; }
    }
    for (int v = 0; v < n; v++) side[v] = col[v];
    /* adjacency */
    int cnt[MAXN] = {0};
    for (int e = 0; e < ne; e++) { adj[ea[e]][cnt[ea[e]]++] = eb[e]; adj[eb[e]][cnt[eb[e]]++] = ea[e]; }
    for (int e = 0; e < ne; e++) for (int k = 0; k < 3; k++) if (adj[eb[e]][k] == ea[e]) { /* ok */ }
    return ne;
}

static void write_graph(const char *fn) {
    FILE *f = fopen(fn, "w"); if (!f) { perror(fn); return; }
    fprintf(f, "%d\n", n);
    for (int e = 0; e < NE; e++) fprintf(f, "%d %d\n", ea[e], eb[e]);
    fclose(f);
}

static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }

static int inF[MAXN];
static int cand[MAXE];

int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage: bo2 EDGES SECS SEED OUTPREFIX\n"); return 2; }
    double secs = atof(argv[2]);
    rng ^= (uint64_t)atol(argv[3]) * 0x9E3779B97F4A7C15ULL; if (!rng) rng = 1;
    for (int i = 0; i < 10; i++) rnd();
    if (getenv("FR")) FR = atoi(getenv("FR"));
    if (getenv("TEN")) TEN = atoi(getenv("TEN"));
    if (getenv("WCAP")) WCAP = atoi(getenv("WCAP"));
    if (getenv("BOWALK")) BOWALK = atoi(getenv("BOWALK"));
    if (getenv("SAMPLE")) SAMPLE = atoi(getenv("SAMPLE"));
    if (getenv("STALL")) STALL = atol(getenv("STALL"));
    if (getenv("PERT")) PERT = atoi(getenv("PERT"));
    if (getenv("RESTART")) RESTART = atoi(getenv("RESTART"));
    if (getenv("DELTA")) DELTA = atoll(getenv("DELTA"));
    if (getenv("RESTORE")) RESTORE = atol(getenv("RESTORE"));
    read_graph(argv[1]);
    NW = (n + 63) / 64;
    memset(sideM, 0, sizeof sideM);
    for (int v = 0; v < n; v++) sideM[side[v]][v >> 6] |= 1ULL << (v & 63);
    for (int u = 0; u < n; u++) for (int v = 0; v < n; v++) wt[u][v] = 1;
    evaluate();
    long long bestraw = rawc;
    int bestEA[MAXE], bestEB[MAXE];
    memcpy(bestEA, ea, sizeof(int) * NE); memcpy(bestEB, eb, sizeof(int) * NE);
    char fn[512];
    snprintf(fn, sizeof fn, "%s_best.edges", argv[4]); write_graph(fn);
    fprintf(stderr, "start raw %lld (n=%d, NE=%d, FR=%d TEN=%d WCAP=%d BOWALK=%d SAMPLE=%d STALL=%ld PERT=%d RESTART=%d)\n",
            rawc, n, NE, FR, TEN, WCAP, BOWALK, SAMPLE, STALL, PERT, RESTART);

    if (getenv("DIAG")) {
        long hist[12] = {0}; long long mn = 1LL<<40; long cnt = 0; long long sumr = 0;
        int ntry = 0;
        for (int i = 0; i < NE; i++) for (int j = i + 1; j < NE; j++) {
            int a1 = ea[i], b1 = eb[i], a2 = ea[j], b2 = eb[j];
            if (is_edge(a1, b2) || is_edge(a2, b1)) continue;
            sw(i, j); evaluate(); long long cr = rawc; sw(i, j);
            cnt++; sumr += cr; if (cr < mn) mn = cr;
            int bin = cr < 40 ? 0 : cr < 60 ? 1 : cr < 80 ? 2 : cr < 100 ? 3 : cr < 150 ? 4 : cr < 200 ? 5 : cr < 300 ? 6 : cr < 400 ? 7 : cr < 600 ? 8 : 9;
            hist[bin]++;
        }
        fprintf(stderr, "DIAG start raw %lld: %ld valid 2-switches, min raw %lld, mean %.1f\n", rawc, cnt, mn, (double)sumr / cnt);
        const char *lab[10] = {"<40","40-59","60-79","80-99","100-149","150-199","200-299","300-399","400-599",">=600"};
        for (int b = 0; b < 10; b++) fprintf(stderr, "  %s: %ld\n", lab[b], hist[b]);
        (void)ntry; return 0;
    }
    double t0 = now(), tlast = t0;
    long bumps = 0, walks = 0, evals = 0, lastimp = 0; long long candtot = 0;
    long stallcnt = 0; long nobad = 0, restores = 0;
    while (now() - t0 < secs) {
        iter++;
        evaluate(); evals++;
        if (rawc < bestraw) {
            bestraw = rawc; lastimp = iter; stallcnt = 0;
            memcpy(bestEA, ea, sizeof(int) * NE); memcpy(bestEB, eb, sizeof(int) * NE);
            write_graph(fn);
            fprintf(stderr, "[%.1fs it %ld] new best raw %lld (wcost %lld)\n", now() - t0, iter, bestraw, wcost);
        }
        if (rawc == 0) break;
        if (STALL > 0 && iter - lastimp > STALL) {
            /* kick: restart from best (if RESTART) and perturb with random valid 2-switches */
            if (RESTART) { memcpy(ea, bestEA, sizeof(int) * NE); memcpy(eb, bestEB, sizeof(int) * NE);
                for (int v = 0; v < n; v++) adj[v][0] = adj[v][1] = adj[v][2] = -1;
                for (int e = 0; e < NE; e++) { int a = ea[e], b = eb[e];
                    int k = 0; while (adj[a][k] >= 0) k++; adj[a][k] = b;
                    k = 0; while (adj[b][k] >= 0) k++; adj[b][k] = a; } }
            int done = 0;
            while (done < PERT) { int i = rnd() % NE, j = rnd() % NE; if (i == j) continue;
                if (is_edge(ea[i], eb[j]) || is_edge(ea[j], eb[i])) continue; sw(i, j); done++; }
            lastimp = iter;
            continue;
        }
        int p = rnd() % nv;
        int u = vu[p], v = vv[p];
        /* focus set: vertices within distance FR of u or v */
        memset(inF, 0, sizeof(int) * n);
        {
            int fr[MAXN], nf = 0, lev[MAXN];
            int seeds[2] = {u, v};
            for (int s = 0; s < 2; s++) { int x = seeds[s]; if (!inF[x]) { inF[x] = 1; fr[nf] = x; lev[nf] = 0; nf++; } }
            for (int h = 0; h < nf; h++) {
                if (lev[h] >= FR) continue;
                int x = fr[h];
                for (int k = 0; k < 3; k++) { int y = adj[x][k]; if (!inF[y]) { inF[y] = 1; fr[nf] = y; lev[nf] = lev[h] + 1; nf++; } }
            }
        }
        int nc = 0;
        for (int e = 0; e < NE; e++) if (inF[ea[e]] || inF[eb[e]]) cand[nc++] = e;
        int nfocus = nc;
        for (int s = 0; s < SAMPLE; s++) { int e = rnd() % NE; int dup = 0; for (int k = 0; k < nc; k++) if (cand[k] == e) dup = 1; if (!dup) cand[nc++] = e; }
        long long cur_w = wcost;
        long long bestw = LLONG_MAX; int bi = -1, bj = -1, bcnt = 0;
        for (int ii = 0; ii < nc; ii++) for (int jj = ii + 1; jj < nc; jj++) {
            int i = cand[ii], j = cand[jj];
            if (i == j) continue;
            int a1 = ea[i], b1 = eb[i], a2 = ea[j], b2 = eb[j];
            if (side[a1] != 0 || side[a2] != 0) continue; /* should not happen */
            if (is_edge(a1, b2) || is_edge(a2, b1)) continue;
            int istabu = (tabu[a1][b2] > iter) || (tabu[a2][b1] > iter);
            sw(i, j); evaluate(); evals++;
            long long cw = wcost, cr = rawc;
            sw(i, j);
            if (istabu && cr >= bestraw) continue;
            if (DELTA >= 0 && cr > bestraw + DELTA) continue;
            if (cw < bestw) { bestw = cw; bi = i; bj = j; bcnt = 1; }
            else if (cw == bestw) { bcnt++; if (rnd() % bcnt == 0) { bi = i; bj = j; } }
        }
        candtot += nc;
        evaluate(); /* restore current state's violation list */
        if (bi < 0) { /* no admissible move: bump and continue */
            for (int k = 0; k < nv; k++) if (wt[vu[k]][vv[k]] < WCAP) wt[vu[k]][vv[k]]++;
            bumps++; nobad++;
            if (DELTA >= 0 && nobad > RESTORE) { nobad = 0; restores++;
                memcpy(ea, bestEA, sizeof(int) * NE); memcpy(eb, bestEB, sizeof(int) * NE);
                for (int v = 0; v < n; v++) adj[v][0] = adj[v][1] = adj[v][2] = -1;
                for (int e = 0; e < NE; e++) { int a = ea[e], b = eb[e];
                    int k = 0; while (adj[a][k] >= 0) k++; adj[a][k] = b;
                    k = 0; while (adj[b][k] >= 0) k++; adj[b][k] = a; } }
            continue;
        }
        nobad = 0;
        if (bestw < cur_w) {
            int a1 = ea[bi], b1 = eb[bi], a2 = ea[bj], b2 = eb[bj];
            tabu[a1][b1] = iter + TEN; tabu[a2][b2] = iter + TEN;
            sw(bi, bj);
        } else {
            for (int k = 0; k < nv; k++) if (wt[vu[k]][vv[k]] < WCAP) wt[vu[k]][vv[k]]++;
            bumps++;
            if (BOWALK) {
                int a1 = ea[bi], b1 = eb[bi], a2 = ea[bj], b2 = eb[bj];
                tabu[a1][b1] = iter + TEN; tabu[a2][b2] = iter + TEN;
                sw(bi, bj); walks++;
            }
        }
        if (now() - tlast > 10.0) {
            tlast = now();
            fprintf(stderr, "[%.0fs it %ld] raw %lld wcost %lld best %lld bumps %ld walks %ld evals %ld avgcand %.1f\n",
                    now() - t0, iter, rawc, cur_w, bestraw, bumps, walks, evals, (double)candtot / iter);
        }
        (void)nfocus;
    }
    /* final state check */
    evaluate();
    fprintf(stderr, "END it %ld best raw %lld (current raw %lld) bumps %ld walks %ld evals %ld restores %ld\n", iter, bestraw, rawc, bumps, walks, evals, restores);
    printf("%lld\n", bestraw);
    return 0;
}
