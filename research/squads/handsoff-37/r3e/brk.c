/* r3e/brk.c: breakout tabu over 2-switches, focused on far pairs, for an UNSYMMETRIC cubic bipartite graph.
   usage: brk START.edges SEED SECS TAG [PERT]
   env: FR1 (radius of edges around the first far endpoint, default 1), FR2 (around the second, default 1),
        TEN (tabu tenure, 4), WCAP (weight cap, 16), BOWALK (1), NRAND (random extra 2-switches per step, 0),
        PRINT (progress every this many seconds, 10).
   Cost: weighted far, sum over unordered pairs {x,y} with dist > 7 of W[x][y]; W starts at 1 and grows by 1 on
   every far pair at a local minimum (breakout). Real far is tracked separately (score37 definition).
   Build: gcc -O3 -march=native -o brk brk.c */
#include "g37.h"
#include <time.h>

static int n;
static int side[MAXN];
static int W[MAXN][MAXN];
static long TA[MAXN][MAXN], TD[MAXN][MAXN];
static int ES[MAXN][MAXN];
static int estamp = 0;
static int bmark[MAXN], bstamp = 0;
static int FR1 = 1, FR2 = 1, TEN = 4, WCAP = 16, BOWALK = 1, NRAND = 0, FULL = 0;
static G g;
static u64 wmask[WMAX];
static int FLX[40000], FLY[40000];
static int nfl = 0;

typedef struct { int a1, b1, a2, b2; } Mv;  /* remove (a1,b1),(a2,b2); add (a1,b2),(a2,b1); a = side 0, b = side 1 */

static void mv_apply(Mv m) { g_del(&g, m.a1, m.b1); g_del(&g, m.a2, m.b2); g_add(&g, m.a1, m.b2); g_add(&g, m.a2, m.b1); }
static void mv_revert(Mv m) { g_del(&g, m.a1, m.b2); g_del(&g, m.a2, m.b1); g_add(&g, m.a1, m.b1); g_add(&g, m.a2, m.b2); }
static int mv_ok(int a1, int b1, int a2, int b2) {
    return a1 != a2 && b1 != b2 && !g_has(&g, a1, b2) && !g_has(&g, a2, b1);
}

/* far count (unordered pairs at distance > 7), weighted cost, and (if want_list) the far pairs into FLX/FLY.
   Fixed 3-word bitsets (n <= 192). */
static u64 Q[2][MAXN][3];
static long evalg(long long *cwout, int want_list) {
    int cur = 0;
    for (int x = 0; x < n; x++) { Q[0][x][0] = Q[0][x][1] = Q[0][x][2] = 0; Q[0][x][x >> 6] |= 1ULL << (x & 63); }
    for (int s = 0; s < 7; s++) {
        int nx = cur ^ 1;
        for (int x = 0; x < n; x++) {
            u64 a0 = Q[cur][x][0], a1 = Q[cur][x][1], a2 = Q[cur][x][2];
            int d = g.deg[x];
            for (int i = 0; i < d; i++) { int y = g.nb[x][i]; a0 |= Q[cur][y][0]; a1 |= Q[cur][y][1]; a2 |= Q[cur][y][2]; }
            Q[nx][x][0] = a0; Q[nx][x][1] = a1; Q[nx][x][2] = a2;
        }
        cur = nx;
    }
    long far = 0; long long cw = 0; if (want_list) nfl = 0;
    for (int x = 0; x < n; x++) for (int w = (x >> 6); w < 3; w++) {
        int lo = w * 64;
        if (lo >= n) break;
        u64 u = ~Q[cur][x][w] & wmask[w];
        if (x >= lo) u &= ~((2ULL << (x - lo)) - 1);
        while (u) {
            int b = __builtin_ctzll(u); u &= u - 1; int y = lo + b;
            far++; cw += W[x][y];
            if (want_list) { FLX[nfl] = x; FLY[nfl] = y; nfl++; }
        }
    }
    *cwout = cw; return far;
}

/* edges with an endpoint within distance R of u, as canonical (a in side 0, b in side 1) */
static int near_edges(int u, int R, int *ea, int *eb) {
    int ball[MAXN], bd[MAXN], nb = 0, qh = 0;
    bstamp++;
    ball[nb] = u; bd[nb] = 0; nb++; bmark[u] = bstamp;
    while (qh < nb) {
        int x = ball[qh], d = bd[qh]; qh++;
        if (d >= R) continue;
        for (int i = 0; i < g.deg[x]; i++) { int y = g.nb[x][i]; if (bmark[y] != bstamp) { bmark[y] = bstamp; ball[nb] = y; bd[nb] = d + 1; nb++; } }
    }
    estamp++; int c = 0;
    for (int k = 0; k < nb; k++) {
        int x = ball[k];
        for (int i = 0; i < g.deg[x]; i++) {
            int y = g.nb[x][i];
            int a = side[x] == 0 ? x : y, b = side[x] == 0 ? y : x;
            if (ES[a][b] != estamp) { ES[a][b] = estamp; ea[c] = a; eb[c] = b; c++; }
        }
    }
    return c;
}

static long bestF_c_dbg(int bi) { (void)bi; return -1; }
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }

static void save(const char *fn) { g_write(&g, fn); }

int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage: brk START.edges SEED SECS TAG [PERT]\n"); return 2; }
    int seed = atoi(argv[2]); double secs = atof(argv[3]); const char *tag = argv[4];
    int pert = argc > 5 ? atoi(argv[5]) : 0;
    if (getenv("FR1")) FR1 = atoi(getenv("FR1"));
    if (getenv("FR2")) FR2 = atoi(getenv("FR2"));
    if (getenv("TEN")) TEN = atoi(getenv("TEN"));
    if (getenv("WCAP")) WCAP = atoi(getenv("WCAP"));
    if (getenv("BOWALK")) BOWALK = atoi(getenv("BOWALK"));
    if (getenv("NRAND")) NRAND = atoi(getenv("NRAND"));
    if (getenv("FULL")) FULL = atoi(getenv("FULL"));
    double printgap = getenv("PRINT") ? atof(getenv("PRINT")) : 10.0;
    if (g_load(&g, argv[1]) < 0) { fprintf(stderr, "load failed\n"); return 2; }
    n = g.n;
    for (int x = 0; x < n; x++) if (g.deg[x] != 3) { fprintf(stderr, "not cubic at %d\n", x); return 2; }
    for (int x = 0; x < n; x++) side[x] = -1;
    { int q[MAXN], h = 0, t = 0; side[0] = 0; q[t++] = 0;
      while (h < t) { int x = q[h++]; for (int i = 0; i < 3; i++) { int y = g.nb[x][i]; if (side[y] < 0) { side[y] = 1 - side[x]; q[t++] = y; } else if (side[y] == side[x]) { fprintf(stderr, "not bipartite\n"); return 2; } } } }
    int Wn = (n + 63) / 64;
    for (int w = 0; w < Wn; w++) wmask[w] = (64 * (w + 1) <= n) ? ~0ULL : ((1ULL << (n - 64 * w)) - 1);
    for (int x = 0; x < n; x++) for (int y = 0; y < n; y++) W[x][y] = 1;
    for (int x = 0; x < n; x++) for (int y = 0; y < n; y++) { TA[x][y] = 0; TD[x][y] = 0; }
    rng_seed(seed);
    /* perturbation: random valid 2-switches */
    int done = 0;
    while (done < pert) {
        int a1 = rng_int(n), a2 = rng_int(n);
        if (side[a1] != 0 || side[a2] != 0 || g.deg[a1] == 0) continue;
        int b1 = g.nb[a1][rng_int(3)], b2 = g.nb[a2][rng_int(3)];
        if (!mv_ok(a1, b1, a2, b2)) continue;
        Mv m = {a1, b1, a2, b2}; mv_apply(m); done++;
    }
    if (getenv("WIN")) {   /* restore breakout weights: lines "x y w" */
        FILE *wf = fopen(getenv("WIN"), "r");
        if (wf) { int x, y, w; while (fscanf(wf, "%d %d %d", &x, &y, &w) == 3) W[x][y] = w; fclose(wf); }
    }
    long long cw; long F = evalg(&cw, 1);
    long bestF = F; char fn[512];
    snprintf(fn, sizeof fn, "out/%s_best.edges", tag); save(fn);
    fprintf(stderr, "start n=%d far=%ld (pert %d) seed %d FR1 %d FR2 %d TEN %d WCAP %d BOWALK %d NRAND %d\n", n, F, pert, seed, FR1, FR2, TEN, WCAP, BOWALK, NRAND);
    double t0 = now(), tlast = t0; long step = 0, bumps = 0, impr = 0;
    static int EAa[400], EAb[400], EBa[400], EBb[400];
    static Mv cand[40000];
    while (now() - t0 < secs) {
        if (F == 0) { snprintf(fn, sizeof fn, "out/%s_far0.edges", tag); save(fn); fprintf(stderr, "FAR 0 at step %ld\n", step); break; }
        step++;
        int r = rng_int(nfl); int fx = FLX[r], fy = FLY[r];
        int c1, c2;
        if (FULL) {   /* all edges as both lists: every pair of distinct edges is a candidate */
            c1 = 0;
            for (int a = 0; a < n; a++) if (side[a] == 0) for (int i = 0; i < 3; i++) { EAa[c1] = a; EAb[c1] = g.nb[a][i]; c1++; }
            c2 = c1; for (int i = 0; i < c1; i++) { EBa[i] = EAa[i]; EBb[i] = EAb[i]; }
        } else {
            c1 = near_edges(fx, FR1, EAa, EAb);
            c2 = near_edges(fy, FR2, EBa, EBb);
        }
        int nc = 0;
        for (int i = 0; i < c1; i++) for (int j = FULL ? i + 1 : 0; j < c2; j++) {
            int a1 = EAa[i], b1 = EAb[i], a2 = EBa[j], b2 = EBb[j];
            if ((a1 == a2 && b1 == b2)) continue;
            if (!mv_ok(a1, b1, a2, b2)) continue;
            cand[nc].a1 = a1; cand[nc].b1 = b1; cand[nc].a2 = a2; cand[nc].b2 = b2; nc++;
            if (nc >= 39990) break;
        }
        for (int k = 0; k < NRAND; k++) {
            int a1 = rng_int(n), a2 = rng_int(n);
            if (side[a1] != 0 || side[a2] != 0) continue;
            int b1 = g.nb[a1][rng_int(3)], b2 = g.nb[a2][rng_int(3)];
            if (!mv_ok(a1, b1, a2, b2)) continue;
            cand[nc].a1 = a1; cand[nc].b1 = b1; cand[nc].a2 = a2; cand[nc].b2 = b2; nc++;
        }
        /* evaluate */
        long long bestcw = -1; int bi = -1, nties = 0;
        for (int k = 0; k < nc; k++) {
            Mv m = cand[k];
            int tabu = (TD[m.a1][m.b1] > step) || (TD[m.a2][m.b2] > step) || (TA[m.a1][m.b2] > step) || (TA[m.a2][m.b1] > step);
            mv_apply(m); long long c2w; long Fk = evalg(&c2w, 0); mv_revert(m);
            if (tabu && !(Fk < bestF)) continue;
            if (bi < 0 || c2w < bestcw) { bestcw = c2w; bi = k; nties = 1; }
            else if (c2w == bestcw) { nties++; if (rng_int(nties) == 0) { bi = k; } }
        }
        if (bi < 0) continue;
        if (getenv("DBG") && step <= atol(getenv("DBG"))) {
            int hist[8] = {0}; long long mn = 1LL<<60; long mnf = 1L<<30;
            for (int k = 0; k < nc; k++) { Mv m = cand[k]; mv_apply(m); long long c2w; long Fk = evalg(&c2w, 0); mv_revert(m); if (Fk < mnf) mnf = Fk; if (c2w < mn) mn = c2w; }
            fprintf(stderr, "DBG step %ld cur far %ld nfl %d focus (%d,%d) nc %d bestcand_cw %lld cur_cw_w %lld minfar_cand %ld chosen far %ld\n", step, F, nfl, fx, fy, nc, bestcw, (long long)0, mnf, bestF_c_dbg(bi));
        }
        /* current weighted cost (weights as now) */
        long long cwcur = 0; for (int k = 0; k < nfl; k++) cwcur += W[FLX[k]][FLY[k]];
        if (bestcw >= cwcur) {
            /* local minimum of the weighted cost: breakout bump on every far pair */
            for (int k = 0; k < nfl; k++) { int x = FLX[k], y = FLY[k]; if (W[x][y] < WCAP) W[x][y]++; }
            bumps++;
            if (!BOWALK) { /* stay */ goto progress; }
        }
        {
            Mv m = cand[bi];
            mv_apply(m);
            TA[m.a1][m.b1] = step + TEN; TA[m.a2][m.b2] = step + TEN;
            TD[m.a1][m.b2] = step + TEN; TD[m.a2][m.b1] = step + TEN;
            F = evalg(&cw, 1);
            if (F < bestF) {
                bestF = F; impr++;
                snprintf(fn, sizeof fn, "out/%s_best.edges", tag); save(fn);
                fprintf(stderr, "  new best far %ld at step %ld t=%.1f\n", bestF, step, now() - t0);
            }
        }
    progress:
        if (now() - tlast >= printgap) {
            tlast = now();
            long long cwc = 0; for (int k = 0; k < nfl; k++) cwc += W[FLX[k]][FLY[k]];
            fprintf(stderr, "t=%.0f step=%ld far=%ld cw=%lld best=%ld bumps=%ld cand=%d\n", now() - t0, step, F, cwc, bestF, bumps, nc);
        }
    }
    snprintf(fn, sizeof fn, "out/%s_cur.edges", tag); save(fn);
    { snprintf(fn, sizeof fn, "out/%s_w.txt", tag); FILE *wf = fopen(fn, "w");
      if (wf) { for (int x = 0; x < n; x++) for (int y = x + 1; y < n; y++) if (W[x][y] != 1) fprintf(wf, "%d %d %d\n", x, y, W[x][y]); fclose(wf); } }
    printf("RESULT tag=%s n=%d best_far=%ld final_far=%ld steps=%ld bumps=%ld improvements=%ld\n", tag, n, bestF, F, step, bumps, impr);
    return 0;
}
