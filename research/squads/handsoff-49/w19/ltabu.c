/* ltabu (w19): full-neighbourhood tabu search, built from lann.c. lann: annealer for voltage lifts of a bipartite base multigraph over a group table, with optional base 2-switches (w19).
   Lift convention (flift/wl2): base edge (u,v,g) gives lift edges (u,x) ~ (v, g*x); K acts on the right and transitively
   on each fibre, so cost = sum over base vertices u of #lift vertices at distance > D from (u,e) (= ordered far pairs / |K|).
   Cost 0 <=> diameter <= D.  Lift vertex id = u*N + x, n_lift = b*N.
   Usage: lann TABLE.bin BASE.txt D seconds seed OUT
     TABLE.bin: int32 N then N*N uint16 (row g: g*h, identity index 0).
     BASE.txt : "b m" then m lines "u v g" (g = voltage index; a bipartite base, sides 0..b/2-1 and b/2..b-1).
   Env: T0 (2.0) T1 (0.05) CYC (evaluations per cooling cycle, 300000) MV2 (probability of a base 2-switch, 0)
        FIXBASE (1: no base moves) QUIET.
   Writes OUT.best.txt (base with voltages) on every improvement of the best cost, and OUT.best.edges (lift) at the
   end; on cost 0 writes OUT.edges and prints RESULT FOUND. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>

#define MAXB 256
#define MAXM 1024
#define MAXDEG 16
#define MAXV (MAXB * 1024)

static int N, b, m, D;
static uint16_t *MT; static int *INV;
static int eu[MAXM], ev[MAXM], eg[MAXM];
static int dcnt[MAXB], dto[MAXB][MAXDEG], dg[MAXB][MAXDEG];
static uint32_t *stamp; static uint32_t cur_stamp = 1; static int32_t *queue;
static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }

static void build_darts(void) {
    for (int u = 0; u < b; u++) dcnt[u] = 0;
    for (int i = 0; i < m; i++) {
        int u = eu[i], v = ev[i], g = eg[i];
        if (dcnt[u] >= MAXDEG || dcnt[v] >= MAXDEG) { fprintf(stderr, "degree too large\n"); exit(2); }
        dto[u][dcnt[u]] = v; dg[u][dcnt[u]] = g; dcnt[u]++;
        dto[v][dcnt[v]] = u; dg[v][dcnt[v]] = INV[g]; dcnt[v]++;
    }
}

/* far count from all roots; abort (return > lim) when the running total exceeds lim */
static long evalcost(long lim) {
    long far = 0; long nl = (long)b * N;
    for (int r = 0; r < b; r++) {
        cur_stamp++;
        int32_t head = 0, tail = 0;
        int32_t root = (int32_t)(r * N);
        stamp[root] = cur_stamp; queue[tail++] = root;
        int32_t ls = 0, le = 1;
        for (int d = 0; d < D; d++) {
            for (int32_t qi = ls; qi < le; qi++) {
                int32_t id = queue[qi]; int u = id / N; int x = id - u * N;
                for (int c = 0; c < dcnt[u]; c++) {
                    int v = dto[u][c]; int y = MT[(size_t)dg[u][c] * N + x];
                    int32_t nid = v * N + y;
                    if (stamp[nid] != cur_stamp) { stamp[nid] = cur_stamp; queue[tail++] = nid; }
                }
            }
            ls = le; le = tail;
            if (ls == le) break;
        }
        far += nl - tail;
        if (far > lim) return far;
    }
    return far;
}

static void write_base(const char *fn) {
    FILE *f = fopen(fn, "w"); if (!f) return;
    fprintf(f, "%d %d\n", b, m);
    for (int i = 0; i < m; i++) fprintf(f, "%d %d %d\n", eu[i], ev[i], eg[i]);
    fclose(f);
}

static void write_edges(const char *fn) {
    FILE *f = fopen(fn, "w"); if (!f) return;
    fprintf(f, "%ld\n", (long)b * N);
    for (int i = 0; i < m; i++)
        for (int x = 0; x < N; x++)
            fprintf(f, "%d %d\n", eu[i] * N + x, ev[i] * N + MT[(size_t)eg[i] * N + x]);
    fclose(f);
}

static int two_switch(int i, int j) {  /* returns 1 if performed (edges i,j get swapped endpoints v) */
    if (eu[i] == eu[j] || ev[i] == ev[j]) return 0;
    int t = ev[i]; ev[i] = ev[j]; ev[j] = t;
    return 1;
}


static int tabu_v[MAXM][1024];     /* tabu_v[i][g]: step until which edge i may not take voltage g */
static int32_t tabu_b[MAXM][MAXM]; /* tabu for base swaps (i,j) */

int main(int argc, char **argv) {
    if (argc < 7) { fprintf(stderr, "usage: ltabu TABLE.bin BASE.txt D seconds seed OUT\n"); return 2; }
    FILE *f = fopen(argv[1], "rb"); int32_t n32;
    if (!f || fread(&n32, 4, 1, f) != 1) { fprintf(stderr, "bad table\n"); return 2; }
    N = n32; MT = malloc((size_t)N * N * 2);
    if (fread(MT, 2, (size_t)N * N, f) != (size_t)N * N) { fprintf(stderr, "short table\n"); return 2; }
    fclose(f);
    INV = malloc(N * sizeof(int));
    for (int g = 0; g < N; g++) { INV[g] = -1; for (int h = 0; h < N; h++) if (MT[(size_t)g * N + h] == 0) { INV[g] = h; break; } if (INV[g] < 0) return 2; }
    f = fopen(argv[2], "r"); if (!f) return 2;
    if (fscanf(f, "%d %d", &b, &m) != 2) return 2;
    for (int i = 0; i < m; i++) {
        int g = -1;
        if (fscanf(f, "%d %d %d", &eu[i], &ev[i], &g) < 2) return 2;
        if (g < 0) g = (int)(rnd() % N);
        eg[i] = g;
    }
    fclose(f);
    D = atoi(argv[3]); double secs = atof(argv[4]);
    rs ^= (uint64_t)atoll(argv[5]) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 20; i++) rnd();
    const char *OUT = argv[6];
    int TT = getenv("TT") ? atoi(getenv("TT")) : 12;          /* tabu tenure (steps) */
    int TTB = getenv("TTB") ? atoi(getenv("TTB")) : 30;       /* tabu tenure for base swaps */
    long NOIMP = getenv("NOIMP") ? atol(getenv("NOIMP")) : 400; /* steps without improvement before a kick */
    int KICK = getenv("KICK") ? atoi(getenv("KICK")) : 3;      /* random voltage changes in a kick */
    int MV2 = getenv("MV2") ? atoi(getenv("MV2")) : 1;         /* include base 2-switch neighbours */
    int FIXBASE = getenv("FIXBASE") ? atoi(getenv("FIXBASE")) : 0;
    int QUIET = getenv("QUIET") ? 1 : 0;
    stamp = calloc((size_t)b * N + 1, sizeof(uint32_t)); queue = malloc(((size_t)b * N + 1) * sizeof(int32_t));
    build_darts();
    long cur = evalcost(1L << 60), best = cur;
    int bu[MAXM], bv[MAXM], bgv[MAXM];
    memcpy(bu, eu, sizeof(int) * m); memcpy(bv, ev, sizeof(int) * m); memcpy(bgv, eg, sizeof(int) * m);
    char fn[1024];
    double t0 = now(); long evals = 0, step = 0, lastimp = 0;
    double lastprint = t0;
    if (!QUIET) fprintf(stderr, "init N=%d b=%d m=%d cost=%ld\n", N, b, m, cur);
    while (now() - t0 < secs) {
        step++;
        /* best non-tabu neighbour (exact values), aspiration if it beats the global best */
        long bestn = 1L << 60; int nbtype = -1, ni = -1, nj = -1, nval = -1; int ties = 0;
        for (int i = 0; i < m; i++) {
            if (FIXBASE) break;
            int g0 = eg[i];
            for (int g = 0; g < N; g++) {
                if (g == g0) continue;
                int istabu = tabu_v[i][g] >= step;
                long lim = istabu ? (best - 1) : bestn;
                if (lim < cur - 0) { /* nothing needed */ }
                eg[i] = g; build_darts();
                long c2 = evalcost(lim);
                evals++;
                eg[i] = g0; build_darts();
                if (istabu && c2 > best - 1) continue;
                if (c2 < bestn) { bestn = c2; nbtype = 0; ni = i; nval = g; ties = 1; }
                else if (c2 == bestn && c2 <= lim) { ties++; if (rnd() % ties == 0) { nbtype = 0; ni = i; nval = g; } }
            }
        }
        if (MV2) for (int i = 0; i < m; i++) for (int j = i + 1; j < m; j++) {
            if (eu[i] == eu[j] || ev[i] == ev[j]) continue;
            int istabu = tabu_b[i][j] >= step;
            long lim = istabu ? (best - 1) : bestn;
            int t = ev[i]; ev[i] = ev[j]; ev[j] = t; build_darts();
            long c2 = evalcost(lim);
            evals++;
            t = ev[i]; ev[i] = ev[j]; ev[j] = t; build_darts();
            if (istabu && c2 > best - 1) continue;
            if (c2 < bestn) { bestn = c2; nbtype = 1; ni = i; nj = j; ties = 1; }
            else if (c2 == bestn && c2 <= lim) { ties++; if (rnd() % ties == 0) { nbtype = 1; ni = i; nj = j; } }
        }
        if (nbtype < 0) { /* everything tabu: kick */
            lastimp = step - NOIMP;
            continue;
        }
        if (nbtype == 0) {
            int old = eg[ni];
            eg[ni] = nval; build_darts();
            tabu_v[ni][old] = (int)(step + TT);
        } else {
            int t = ev[ni]; ev[ni] = ev[nj]; ev[nj] = t; build_darts();
            tabu_b[ni][nj] = (int)(step + TTB);
        }
        cur = bestn;
        if (cur < best) {
            best = cur; lastimp = step;
            memcpy(bu, eu, sizeof(int) * m); memcpy(bv, ev, sizeof(int) * m); memcpy(bgv, eg, sizeof(int) * m);
            snprintf(fn, sizeof fn, "%s.best.txt", OUT); write_base(fn);
            if (!QUIET) fprintf(stderr, "  t=%.1f step=%ld evals=%ld best=%ld\n", now() - t0, step, evals, best);
            if (best == 0) {
                snprintf(fn, sizeof fn, "%s.edges", OUT); write_edges(fn);
                printf("RESULT FOUND cost=0 n=%ld file=%s\n", (long)b * N, fn);
                fflush(stdout);
                break;
            }
        }
        if (step - lastimp > NOIMP) {  /* kick: restart from the global best with random voltage changes */
            memcpy(eu, bu, sizeof(int) * m); memcpy(ev, bv, sizeof(int) * m); memcpy(eg, bgv, sizeof(int) * m);
            for (int k = 0; k < KICK; k++) eg[rnd() % m] = (int)(rnd() % N);
            build_darts();
            cur = evalcost(1L << 60);
            lastimp = step;
        }
        if (!QUIET && now() - lastprint > 60) { lastprint = now(); fprintf(stderr, "  .. t=%.0f step=%ld evals=%ld cur=%ld best=%ld\n", now() - t0, step, evals, cur, best); }
    }
    memcpy(eu, bu, sizeof(int) * m); memcpy(ev, bv, sizeof(int) * m); memcpy(eg, bgv, sizeof(int) * m);
    build_darts();
    snprintf(fn, sizeof fn, "%s.best.txt", OUT); write_base(fn);
    printf("DONE best=%ld steps=%ld evals=%ld time=%.1f\n", best, step, evals, now() - t0);
    return 0;
}
