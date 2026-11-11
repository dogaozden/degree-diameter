/* fa (w19): far-pair-aimed greedy/tabu on voltages, built from lann.c. lann: annealer for voltage lifts of a bipartite base multigraph over a group table, with optional base 2-switches (w19).
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


/* Dist[r][id]: distance from root (r,e) to lift vertex id, 255 if > D */
static uint8_t *DIST; static int32_t *scoreA; static uint32_t *seenA;
static void all_dist(void) {
    long nl = (long)b * N;
    for (int r = 0; r < b; r++) {
        uint8_t *dr = DIST + (size_t)r * nl;
        memset(dr, 255, nl);
        int32_t root = r * N; dr[root] = 0;
        int32_t ls = 0, le = 1, tail = 1; queue[0] = root;
        for (int d = 0; d < D; d++) {
            for (int32_t qi = ls; qi < le; qi++) {
                int32_t id = queue[qi]; int u = id / N; int x = id - u * N;
                for (int c = 0; c < dcnt[u]; c++) {
                    int v = dto[u][c]; int y = MT[(size_t)dg[u][c] * N + x];
                    int32_t nid = v * N + y;
                    if (dr[nid] == 255) { dr[nid] = (uint8_t)(d + 1); queue[tail++] = nid; }
                }
            }
            ls = le; le = tail;
        }
    }
}

int main(int argc, char **argv) {
    if (argc < 7) { fprintf(stderr, "usage: fa TABLE.bin BASE.txt D seconds seed OUT\n"); return 2; }
    FILE *f = fopen(argv[1], "rb"); int32_t n32;
    if (!f || fread(&n32, 4, 1, f) != 1) { fprintf(stderr, "bad table\n"); return 2; }
    N = n32; MT = malloc((size_t)N * N * 2);
    if (fread(MT, 2, (size_t)N * N, f) != (size_t)N * N) { fprintf(stderr, "short table\n"); return 2; }
    fclose(f);
    INV = malloc(N * sizeof(int));
    for (int g = 0; g < N; g++) { INV[g] = -1; for (int h = 0; h < N; h++) if (MT[(size_t)g * N + h] == 0) { INV[g] = h; break; } if (INV[g] < 0) return 2; }
    f = fopen(argv[2], "r"); if (!f) return 2;
    if (fscanf(f, "%d %d", &b, &m) != 2) return 2;
    for (int i = 0; i < m; i++) { int g = -1; if (fscanf(f, "%d %d %d", &eu[i], &ev[i], &g) < 2) return 2; if (g < 0) g = (int)(rnd() % N); eg[i] = g; }
    fclose(f);
    D = atoi(argv[3]); double secs = atof(argv[4]);
    rs ^= (uint64_t)atoll(argv[5]) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 20; i++) rnd();
    const char *OUT = argv[6];
    int TT = getenv("TT") ? atoi(getenv("TT")) : 10;
    int KEXACT = getenv("KEXACT") ? atoi(getenv("KEXACT")) : 12;   /* exact evaluations per step */
    int FP = getenv("FP") ? atoi(getenv("FP")) : 8;                 /* far pairs sampled per step */
    long NOIMP = getenv("NOIMP") ? atol(getenv("NOIMP")) : 200;
    int KICK = getenv("KICK") ? atoi(getenv("KICK")) : 2;
    int QUIET = getenv("QUIET") ? 1 : 0;
    stamp = calloc((size_t)b * N + 1, sizeof(uint32_t)); queue = malloc(((size_t)b * N + 1) * sizeof(int32_t));
    DIST = malloc((size_t)b * b * N + 1);
    scoreA = calloc((size_t)m * N, sizeof(int32_t)); seenA = calloc((size_t)m * N, sizeof(uint32_t));
    static int tabu_v[MAXM][1024];
    build_darts();
    long nl = (long)b * N;
    long cur = evalcost(1L << 60), best = cur;
    int bu[MAXM], bv[MAXM], bgv[MAXM];
    memcpy(bu, eu, sizeof(int) * m); memcpy(bv, ev, sizeof(int) * m); memcpy(bgv, eg, sizeof(int) * m);
    char fn[1024];
    double t0 = now(); long step = 0, lastimp = 0, exacts = 0; uint32_t stampc = 0;
    if (!QUIET) fprintf(stderr, "init N=%d b=%d m=%d cost=%ld\n", N, b, m, cur);
    int *candI = malloc(sizeof(int) * m * N), *candG = malloc(sizeof(int) * m * N);
    while (now() - t0 < secs) {
        step++;
        all_dist();
        /* far pairs (root r, lift vertex w=(v,y)) */
        int nfar = 0; int *fr = malloc(sizeof(int) * 2 * (nl + 1));
        for (int r = 0; r < b; r++) for (long id = 0; id < nl; id++)
            if (DIST[(size_t)r * nl + id] == 255) { fr[2 * nfar] = r; fr[2 * nfar + 1] = (int)id; nfar++; }
        if (nfar == 0) { /* cost 0 */ best = 0; break; }
        /* score candidate (edge, g') moves by the far pairs they fix (one new edge shortcut, approximate) */
        int ncand = 0;
        int samp = nfar < FP ? nfar : FP;
        memset(scoreA, 0, sizeof(int32_t) * m * N);
        for (int s = 0; s < samp; s++) {
            int pi = (int)(rnd() % nfar);
            int r = fr[2 * pi]; int wid = fr[2 * pi + 1];
            int v = wid / N, y = wid - v * N; int yi = INV[y];
            uint8_t *dr = DIST + (size_t)r * nl;
            uint8_t *dv = DIST + (size_t)v * nl;
            stampc++;
            for (int i = 0; i < m; i++) {
                int P = eu[i], Q = ev[i];
                for (int X = 0; X < N; X++) {
                    int aP = dr[P * N + X];           /* root side at P */
                    if (aP <= 8) {
                        for (int Y = 0; Y < N; Y++) {
                            int bQ = dv[Q * N + MT[(size_t)Y * N + yi]];
                            if (bQ != 255 && aP + 1 + bQ <= 9) {
                                int gp = MT[(size_t)Y * N + INV[X]];
                                size_t key = (size_t)i * N + gp;
                                if (seenA[key] != stampc) { seenA[key] = stampc; scoreA[key]++; }
                            }
                        }
                    }
                    int aQ = dr[Q * N + X];           /* root side at Q (X is now a Q-element) */
                    if (aQ <= 8) {
                        for (int Y = 0; Y < N; Y++) {  /* Y is the P-element; new edge (P,Y)~(Q,X) => g' = X Y^{-1} */
                            int bP = dv[P * N + MT[(size_t)Y * N + yi]];
                            if (bP != 255 && aQ + 1 + bP <= 9) {
                                int gp = MT[(size_t)X * N + INV[Y]];
                                size_t key = (size_t)i * N + gp;
                                if (seenA[key] != stampc) { seenA[key] = stampc; scoreA[key]++; }
                            }
                        }
                    }
                }
            }
        }
        free(fr);
        /* collect candidates with the top scores */
        ncand = 0;
        int maxs = 0;
        for (int i = 0; i < m; i++) for (int g = 0; g < N; g++) {
            size_t key = (size_t)i * N + g;
            if (g == eg[i] || scoreA[key] == 0) continue;
            if (scoreA[key] > maxs) maxs = scoreA[key];
        }
        for (int t = maxs; t >= 1 && ncand < KEXACT * 4; t--) {
            for (int i = 0; i < m && ncand < KEXACT * 4; i++) for (int g = 0; g < N && ncand < KEXACT * 4; g++) {
                size_t key = (size_t)i * N + g;
                if (g != eg[i] && scoreA[key] == t) { candI[ncand] = i; candG[ncand] = g; ncand++; }
            }
        }
        /* exact evaluation of a random subset of the top candidates */
        long bestc = 1L << 60; int bi = -1, bg = -1; int tried = 0;
        for (int k = 0; k < ncand && tried < KEXACT; k++) {
            int j = (int)(k + rnd() % (ncand - k));
            int ti = candI[j], tg = candG[j]; candI[j] = candI[k]; candG[j] = candG[k]; candI[k] = ti; candG[k] = tg;
            int i = ti, g = tg;
            if (tabu_v[i][g] >= step) continue;
            int g0 = eg[i];
            eg[i] = g; build_darts();
            long c2 = evalcost(1L << 60);
            exacts++; tried++;
            eg[i] = g0; build_darts();
            if (c2 < bestc) { bestc = c2; bi = i; bg = g; }
        }
        if (bi < 0) { /* nothing: random kick */
            int i = (int)(rnd() % m); eg[i] = (int)(rnd() % N); build_darts(); cur = evalcost(1L << 60);
            lastimp = step;
            continue;
        }
        int old = eg[bi];
        eg[bi] = bg; build_darts();
        tabu_v[bi][old] = (int)(step + TT);
        cur = bestc;
        if (getenv("DBG") && step % 25 == 0) fprintf(stderr, "step %ld nfar %d ncand %d maxs %d cur %ld\n", step, nfar, ncand, maxs, cur);
        if (cur < best) {
            best = cur; lastimp = step;
            memcpy(bu, eu, sizeof(int) * m); memcpy(bv, ev, sizeof(int) * m); memcpy(bgv, eg, sizeof(int) * m);
            snprintf(fn, sizeof fn, "%s.best.txt", OUT); write_base(fn);
            if (!QUIET) fprintf(stderr, "  t=%.1f step=%ld exact=%ld cand=%d best=%ld\n", now() - t0, step, exacts, ncand, best);
            if (best == 0) break;
        }
        if (step - lastimp > NOIMP) {
            memcpy(eu, bu, sizeof(int) * m); memcpy(ev, bv, sizeof(int) * m); memcpy(eg, bgv, sizeof(int) * m);
            for (int k = 0; k < KICK; k++) eg[rnd() % m] = (int)(rnd() % N);
            build_darts(); cur = evalcost(1L << 60); lastimp = step;
        }
    }
    if (best == 0) {
        memcpy(eu, bu, sizeof(int) * m); memcpy(ev, bv, sizeof(int) * m); memcpy(eg, bgv, sizeof(int) * m);
        build_darts();
        snprintf(fn, sizeof fn, "%s.edges", OUT); write_edges(fn);
        printf("RESULT FOUND cost=0 n=%ld file=%s\n", (long)b * N, fn);
    }
    memcpy(eu, bu, sizeof(int) * m); memcpy(ev, bv, sizeof(int) * m); memcpy(eg, bgv, sizeof(int) * m);
    build_darts();
    snprintf(fn, sizeof fn, "%s.best.txt", OUT); write_base(fn);
    printf("DONE best=%ld steps=%ld exact=%ld time=%.1f\n", best, step, exacts, now() - t0);
    return 0;
}
