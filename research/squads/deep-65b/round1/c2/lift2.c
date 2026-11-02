/* lift2.c: word-based cost for 2+2 lifts of the base [[a,6-a],[6-a,a]] by a group H (SmallGroup table).
 *
 * Base vertices: A0=0, A1=1, B0=2, B1=3. Class (i,j) has M[i][j] parallel base edges with voltages in H
 * (a SET: distinct values, so the lift is simple). Lift: A_i,h ~ B_j,h*g for each voltage g of class (i,j).
 * Spanning-tree edges (first edge of classes (0,0),(0,1),(1,0)) are fixed to the identity (normalisation).
 *
 * Word cost: W = sum over base sources u, targets v, of #{x in H : no non-backtracking base walk of length
 * <= 5 from u to v with holonomy x}. Non-backtracking walks are enumerated once as a tree (depth <= 5);
 * holonomy of a walk = product of its dart voltages in order (inverse for backward darts).
 * BFS check: the lift has bad unordered pairs (dist > 5) = m*W/2 exactly (m = |H|).
 *
 * usage:
 *   lift2 TABLE a check SEED COUNT [OUTPREFIX]      random assignments: W vs BFS, must match (m*W == 2*bad)
 *   lift2 TABLE a tabu SEED SECONDS OUTPREFIX [TENURE STALL SAMPLE]
 *        tabu over single-voltage changes (full neighbourhood unless SAMPLE>0); writes OUTPREFIX.val and
 *        OUTPREFIX.edges when cost 0 is reached.
 *   lift2 TABLE a speed SEED COUNT                  time COUNT evaluations
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAXM 192
#define MAXN 20000
#define NE 12

typedef struct { int par; uint8_t dart; uint8_t cidx; } node_t;

static int m;
static uint8_t MUL[MAXM][MAXM];
static int INV[MAXM];
static int EA[NE], EB[NE], CLS[NE], FIXED[NE];
static int NN;
static node_t ND[MAXN];
static int VAL[NE];
static uint8_t SEEN[16][MAXM];
static uint8_t HOL[MAXN];
static int FREE[NE], NFREE;
static int TABU[NE][MAXM];
static int MIR[NE];      /* sym mode: partner edge with equal voltage (A0B0<->A1B1, A0B1<->A1B0) */
static int SYM = 0;
static int FREES[NE], NFREES;
static void setv(int e, int t) { VAL[e] = t; if (SYM && MIR[e] >= 0) VAL[MIR[e]] = t; }

static int tail_of(int d) { int e = d >> 1; return (d & 1) ? 2 + EB[e] : EA[e]; }
static int head_of(int d) { int e = d >> 1; return (d & 1) ? EA[e] : 2 + EB[e]; }

static int read_table(const char *fn) {
    FILE *f = fopen(fn, "r");
    if (!f) { perror(fn); return 0; }
    if (fscanf(f, "%d", &m) != 1) return 0;
    if (m > MAXM) { fprintf(stderr, "m too big\n"); return 0; }
    for (int g = 0; g < m; g++)
        for (int h = 0; h < m; h++) {
            int x;
            if (fscanf(f, "%d", &x) != 1) return 0;
            MUL[g][h] = (uint8_t)x;
        }
    fclose(f);
    for (int h = 0; h < m; h++) if (MUL[0][h] != h) { fprintf(stderr, "identity is not 0\n"); return 0; }
    for (int g = 0; g < m; g++)
        for (int h = 0; h < m; h++) if (MUL[g][h] == 0) INV[g] = h;
    return 1;
}

static void build_base(int a) {
    int M[2][2] = {{a, 6 - a}, {6 - a, a}};
    int e = 0;
    for (int i = 0; i < 2; i++)
        for (int j = 0; j < 2; j++)
            for (int k = 0; k < M[i][j]; k++) {
                EA[e] = i; EB[e] = j; CLS[e] = 2 * i + j;
                FIXED[e] = (k == 0 && !(i == 1 && j == 1) && !SYM);
                e++;
            }
    if (e != NE) { fprintf(stderr, "bad a\n"); exit(1); }
    NFREE = 0;
    for (int x = 0; x < NE; x++) if (!FIXED[x]) FREE[NFREE++] = x;
    for (int x = 0; x < NE; x++) MIR[x] = -1;
    /* sym (Haar-type) mirror: class (0,0) <-> (1,1) and (0,1) <-> (1,0) with equal voltage sets */
    for (int k = 0; k < a; k++) { MIR[k] = 12 - a + k; MIR[12 - a + k] = k; }
    for (int k = 0; k < 6 - a; k++) { MIR[a + k] = 6 + k; MIR[6 + k] = a + k; }
    NFREES = 0;
    for (int x = 0; x < NE; x++) if (!FIXED[x] && (SYM ? x < 6 : 1)) FREES[NFREES++] = x;
}

/* non-backtracking walk tree, depth <= 5, one block per source u (root first) */
static void build_tree(void) {
    NN = 0;
    for (int u = 0; u < 4; u++) {
        int base = NN;
        ND[NN].par = -1; ND[NN].dart = 255; ND[NN].cidx = (uint8_t)(u * 4 + u); NN++;
        int vert_of_node_u = u;
        (void)vert_of_node_u;
        for (int q = base; q < NN; q++) {
            int depth = 0;
            { /* depth of q: count parents within block */
                int p = q; while (ND[p].par >= 0) { p = ND[p].par; depth++; }
            }
            if (depth >= 5) continue;
            int qv;
            if (ND[q].par < 0) qv = u; else qv = head_of(ND[q].dart);
            for (int d = 0; d < 2 * NE; d++) {
                if (tail_of(d) != qv) continue;
                if (ND[q].par >= 0 && d == (ND[q].dart ^ 1)) continue;
                ND[NN].par = q; ND[NN].dart = (uint8_t)d;
                ND[NN].cidx = (uint8_t)(u * 4 + head_of(d));
                NN++;
            }
        }
    }
}

static inline int valid(int e, int t) {
    for (int e2 = 0; e2 < NE; e2++)
        if (e2 != e && CLS[e2] == CLS[e] && VAL[e2] == t) return 0;
    return 1;
}

static int evalW(void) {
    uint8_t dv[2 * NE];
    for (int e = 0; e < NE; e++) { dv[2 * e] = (uint8_t)VAL[e]; dv[2 * e + 1] = (uint8_t)INV[VAL[e]]; }
    memset(SEEN, 0, sizeof SEEN);
    for (int u = 0; u < 4; u++) SEEN[u * 5][0] = 1;   /* length-0 walk: (u,u,identity) */
    for (int n = 0; n < NN; n++) {
        const node_t *p = &ND[n];
        if (p->par < 0) { HOL[n] = 0; continue; }
        int x = MUL[HOL[p->par]][dv[p->dart]];
        HOL[n] = (uint8_t)x;
        SEEN[p->cidx][x] = 1;
    }
    int W = 0;
    for (int c = 0; c < 16; c++)
        for (int x = 0; x < m; x++) W += (SEEN[c][x] == 0);
    return W;
}

static uint64_t RS = 88172645463325252ULL;
static inline uint64_t rnd(void) {
    RS ^= RS >> 12; RS ^= RS << 25; RS ^= RS >> 27;
    return RS * 2685821657736338717ULL;
}

static double now(void) {
    struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + 1e-9 * ts.tv_nsec;
}

static void random_init(void) {
    for (int e = 0; e < NE; e++) VAL[e] = FIXED[e] ? 0 : -1;
    if (SYM) {
        for (int e = 0; e < NE; e++) if (MIR[e] >= 0 && VAL[e] == -1 && FIXED[e]) VAL[MIR[e]] = 0;
        for (int k = 0; k < NE; k++) if (MIR[k] >= 0 && FIXED[k]) VAL[MIR[k]] = 0;
    }
    for (int k = 0; k < (SYM ? NFREES : NFREE); k++) {
        int e = SYM ? FREES[k] : FREE[k], t;
        do { t = (int)(rnd() % m); } while (!valid(e, t));
        setv(e, t);
    }
}

/* exact BFS on the built lift: returns bad unordered pairs at distance > 5 (or unreachable) */
static long bfs_bad_unordered(void) {
    int n = 4 * m;
    static int adj[4 * MAXM][6];
    static int deg[4 * MAXM];
    static int dist[4 * MAXM], queue[4 * MAXM];
    memset(deg, 0, sizeof deg);
    for (int e = 0; e < NE; e++)
        for (int h = 0; h < m; h++) {
            int u = EA[e] * m + h, v = (2 + EB[e]) * m + MUL[h][VAL[e]];
            if (deg[u] >= 6 || deg[v] >= 6) { fprintf(stderr, "degree > 6\n"); exit(1); }
            adj[u][deg[u]++] = v; adj[v][deg[v]++] = u;
        }
    for (int u = 0; u < n; u++) {
        if (deg[u] != 6) { fprintf(stderr, "degree %d != 6\n", deg[u]); exit(1); }
        for (int i = 0; i < 6; i++) for (int j = i + 1; j < 6; j++)
            if (adj[u][i] == adj[u][j]) { fprintf(stderr, "multi-edge\n"); exit(1); }
    }
    long total = 0;
    for (int s = 0; s < n; s++) {
        for (int i = 0; i < n; i++) dist[i] = -1;
        int qh = 0, qt = 0;
        queue[qt++] = s; dist[s] = 0;
        int within = 0;
        while (qh < qt) {
            int x = queue[qh++];
            if (dist[x] >= 5) continue;
            for (int k = 0; k < 6; k++) {
                int y = adj[x][k];
                if (dist[y] < 0) { dist[y] = dist[x] + 1; queue[qt++] = y; within++; }
            }
        }
        total += (n - 1 - within);
    }
    return total / 2;
}

static void write_graph(const char *fn) {
    FILE *f = fopen(fn, "w");
    if (!f) { perror(fn); return; }
    fprintf(f, "%d\n", 4 * m);
    for (int e = 0; e < NE; e++)
        for (int h = 0; h < m; h++)
            fprintf(f, "%d %d\n", EA[e] * m + h, (2 + EB[e]) * m + MUL[h][VAL[e]]);
    fclose(f);
}

static void write_val(const char *fn) {
    FILE *f = fopen(fn, "w");
    if (!f) { perror(fn); return; }
    for (int e = 0; e < NE; e++) fprintf(f, "%d ", VAL[e]);
    fprintf(f, "\n");
    fclose(f);
}

static int run_tabu(double secs, int tenure, int stall, int sample, long *iters_out, double *tsol,
                    int bestval[NE], int *best_out) {
    double t0 = now();
    random_init();
    int cur = evalW();
    int best = cur;
    memcpy(bestval, VAL, sizeof VAL);
    *tsol = -1;
    memset(TABU, 0, sizeof TABU);
    long it = 0, last = 0;
    while (best > 0) {
        it++;
        if ((it & 3) == 0 && now() - t0 > secs) break;
        int bc = 1 << 30, be = -1, bt = -1, bn = 0;
        int NF = SYM ? NFREES : NFREE; int *FL = SYM ? FREES : FREE;
        if (sample > 0) {
            for (int s = 0; s < sample; s++) {
                int e = FL[rnd() % NF];
                int t = (int)(rnd() % m);
                if (t == VAL[e] || !valid(e, t)) continue;
                int old = VAL[e];
                setv(e, t); int c = evalW(); setv(e, old);
                if (TABU[e][t] > it && c >= best) continue;
                if (c < bc) { bc = c; be = e; bt = t; bn = 1; }
                else if (c == bc) { bn++; if (rnd() % bn == 0) { be = e; bt = t; } }
            }
        } else {
            for (int k = 0; k < NF; k++) {
                int e = FL[k], old = VAL[e];
                for (int t = 0; t < m; t++) {
                    if (t == old || !valid(e, t)) continue;
                    setv(e, t); int c = evalW(); setv(e, old);
                    if (TABU[e][t] > it && c >= best) continue;
                    if (c < bc) { bc = c; be = e; bt = t; bn = 1; }
                    else if (c == bc) { bn++; if (rnd() % bn == 0) { be = e; bt = t; } }
                }
            }
        }
        if (be < 0) continue;
        int old = VAL[be];
        TABU[be][old] = (int)it + tenure + (int)(rnd() % (uint64_t)tenure);
        setv(be, bt); cur = bc;
        if (cur < best) {
            best = cur; memcpy(bestval, VAL, sizeof VAL); last = it;
            if (best == 0) *tsol = now() - t0;
        }
        if (it - last > stall) {
            for (int r = 0; r < 3; r++) {
                int e = FL[rnd() % NF], t;
                do { t = (int)(rnd() % m); } while (!valid(e, t));
                setv(e, t);
            }
            last = it;
            cur = evalW();
        }
    }
    *iters_out = it;
    *best_out = best;
    return best;
}

int main(int argc, char **argv) {
    if (argc < 4) { fprintf(stderr, "usage: see header\n"); return 2; }
    if (!read_table(argv[1])) { fprintf(stderr, "table read failed\n"); return 2; }
    int a = atoi(argv[2]);
    if (!strcmp(argv[3], "tabu") && argc > 10) SYM = atoi(argv[10]);
    build_base(a);
    build_tree();
    const char *mode = argv[3];
    if (!strcmp(mode, "check")) {
        uint64_t seed = (uint64_t)atoll(argv[4]);
        int count = atoi(argv[5]);
        const char *outp = argc > 6 ? argv[6] : NULL;
        RS ^= seed * 0x9E3779B97F4A7C15ULL; if (!RS) RS = 1;
        int mism = 0; long maxbad = 0;
        for (int c = 0; c < count; c++) {
            if (c % 2 == 0) random_init();
            else {
                /* near-optimal style states: a few random moves from the previous state */
                for (int r = 0; r < 2; r++) {
                    int e = FREE[rnd() % NFREE], t;
                    do { t = (int)(rnd() % m); } while (!valid(e, t));
                    VAL[e] = t;
                }
            }
            int W = evalW();
            long bad = bfs_bad_unordered();
            if ((long)m * W != 2 * bad) mism++;
            if (bad > maxbad) maxbad = bad;
            if (c < 5 || (c % 50) == 0) printf("sample %d W=%d m*W/2=%ld bfs_bad=%ld\n", c, W, (long)m * W / 2, bad);
            if (outp && c == 0) { char fn[512]; snprintf(fn, sizeof fn, "%s.check.edges", outp); write_graph(fn); }
        }
        printf("CHECK m=%d a=%d samples=%d mismatches=%d max_bad=%ld\n", m, a, count, mism, maxbad);
        return mism != 0;
    }
    if (!strcmp(mode, "speed")) {
        uint64_t seed = (uint64_t)atoll(argv[4]);
        int count = atoi(argv[5]);
        RS ^= seed * 0x9E3779B97F4A7C15ULL; if (!RS) RS = 1;
        random_init();
        double t0 = now(); long s = 0;
        for (int c = 0; c < count; c++) s += evalW();
        double dt = now() - t0;
        printf("SPEED nodes=%d evals=%d time=%.3f us_per_eval=%.2f (checksum %ld)\n", NN, count, dt, 1e6 * dt / count, s);
        return 0;
    }
    if (!strcmp(mode, "tabu")) {
        uint64_t seed = (uint64_t)atoll(argv[4]);
        double secs = atof(argv[5]);
        const char *outp = argv[6];
        int tenure = argc > 7 ? atoi(argv[7]) : 10;
        int stall = argc > 8 ? atoi(argv[8]) : 400;
        int sample = argc > 9 ? atoi(argv[9]) : 0;
        RS ^= seed * 0x9E3779B97F4A7C15ULL; if (!RS) RS = 1;
        int bestval[NE]; long iters; double tsol; int best;
        run_tabu(secs, tenure, stall, sample, &iters, &tsol, bestval, &best);
        memcpy(VAL, bestval, sizeof VAL);
        int check = evalW();
        printf("TABU a=%d m=%d n=%d seed=%llu secs=%.0f tenure=%d stall=%d sample=%d iters=%ld best=%d (re-eval %d) t_solution=%s%.2f\n",
               a, m, 4 * m, (unsigned long long)seed, secs, tenure, stall, sample, iters, best, check,
               tsol >= 0 ? "" : "none/", tsol >= 0 ? tsol : 0.0);
        printf("VAL");
        for (int e = 0; e < NE; e++) printf(" %d", VAL[e]);
        printf("\n");
        if (best == 0) {
            char fn[512];
            snprintf(fn, sizeof fn, "%s.val", outp); write_val(fn);
            snprintf(fn, sizeof fn, "%s.edges", outp); write_graph(fn);
            printf("WROTE %s.edges (bfs bad=%ld)\n", outp, bfs_bad_unordered());
        }
        return 0;
    }
    fprintf(stderr, "unknown mode\n");
    return 2;
}
