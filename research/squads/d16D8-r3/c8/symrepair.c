/* symrepair.c: targeted repair search for C-INVARIANT Z_k-lifts (Opus, d16D8 round 3), from the squad's repair.c
   (round 2 card c7). Edge class = orbit id: all edges of an orbit keep one voltage, so the cyclic group C acts on the
   lift and the sources in SRCFILE (one point and one line per C-orbit, from symbase.py) decide the diameter exactly.
   A move changes a whole orbit's voltage by delta with n_O * delta = (g - sigma), n_O = signed number of times the
   walk uses edges of that orbit.  Usage as below, but SRCFILE is required and plays the role of "all sources".

   Original description (repair.c, card c7):
   The lift check and its BFS are the same as baselift (bit-parallel over sources, sheets in k-bit blocks).

   A step takes an uncovered triple (s, y, g): the source (s,0) cannot reach (y,g) within D. A random depth-first search
   enumerates non-backtracking base walks of length <= D from s to y (pruned by the base distance to y). For one walk w
   with signed sheet sum sigma(w) = sum eps_i c_{e_i} (eps = +1 when the walk traverses an edge from ex to ey), and one of
   its edges e with sign eps, the move sets c_e += eps*(g - sigma(w)) mod k, so that w now reaches (y,g). K candidate
   moves are scored by the uncovered count on the active source set; the best is accepted by a Metropolis rule.

   Active set: all sources (NSRC = 0), or NSRC sources made of the bad sources of the last full check plus random sources;
   a full check runs after every EPOCH steps. A design with a full check of 0 is VALID.

   Usage:  repair BASE D SECS SEED OUT     (SECS = 0: only the full check, printed like baselift eval)
   env: NSRC (default 0), EPOCH (default 200), K (candidates per step, default 1), T0 (default 1.0), T1 (default 0.1),
        NODES (DFS node budget per move, default 100000). THREADS is not used (single thread). */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>
typedef uint64_t u64;

typedef struct { int s, y, g; } Trip;

static int V, k, E, P, Dm;
static int *ex, *ey, *ec, *ecls, *px, *py;
static int norb, *ooff, *olist;     /* edges; px/py: adjacency slot of the edge at its two ends */
static int *off, *nb, *sh, *eid, *sg;          /* CSR adjacency: nb = neighbour, sh = sheet shift x->nb, sg = +1 at ex, -1 at ey */
static u64 HI[64], LO[64];
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline int rndi(int n) { return (int)(rnd() % (uint64_t)n); }
static double now(void) { struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts); return ts.tv_sec + 1e-9 * ts.tv_nsec; }

static void setup_masks(void) {
    P = 64 / k;
    for (int c = 0; c < k; c++) {
        HI[c] = LO[c] = 0;
        for (int i = 0; i < P * k; i++) { if (i % k >= c) HI[c] |= 1ULL << i; else LO[c] |= 1ULL << i; }
    }
}
static inline u64 rot(u64 x, int c) {
    if (!c) return x;
    return ((x << c) & HI[c]) | ((x >> (k - c)) & LO[c]);
}

static void build_adj(void) {
    int *deg = calloc(V, sizeof(int));
    for (int e = 0; e < E; e++) { deg[ex[e]]++; deg[ey[e]]++; }
    off = malloc(sizeof(int) * (V + 1));
    off[0] = 0; for (int x = 0; x < V; x++) off[x + 1] = off[x] + deg[x];
    nb = malloc(sizeof(int) * off[V]); sh = malloc(sizeof(int) * off[V]);
    eid = malloc(sizeof(int) * off[V]); sg = malloc(sizeof(int) * off[V]);
    int *fill = calloc(V, sizeof(int));
    for (int e = 0; e < E; e++) {
        int x = ex[e], y = ey[e], c = ec[e];
        int j = off[x] + fill[x]++;
        nb[j] = y; sh[j] = c; eid[j] = e; sg[j] = 1; px[e] = j;
        j = off[y] + fill[y]++;
        nb[j] = x; sh[j] = (k - c) % k; eid[j] = e; sg[j] = -1; py[e] = j;
    }
    free(deg); free(fill);
}
static void read_base(const char *fn) {
    FILE *f = fopen(fn, "r"); if (!f) { fprintf(stderr, "cannot open %s\n", fn); exit(1); }
    if (fscanf(f, "%d %d %d", &V, &k, &E) != 3) { fprintf(stderr, "bad header\n"); exit(1); }
    if (k < 1 || k > 64) { fprintf(stderr, "need 1 <= k <= 64\n"); exit(1); }
    ex = malloc(sizeof(int) * E); ey = malloc(sizeof(int) * E); ec = malloc(sizeof(int) * E); ecls = malloc(sizeof(int) * E);
    px = malloc(sizeof(int) * E); py = malloc(sizeof(int) * E);
    for (int e = 0; e < E; e++) {
        if (fscanf(f, "%d %d %d %d", &ex[e], &ey[e], &ec[e], &ecls[e]) != 4) { fprintf(stderr, "short base file at edge %d\n", e); exit(1); }
        if (ex[e] < 0 || ex[e] >= V || ey[e] < 0 || ey[e] >= V || ec[e] < 0 || ec[e] >= k) { fprintf(stderr, "bad edge %d\n", e); exit(1); }
    }
    fclose(f);
    setup_masks(); build_adj();
}
static void write_base(const char *fn) {
    char tmpn[1024]; snprintf(tmpn, sizeof tmpn, "%s.tmp", fn);
    FILE *f = fopen(tmpn, "w"); fprintf(f, "%d %d %d\n", V, k, E);
    for (int e = 0; e < E; e++) fprintf(f, "%d %d %d %d\n", ex[e], ey[e], ec[e], ecls[e]);
    fclose(f); rename(tmpn, fn);
}
/* change the voltage of edge e (keeps the adjacency consistent) */
static void set_volt1(int e, int c) { ec[e] = c; sh[px[e]] = c; sh[py[e]] = (k - c) % k; }
/* change the voltage of the whole orbit of edge e */
static void set_volt(int e, int c) { int o = ecls[e]; for (int i = ooff[o]; i < ooff[o + 1]; i++) set_volt1(olist[i], c); }
static void build_orbits(void) {
    norb = 0; for (int e = 0; e < E; e++) if (ecls[e] + 1 > norb) norb = ecls[e] + 1;
    ooff = calloc(norb + 1, sizeof(int)); olist = malloc(sizeof(int) * E);
    for (int e = 0; e < E; e++) ooff[ecls[e] + 1]++;
    for (int o = 0; o < norb; o++) ooff[o + 1] += ooff[o];
    int *fill = calloc(norb, sizeof(int));
    for (int e = 0; e < E; e++) olist[ooff[ecls[e]] + fill[ecls[e]]++] = e;
    for (int e = 0; e < E; e++) if (ec[e] != ec[olist[ooff[ecls[e]]]]) { fprintf(stderr, "orbit %d not constant\n", ecls[e]); exit(1); }
    free(fill);
}

/* ---- lift BFS: uncovered count over a batch of sources, optionally recording the uncovered triples ---- */
static u64 *Ra, *Fa, *Xa;
static Trip *LA, *LB, *LW;
static long nA, nB, nW, LCAP;

static long bfs_batch(const int *src, int ns, Trip *L, long *cnt) {
    u64 *R = Ra, *F = Fa, *X = Xa;
    memset(R, 0, sizeof(u64) * V); memset(F, 0, sizeof(u64) * V);
    for (int i = 0; i < ns; i++) { R[src[i]] |= 1ULL << (i * k); F[src[i]] |= 1ULL << (i * k); }
    for (int d = 1; d <= Dm; d++) {
        for (int x = 0; x < V; x++) {
            u64 acc = 0;
            for (int j = off[x]; j < off[x + 1]; j++) { u64 f = F[nb[j]]; if (f) acc |= rot(f, (k - sh[j]) % k); }
            X[x] = acc & ~R[x];
        }
        for (int x = 0; x < V; x++) R[x] |= X[x];
        u64 *tp = F; F = X; X = tp;
    }
    u64 full = (ns * k >= 64) ? ~0ULL : ((1ULL << (ns * k)) - 1);
    long miss = 0;
    for (int x = 0; x < V; x++) {
        u64 mm = full & ~R[x];
        if (!mm) continue;
        miss += __builtin_popcountll(mm);
        if (L) while (mm) {
            int b = __builtin_ctzll(mm); mm &= mm - 1;
            if (*cnt < LCAP) { L[*cnt].s = src[b / k]; L[*cnt].y = x; L[*cnt].g = b % k; (*cnt)++; }
        }
    }
    return miss;
}
static long eval_set(const int *S, int n, Trip *L, long *cnt) {
    long tot = 0; *cnt = 0;
    for (int b = 0; b < n; b += P) {
        int ns = n - b < P ? n - b : P;
        tot += bfs_batch(S + b, ns, L, cnt);
    }
    return tot;
}

/* ---- walk search: non-backtracking walks of length <= Dm from s to tgt ---- */
#define MAXDEP 12
#define MAXFOUND 256
static int tgt, *distT, *qbuf;
static int FIXCLS = 0;   /* card c8: classes below FIXCLS are fixed (env FIXCLS) */
static int wE[MAXDEP], wS[MAXDEP];
static int FE[MAXFOUND][MAXDEP], FS[MAXFOUND][MAXDEP], FL[MAXFOUND], FSIG[MAXFOUND], nfound;
static long nodes_left, NODES;

static void dfs(int x, int depth, int lastE) {
    if (--nodes_left < 0 || nfound >= MAXFOUND) return;
    if (depth > 0 && x == tgt) {
        long s = 0;
        for (int i = 0; i < depth; i++) s += (long)wS[i] * ec[wE[i]];
        int n = nfound++;
        FL[n] = depth; FSIG[n] = (int)(((s % k) + k) % k);
        for (int i = 0; i < depth; i++) { FE[n][i] = wE[i]; FS[n][i] = wS[i]; }
    }
    if (depth == Dm) return;
    int lo = off[x], deg = off[x + 1] - lo;
    int ord[128];
    for (int t = 0; t < deg; t++) ord[t] = lo + t;
    for (int t = deg - 1; t > 0; t--) { int r = rndi(t + 1), tmp = ord[t]; ord[t] = ord[r]; ord[r] = tmp; }
    for (int t = 0; t < deg; t++) {
        int j = ord[t], e = eid[j], y = nb[j];
        if (e == lastE || depth + 1 + distT[y] > Dm) continue;
        int rep = 0;
        for (int i = 0; i < depth; i++) if (wE[i] == e) { rep = 1; break; }
        if (rep) continue;
        wE[depth] = e; wS[depth] = sg[j];
        dfs(y, depth + 1, e);
        if (nodes_left < 0 || nfound >= MAXFOUND) return;
    }
}
static void dist_to(int t) {
    for (int x = 0; x < V; x++) distT[x] = 1 << 20;
    int h = 0, tl = 0; distT[t] = 0; qbuf[tl++] = t;
    while (h < tl) {
        int x = qbuf[h++];
        for (int j = off[x]; j < off[x + 1]; j++) { int y = nb[j]; if (distT[y] > distT[x] + 1) { distT[y] = distT[x] + 1; qbuf[tl++] = y; } }
    }
}
/* repair move for uncovered (s, y, g): returns 1 and the edge and its new voltage */
static int make_move(int s, int y, int g, int *oe, int *onv) {
    tgt = y; dist_to(y);
    if (distT[s] > Dm) return 0;
    nodes_left = NODES; nfound = 0;
    dfs(s, 0, -1);
    if (!nfound) return 0;
    int w = rndi(nfound), p = rndi(FL[w]);
    if (FIXCLS > 0) {                                  /* card c8: only edges of classes >= FIXCLS may move */
        int cand[MAXDEP], nc = 0;
        for (int i = 0; i < FL[w]; i++) if (ecls[FE[w][i]] >= FIXCLS) cand[nc++] = i;
        if (!nc) return 0;
        p = cand[rndi(nc)];
    }
    int e = FE[w][p];
    int delta = ((g - FSIG[w]) % k + k) % k;          /* the walk reaches sheet FSIG[w]; needs +delta */
    int nO = 0; for (int i = 0; i < FL[w]; i++) if (ecls[FE[w][i]] == ecls[e]) nO += FS[w][i];
    nO = ((nO % k) + k) % k; if (!nO) return 0;
    int dv = -1; for (int t = 0; t < k; t++) if ((nO * t) % k == delta) { dv = t; break; }
    if (dv < 0) return 0;
    int nv = (ec[e] + dv) % k;
    if (nv == ec[e]) return 0;
    *oe = e; *onv = nv;
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: repair BASE D SECS SEED OUT\n"); return 1; }
    read_base(argv[1]);
    Dm = atoi(argv[2]);
    if (Dm > MAXDEP - 1) { fprintf(stderr, "D too large\n"); return 1; }
    double secs = atof(argv[3]);
    rs ^= (uint64_t)atoll(argv[4]) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 10; i++) rnd();
    const char *out = argv[5];
    int NSRC = getenv("NSRC") ? atoi(getenv("NSRC")) : 0;
    int EPOCH = getenv("EPOCH") ? atoi(getenv("EPOCH")) : 200;
    int K = getenv("K") ? atoi(getenv("K")) : 1;
    double T0 = getenv("T0") ? atof(getenv("T0")) : 1.0, T1 = getenv("T1") ? atof(getenv("T1")) : 0.1;
    NODES = getenv("NODES") ? atol(getenv("NODES")) : 100000;
    FIXCLS = getenv("FIXCLS") ? atoi(getenv("FIXCLS")) : 0;
    int act_all = 1; (void)NSRC;

    Ra = malloc(sizeof(u64) * V); Fa = malloc(sizeof(u64) * V); Xa = malloc(sizeof(u64) * V);
    distT = malloc(sizeof(int) * V); qbuf = malloc(sizeof(int) * V);
    LCAP = 3000000;
    LA = malloc(sizeof(Trip) * LCAP); LB = malloc(sizeof(Trip) * LCAP); LW = malloc(sizeof(Trip) * LCAP);
    int *allS = malloc(sizeof(int) * V); int NS = 0;
    { const char *sf = getenv("SRCFILE"); if (!sf) { fprintf(stderr, "SRCFILE required\n"); return 1; }
      FILE *f = fopen(sf, "r"); int x; while (NS < V && fscanf(f, "%d", &x) == 1) allS[NS++] = x; fclose(f); }
    build_orbits();
    int *act = malloc(sizeof(int) * V); char *mark = calloc(V, 1);
    long nact = V;

    double t0 = now();
    long U_full = eval_set(allS, NS, LA, &nA);
    long best = U_full;
    if (secs <= 0) {
        printf("V=%d k=%d E=%d D=%d lift_vertices=%lld sources=%d uncovered=%ld time=%.2fs%s\n", V, k, E, Dm,
               (long long)V * k, NS, U_full, now() - t0, U_full == 0 ? " VALID(all orbit sources)" : "");
        return 0;
    }
    write_base(out);
    fprintf(stderr, "start full uncovered %ld (k=%d, P=%d, act=%s NSRC=%d K=%d EPOCH=%d NODES=%ld)\n", U_full, k, P,
            act_all ? "all" : "sample", NSRC, K, EPOCH, NODES);

    long Ucur = U_full, steps = 0, accs = 0, nmoves = 0;
    double tlast = t0;
    while (best > 0 && now() - t0 < secs) {
        if (!act_all) {                                   /* active set: bad sources of the last full check + random */
            memset(mark, 0, V); nact = 0;
            for (long i = 0; i < nA; i++) { int s = LA[i].s; if (!mark[s]) { mark[s] = 1; act[nact++] = s; } }
            if (nact > NSRC) {                            /* too many bad sources: shuffle and keep NSRC */
                for (long i = nact - 1; i > 0; i--) { int r = rndi((int)i + 1), tmp = act[i]; act[i] = act[r]; act[r] = tmp; }
                for (long i = NSRC; i < nact; i++) mark[act[i]] = 0;
                nact = NSRC;
            }
            while (nact < NSRC) { int s = rndi(V); if (!mark[s]) { mark[s] = 1; act[nact++] = s; } }
            Ucur = eval_set(act, (int)nact, LA, &nA);
        }
        long lim_steps = act_all ? (1L << 60) : EPOCH;
        for (long st = 0; st < lim_steps; st++) {
            double tn = now();
            if (tn - t0 >= secs || nA == 0) break;
            double T = T0 * pow(T1 / T0, (tn - t0) / secs);
            long bestU = -1; int be = -1, bnv = 0;
            for (int c = 0; c < K; c++) {
                Trip tr = LA[rndi((int)nA)];
                int e, nv;
                if (!make_move(tr.s, tr.y, tr.g, &e, &nv)) continue;
                nmoves++;
                int old = ec[e];
                set_volt(e, nv);
                long Uc = eval_set(allS, NS, LW, &nW);
                set_volt(e, old);
                if (bestU < 0 || Uc < bestU) {
                    bestU = Uc; be = e; bnv = nv;
                    Trip *tmp = LB; LB = LW; LW = tmp; nB = nW;
                }
            }
            steps++;
            if (bestU < 0) continue;
            double u = (rnd() >> 11) * (1.0 / 9007199254740992.0) + 1e-300;
            if ((double)bestU <= (double)Ucur - T * log(u)) {      /* Metropolis: accept with prob exp(-(bestU-Ucur)/T) */
                set_volt(be, bnv); accs++;
                Ucur = bestU;
                Trip *tmp = LA; LA = LB; LB = tmp; nA = nB;
                if (act_all && Ucur < best) { best = Ucur; write_base(out); }
            }
            if (tn - tlast > 10) {
                tlast = tn;
                fprintf(stderr, "t=%.0f steps=%ld moves=%ld acc=%ld T=%.3f Ucur=%ld best=%ld\n",
                        tn - t0, steps, nmoves, accs, T, Ucur, best);
            }
            if (act_all && best == 0) break;
        }
        if (!act_all && best > 0) {                              /* full check at the end of the epoch */
            long Uf = eval_set(allS, NS, LA, &nA);
            if (Uf < best) { best = Uf; write_base(out); }
            fprintf(stderr, "full check t=%.0f steps=%ld acc=%ld full=%ld best=%ld\n", now() - t0, steps, accs, Uf, best);
        }
    }
    printf("RESULT V=%d k=%d D=%d best=%ld steps=%ld moves=%ld acc=%ld secs=%.0f out=%s%s\n", V, k, Dm, best, steps,
           nmoves, accs, now() - t0, out, best == 0 ? " (full check 0: run baselift eval to confirm)" : "");
    return 0;
}
