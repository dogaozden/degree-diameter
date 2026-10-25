/* lns.c: symmetry-breaking large-neighbourhood search for a large independent set of an orbit graph
 * (card c7, squad d16D7_r3).
 *
 * usage: lns GRAPH BLOCKS SEED OUT CPU_SECONDS RNG_SEED [KMIN KMAX NODE_LIMIT BB_MAXN ILS_ITERS PLOCAL LOCAL_CF PX BIGK PBIG]
 *   GRAPH : orbit graph, "M E", then per vertex "idx rep deg n1 ... n_deg" (og_pts.txt / og_lines.txt).
 *   BLOCKS: group-orbit blocks (quot/q9_*.map): line i = orbit-graph vertices of block i. Vertices in no line are
 *           singleton blocks. Blocks only choose WHAT is removed (whole orbits); the refill ignores them.
 *   SEED  : independent set, one index per line. OUT: best set so far, rewritten on every improvement.
 *
 * Move: pick k blocks meeting the solution S (k in [KMIN,KMAX]); either k random blocks (RANDOM), or (LOCAL, PLOCAL
 * percent) the blocks of the S-vertices adjacent to a random low-conflict outside vertex v0 (at most LOCAL_CF of
 * them), topped up with the blocks of S-vertices adjacent to random neighbours of v0. Remove them: S'.
 * The free set C = {v not in S' : no neighbour in S'} contains the removed vertices R and is re-filled
 * component by component: each connected component of G[C] is solved exactly by a bitset branch and bound
 * (degree 0/1 and domination reductions, bound |P| - greedy matching, random vertex order, NODE_LIMIT nodes); when the
 * limit is hit (or the component is larger than BB_MAXN) an ARW-style iterated local search with ILS_ITERS
 * perturbations takes over. Every component optimum is >= its removed count, so the set never gets smaller.
 * CPU time: CLOCK_PROCESS_CPUTIME_ID. Single thread.
 */
#define _GNU_SOURCE
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAXW 4
#define BBCAP (64 * MAXW)

/* ---------------- graph, blocks, solution ---------------- */
static int M, E, maxdeg;
static int *deg, **adj;
static int nblk, *blkoff, *blkmem, *blk;
static char *inS;
static int *conf, *Sl, *Spos, K;

static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline int rndint(int m) { return (int)(rnd64() % (uint64_t)m); }

static double cpu_now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &ts);
    return ts.tv_sec + 1e-9 * ts.tv_nsec;
}

static void add_v(int v) {
    inS[v] = 1; Spos[v] = K; Sl[K++] = v;
    for (int j = 0; j < deg[v]; j++) conf[adj[v][j]]++;
}

static void rem_v(int v) {
    inS[v] = 0;
    int p = Spos[v], last = Sl[--K];
    Sl[p] = last; Spos[last] = p;
    for (int j = 0; j < deg[v]; j++) conf[adj[v][j]]--;
}

static int *vmark; static int vstamp;
static int verify_set(const int *S, int k) {
    vstamp++;
    for (int i = 0; i < k; i++) {
        if (S[i] < 0 || S[i] >= M || vmark[S[i]] == vstamp) return 0;
        vmark[S[i]] = vstamp;
    }
    for (int i = 0; i < k; i++)
        for (int j = 0; j < deg[S[i]]; j++)
            if (vmark[adj[S[i]][j]] == vstamp) return 0;
    return 1;
}

static void save_sol(const char *of, const int *S, int k) {
    char tmp[1200];
    snprintf(tmp, sizeof tmp, "%s.tmp", of);
    FILE *o = fopen(tmp, "w");
    if (!o) { perror(tmp); exit(4); }
    for (int i = 0; i < k; i++) fprintf(o, "%d\n", S[i]);
    fclose(o);
    rename(tmp, of);
}

static void read_graph(const char *gf) {
    FILE *fp = fopen(gf, "r");
    if (!fp) { perror(gf); exit(1); }
    if (fscanf(fp, "%d %d", &M, &E) != 2) { fprintf(stderr, "bad header\n"); exit(1); }
    deg = calloc(M, sizeof(int));
    adj = calloc(M, sizeof(int *));
    for (int i = 0; i < M; i++) {
        int idx, rep, dg;
        if (fscanf(fp, "%d %d %d", &idx, &rep, &dg) != 3 || idx < 0 || idx >= M) { fprintf(stderr, "bad line %d\n", i); exit(1); }
        deg[idx] = dg;
        adj[idx] = malloc(sizeof(int) * (dg > 0 ? dg : 1));
        for (int j = 0; j < dg; j++) if (fscanf(fp, "%d", &adj[idx][j]) != 1) { fprintf(stderr, "bad neighbour list\n"); exit(1); }
        if (dg > maxdeg) maxdeg = dg;
    }
    fclose(fp);
}

static void read_blocks(const char *bf) {
    blk = malloc(sizeof(int) * M);
    for (int v = 0; v < M; v++) blk[v] = -1;
    blkoff = malloc(sizeof(int) * (M + 2));
    blkmem = malloc(sizeof(int) * M);
    FILE *fp = fopen(bf, "r");
    if (!fp) { perror(bf); exit(1); }
    char *line = NULL; size_t cap = 0; ssize_t len;
    int nb = 0, tot = 0;
    while ((len = getline(&line, &cap, fp)) != -1) {
        char *p = line, *end;
        int any = 0;
        blkoff[nb] = tot;
        for (;;) {
            long v = strtol(p, &end, 10);
            if (end == p) break;
            p = end; any = 1;
            if (v < 0 || v >= M || blk[v] >= 0) { fprintf(stderr, "bad block entry %ld\n", v); exit(1); }
            blk[v] = nb; blkmem[tot++] = (int)v;
        }
        if (any) nb++;
    }
    free(line);
    fclose(fp);
    blkoff[nb] = tot;
    for (int v = 0; v < M; v++)
        if (blk[v] < 0) { blk[v] = nb; blkoff[nb] = tot; blkmem[tot++] = v; nb++; }
    blkoff[nb] = tot;
    nblk = nb;
}

/* ---------------- exact maximum independent set of one component (bitset branch and bound) ---------------- */
static int bbN, bbW, bbmax_g;
static long long bnodes, bnodelim, g_nodes;
static int babort;
static int bbest, bbestN;
static int bbestSet[BBCAP];
static int bstk[BBCAP + 1];
static int bsp;
static uint64_t badj[BBCAP][MAXW];
static uint64_t bP[BBCAP + 2][MAXW];

static inline int btest(const uint64_t *P, int v) { return (int)((P[v >> 6] >> (v & 63)) & 1ULL); }
static inline void bclr(uint64_t *P, int v) { P[v >> 6] &= ~(1ULL << (v & 63)); }
static inline int bdeg(int v, const uint64_t *P) {
    int s = 0;
    for (int w = 0; w < bbW; w++) s += __builtin_popcountll(badj[v][w] & P[w]);
    return s;
}
static inline int bpop(const uint64_t *P) {
    int s = 0;
    for (int w = 0; w < bbW; w++) s += __builtin_popcountll(P[w]);
    return s;
}
/* size of a greedy maximal matching of G[P]: |P| - matching is a valid upper bound on alpha(G[P]) */
static int bmatch(const uint64_t *P) {
    uint64_t av[MAXW];
    for (int w = 0; w < bbW; w++) av[w] = P[w];
    int m = 0;
    for (int w = 0; w < bbW; w++) {
        uint64_t x = P[w];
        while (x) {
            int b = __builtin_ctzll(x);
            x &= x - 1;
            int v = (w << 6) | b;
            if (!((av[w] >> b) & 1ULL)) continue;
            av[w] &= ~(1ULL << b);
            for (int ww = 0; ww < bbW; ww++) {
                uint64_t y = badj[v][ww] & av[ww];
                if (y) { av[ww] &= ~(y & (~y + 1ULL)); m++; break; }
            }
        }
    }
    return m;
}

static void bb(int depth) {
    if (babort) return;
    if (++bnodes > bnodelim) { babort = 1; return; }
    uint64_t *P = bP[depth];
    int sp0 = bsp;
    int changed = 1;
    while (changed) {
        changed = 0;
        /* degree 0/1: some maximum independent set of G[P] contains v */
        for (int v = 0; v < bbN; v++) {
            if (!btest(P, v)) continue;
            if (bdeg(v, P) <= 1) {
                bstk[bsp++] = v;
                bclr(P, v);
                for (int w = 0; w < bbW; w++) P[w] &= ~badj[v][w];
                changed = 1;
            }
        }
        if (changed) continue;
        /* domination: u adjacent to v with N[v] cap P subset of N[u] cap P can be dropped */
        for (int v = 0; v < bbN && !changed; v++) {
            if (!btest(P, v)) continue;
            for (int w = 0; w < bbW && !changed; w++) {
                uint64_t x = badj[v][w] & P[w];
                while (x) {
                    int b = __builtin_ctzll(x);
                    x &= x - 1;
                    int u = (w << 6) | b;
                    int sub = 1;
                    for (int ww = 0; ww < bbW; ww++) {
                        uint64_t selfv = (ww == (v >> 6)) ? (1ULL << (v & 63)) : 0ULL;
                        uint64_t selfu = (ww == (u >> 6)) ? (1ULL << (u & 63)) : 0ULL;
                        uint64_t nv = (badj[v][ww] | selfv) & P[ww];
                        uint64_t nu = (badj[u][ww] | selfu) & P[ww];
                        if (nv & ~nu) { sub = 0; break; }
                    }
                    if (sub) { bclr(P, u); changed = 1; break; }
                }
            }
        }
    }
    int pc = bpop(P);
    if (pc == 0) {
        if (bsp > bbest) { bbest = bsp; bbestN = bsp; memcpy(bbestSet, bstk, sizeof(int) * bsp); }
        bsp = sp0;
        return;
    }
    if (bsp + pc - bmatch(P) <= bbest) { bsp = sp0; return; }
    int bv = -1, bd = -1;
    for (int v = 0; v < bbN; v++)
        if (btest(P, v)) { int d = bdeg(v, P); if (d > bd) { bd = d; bv = v; } }
    uint64_t *Q = bP[depth + 1];
    for (int w = 0; w < bbW; w++) Q[w] = P[w] & ~badj[bv][w];
    bclr(Q, bv);
    bstk[bsp++] = bv;
    bb(depth + 1);
    bsp--;
    if (babort) { bsp = sp0; return; }
    for (int w = 0; w < bbW; w++) Q[w] = P[w];
    bclr(Q, bv);
    bb(depth + 1);
    bsp = sp0;
}

/* ---------------- ARW-style iterated local search for MIS on a CSR graph ---------------- */
static char *ilin;
static int *ilt, *isol, *ipos, ik;
static int *ismark, istamp;
static int *isnap, *isnap2, *ilbuf;
static int ILSIT = 300;

static void il_ins(const int *st, const int *nb, int v) {
    ilin[v] = 1; ipos[v] = ik; isol[ik++] = v;
    for (int j = st[v]; j < st[v + 1]; j++) ilt[nb[j]]++;
}
static void il_del(const int *st, const int *nb, int v) {
    ilin[v] = 0;
    int p = ipos[v], last = isol[--ik];
    isol[p] = last; ipos[last] = p;
    for (int j = st[v]; j < st[v + 1]; j++) ilt[nb[j]]--;
}
static void il_ls(int n, const int *st, const int *nb) {
    int improved = 1;
    while (improved) {
        improved = 0;
        int off = rndint(n);
        for (int t = 0; t < n; t++) {
            int v = off + t; if (v >= n) v -= n;
            if (!ilin[v] && ilt[v] == 0) { il_ins(st, nb, v); improved = 1; }
        }
        int sk = ik;
        memcpy(isnap, isol, sizeof(int) * sk);
        for (int t = sk - 1; t > 0; t--) { int r = rndint(t + 1); int tmp = isnap[t]; isnap[t] = isnap[r]; isnap[r] = tmp; }
        for (int t = 0; t < sk; t++) {
            int x = isnap[t];
            if (!ilin[x]) continue;
            int nL = 0;
            for (int j = st[x]; j < st[x + 1]; j++) { int u = nb[j]; if (!ilin[u] && ilt[u] == 1) ilbuf[nL++] = u; }
            if (nL < 2) continue;
            int fa = -1, fb = -1;
            for (int a = 0; a < nL && fa < 0; a++) {
                int ua = ilbuf[a];
                istamp++;
                for (int j = st[ua]; j < st[ua + 1]; j++) ismark[nb[j]] = istamp;
                for (int b = 0; b < nL; b++)
                    if (b != a && ismark[ilbuf[b]] != istamp) { fa = ua; fb = ilbuf[b]; break; }
            }
            if (fa < 0) continue;
            il_del(st, nb, x);
            il_ins(st, nb, fa);
            il_ins(st, nb, fb);
            for (int j = st[x]; j < st[x + 1]; j++) { int u = nb[j]; if (!ilin[u] && ilt[u] == 0) il_ins(st, nb, u); }
            improved = 1;
        }
    }
}
static int ils_run(int n, const int *st, const int *nb, const char *init, int iters, int *out) {
    for (int v = 0; v < n; v++) { ilin[v] = 0; ilt[v] = 0; }
    ik = 0;
    for (int v = 0; v < n; v++) if (init[v]) il_ins(st, nb, v);
    il_ls(n, st, nb);
    int best = ik;
    memcpy(out, isol, sizeof(int) * ik);
    for (int it = 0; it < iters; it++) {
        int sk = ik;
        memcpy(isnap2, isol, sizeof(int) * sk);
        int v = -1, bl = 1 << 30;
        for (int s = 0; s < 4; s++) { int c = rndint(n); if (!ilin[c] && ilt[c] < bl) { bl = ilt[c]; v = c; } }
        if (v < 0) continue;
        for (int j = st[v]; j < st[v + 1]; j++) { int u = nb[j]; if (ilin[u]) il_del(st, nb, u); }
        il_ins(st, nb, v);
        il_ls(n, st, nb);
        if (ik > best) { best = ik; memcpy(out, isol, sizeof(int) * ik); }
        if (ik < sk) {
            int d = sk - ik;
            if (rndint(1 + d * d) != 0) {            /* keep the worse set with prob 1/(1+d^2), else revert */
                while (ik > 0) il_del(st, nb, isol[ik - 1]);
                for (int t = 0; t < sk; t++) il_ins(st, nb, isnap2[t]);
            }
        }
    }
    /* the final current set has the best size: output it (an equal-size alternative is a plateau move) */
    if (ik == best) memcpy(out, isol, sizeof(int) * ik);
    return best;
}

/* ---------------- component solver ---------------- */
static char *initf;
static long long g_exact, g_abort, g_ils;
static int g_check = 0;
static long long g_bug = 0, g_ilssub = 0, g_checked = 0;

/* n vertices, CSR (st, nb); isrem[i] = 1 if i was removed (the removed set is independent).
 * Writes an independent set of the component, of size >= number of removed vertices, to out and returns its size.
 * excl >= 0: forced variant; vertex excl is not allowed; returns -1 if no such set of size >= removed exists (or the
 * component is not solved exactly), and the caller then solves it normally. */
static int solve_comp(int n, const int *st, const int *nb, const char *isrem, int *out, int excl) {
    int rc = 0;
    for (int i = 0; i < n; i++) rc += isrem[i] ? 1 : 0;
    int have_bb = 0;
    if (n <= bbmax_g) {
        bbN = n; bbW = (n + 63) >> 6;
        for (int i = 0; i < n; i++) for (int w = 0; w < bbW; w++) badj[i][w] = 0;
        for (int i = 0; i < n; i++)
            for (int j = st[i]; j < st[i + 1]; j++) { int u = nb[j]; badj[i][u >> 6] |= 1ULL << (u & 63); }
        for (int w = 0; w < bbW; w++) bP[0][w] = 0;
        for (int i = 0; i < n; i++) if (i != excl) bP[0][i >> 6] |= 1ULL << (i & 63);
        bsp = 0; bbest = rc - 1; bbestN = -1; bnodes = 0; babort = 0;
        bb(0);
        g_nodes += bnodes;
        if (!babort) {
            g_exact++;
            int res;
            if (bbestN >= 0) { memcpy(out, bbestSet, sizeof(int) * bbestN); res = bbestN; }
            else if (excl >= 0) return -1;
            else { int k = 0; for (int i = 0; i < n; i++) if (isrem[i]) out[k++] = i; res = k; }
            if (g_check && excl < 0) {          /* debug: the exact optimum must dominate ILS, and be >= removed */
                for (int i = 0; i < n; i++) initf[i] = isrem[i] ? 1 : 0;
                int *tmpo = malloc(sizeof(int) * (n + 1));
                int ils = ils_run(n, st, nb, initf, 2000, tmpo);
                free(tmpo);
                if (ils > res) { g_bug++; fprintf(stderr, "CHECK BUG: ils %d > exact %d (n=%d)\n", ils, res, n); }
                if (ils < res) g_ilssub++;
                if (res < rc) { g_bug++; fprintf(stderr, "CHECK BUG: exact %d < removed %d\n", res, rc); }
                g_checked++;
            }
            return res;
        }
        if (excl >= 0) return -1;
        g_abort++;
        if (bbestN >= 0) {
            for (int i = 0; i < n; i++) initf[i] = 0;
            for (int t = 0; t < bbestN; t++) initf[bbestSet[t]] = 1;
            have_bb = 1;
        }
    }
    if (excl >= 0) return -1;
    if (!have_bb) for (int i = 0; i < n; i++) initf[i] = isrem[i] ? 1 : 0;
    g_ils++;
    return ils_run(n, st, nb, initf, ILSIT, out);
}

/* ---------------- main ---------------- */
int main(int argc, char **argv) {
    if (argc < 7) {
        fprintf(stderr, "usage: lns GRAPH BLOCKS SEED OUT CPU_SECONDS RNG_SEED [KMIN KMAX NODE_LIMIT BB_MAXN ILS_ITERS PLOCAL LOCAL_CF]\n");
        return 1;
    }
    const char *gf = argv[1], *bf = argv[2], *sf = argv[3], *of = argv[4];
    double budget = atof(argv[5]);
    rs ^= (uint64_t)strtoull(argv[6], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 20; i++) rnd64();
    int KMIN = argc > 7 ? atoi(argv[7]) : 3;
    int KMAX = argc > 8 ? atoi(argv[8]) : 10;
    bnodelim = argc > 9 ? atoll(argv[9]) : 20000;
    bbmax_g = argc > 10 ? atoi(argv[10]) : 128;
    ILSIT = argc > 11 ? atoi(argv[11]) : 300;
    int PLOC = argc > 12 ? atoi(argv[12]) : 50;
    int LCF = argc > 13 ? atoi(argv[13]) : 3;
    int PX = argc > 14 ? atoi(argv[14]) : 0;          /* percent of components tried with a forced exclusion */
    int BIGK = argc > 15 ? atoi(argv[15]) : 0;        /* big moves: k in [KMAX+1, BIGK] ... */
    int PBIG = argc > 16 ? atoi(argv[16]) : 0;        /* ... with this percent probability */
    if (bbmax_g > BBCAP) bbmax_g = BBCAP;
    g_check = getenv("LNS_CHECK") ? 1 : 0;
    if (KMAX < KMIN) KMAX = KMIN;

    read_graph(gf);
    read_blocks(bf);
    fprintf(stderr, "graph M=%d E=%d maxdeg=%d blocks=%d\n", M, E, maxdeg, nblk);

    inS = calloc(M, 1); conf = calloc(M, sizeof(int));
    Sl = malloc(sizeof(int) * M); Spos = malloc(sizeof(int) * M);
    vmark = calloc(M, sizeof(int));
    int *remstamp = calloc(M, sizeof(int));
    int *bstamp = calloc(nblk, sizeof(int)); int bepoch = 0;
    int *cmark = calloc(M, sizeof(int)), *loc = malloc(sizeof(int) * M), *Cl = malloc(sizeof(int) * M);
    int *lst = malloc(sizeof(int) * (M + 1));
    size_t cap = (size_t)M * (maxdeg + 1);
    int *lnb = malloc(sizeof(int) * cap), *snb = malloc(sizeof(int) * cap);
    int *compId = malloc(sizeof(int) * M), *queue = malloc(sizeof(int) * M), *subidx = malloc(sizeof(int) * M);
    int *sst = malloc(sizeof(int) * (M + 1));
    char *isrem = malloc(M);
    int *sol_out = malloc(sizeof(int) * M);
    int *chosen = malloc(sizeof(int) * M), *remv = malloc(sizeof(int) * M);
    int *bestSol = malloc(sizeof(int) * M);
    ilin = calloc(M, 1); ilt = calloc(M, sizeof(int)); isol = malloc(sizeof(int) * M); ipos = malloc(sizeof(int) * M);
    ismark = calloc(M, sizeof(int)); istamp = 0;
    isnap = malloc(sizeof(int) * M); isnap2 = malloc(sizeof(int) * M);
    ilbuf = malloc(sizeof(int) * (maxdeg + 2));
    initf = malloc(M);

    /* seed */
    FILE *sp = fopen(sf, "r");
    if (!sp) { perror(sf); return 1; }
    int v;
    while (fscanf(sp, "%d", &v) == 1) {
        if (v < 0 || v >= M || inS[v] || conf[v]) { fprintf(stderr, "seed vertex %d invalid\n", v); return 1; }
        add_v(v);
    }
    fclose(sp);
    /* maximal */
    for (int x = 0; x < M; x++) if (!inS[x] && conf[x] == 0) add_v(x);
    if (!verify_set(Sl, K)) { fprintf(stderr, "seed not independent\n"); return 1; }
    int bestK = K;
    memcpy(bestSol, Sl, sizeof(int) * K);
    save_sol(of, bestSol, K);
    fprintf(stderr, "seed K=%d (maximal), KMIN=%d KMAX=%d NODE_LIMIT=%lld BB_MAXN=%d ILS_ITERS=%d PLOCAL=%d LOCAL_CF=%d PX=%d BIGK=%d PBIG=%d\n",
            K, KMIN, KMAX, bnodelim, bbmax_g, ILSIT, PLOC, LCF, PX, BIGK, PBIG);

    double t0 = cpu_now(), next_log = 20.0;
    long long iter = 0, nimp = 0, nLocal = 0, sumC = 0, sumR = 0, sumRem_iter = 0;
    int nfail = 0; long long nchanged = 0, nforced = 0;
    for (;;) {
        double el = cpu_now() - t0;
        if (el >= budget) break;
        if (el >= next_log) {
            next_log += 20.0;
            fprintf(stderr, "t=%.0f it=%lld K=%d best=%d avgC=%.1f avgRem=%.1f local=%lld exact=%lld abort=%lld ils=%lld nodes=%lld impr=%lld\n",
                    el, iter, K, bestK, iter ? (double)sumC / iter : 0.0, iter ? (double)sumR / iter : 0.0, nLocal,
                    g_exact, g_abort, g_ils, g_nodes, nimp);
        }
        iter++;
        int K_before = K;
        int ist = (int)iter;

        /* 1. choose blocks */
        int nch = 0, done = 0, kind = 0;
        int k = KMIN + rndint(KMAX - KMIN + 1);
        if (BIGK > KMAX && rndint(100) < PBIG) k = KMAX + 1 + rndint(BIGK - KMAX);
        if (rndint(100) < PLOC) {
            for (int tries = 0; tries < 50 && !done; tries++) {
                int v0 = -1;
                for (int t = 0; t < 200000; t++) {
                    int c = rndint(M);
                    if (!inS[c] && conf[c] >= 1 && conf[c] <= LCF) { v0 = c; break; }
                }
                if (v0 < 0) break;
                bepoch++; nch = 0;
                for (int j = 0; j < deg[v0]; j++) {
                    int u = adj[v0][j];
                    if (inS[u]) { int b = blk[u]; if (bstamp[b] != bepoch) { bstamp[b] = bepoch; chosen[nch++] = b; } }
                }
                if (nch == 0 || nch > k) continue;
                for (int t = 0; nch < k && t < 40 * k; t++) {
                    int x = adj[v0][rndint(deg[v0])];
                    if (inS[x]) continue;
                    int y = adj[x][rndint(deg[x])];
                    if (!inS[y]) continue;
                    int b = blk[y];
                    if (bstamp[b] != bepoch) { bstamp[b] = bepoch; chosen[nch++] = b; }
                }
                done = 1; kind = 1; nLocal++;
            }
        }
        if (!done) {
            bepoch++; nch = 0;
            for (int t = 0; nch < k && t < 50 * k; t++) {
                int u = Sl[rndint(K)]; int b = blk[u];
                if (bstamp[b] != bepoch) { bstamp[b] = bepoch; chosen[nch++] = b; }
            }
        }
        (void)kind;

        /* 2. remove the S-vertices of the chosen blocks */
        int nrem = 0;
        for (int c = 0; c < nch; c++) {
            int b = chosen[c];
            for (int t = blkoff[b]; t < blkoff[b + 1]; t++) {
                int u = blkmem[t];
                if (inS[u]) { rem_v(u); remv[nrem++] = u; remstamp[u] = ist; }
            }
        }

        /* 3. free set C and its CSR graph */
        int nC = 0;
        for (int x = 0; x < M; x++)
            if (!inS[x] && conf[x] == 0) { cmark[x] = ist; loc[x] = nC; Cl[nC++] = x; }
        int nE2 = 0;
        for (int i = 0; i < nC; i++) {
            lst[i] = nE2;
            int c = Cl[i];
            for (int j = 0; j < deg[c]; j++) { int u = adj[c][j]; if (cmark[u] == ist) lnb[nE2++] = loc[u]; }
        }
        lst[nC] = nE2;
        sumC += nC; sumR += nrem; sumRem_iter++;

        /* 4. refill each connected component of G[C] */
        int iter_changed = 0;
        for (int i = 0; i < nC; i++) compId[i] = -1;
        int ncomp = 0;
        for (int s = 0; s < nC; s++) {
            if (compId[s] >= 0) continue;
            int qh = 0, qt = 0;
            queue[qt++] = s; compId[s] = ncomp;
            while (qh < qt) {
                int x = queue[qh++];
                for (int j = lst[x]; j < lst[x + 1]; j++) {
                    int y = lnb[j];
                    if (compId[y] < 0) { compId[y] = ncomp; queue[qt++] = y; }
                }
            }
            for (int i = qt - 1; i > 0; i--) { int r = rndint(i + 1); int tmp = queue[i]; queue[i] = queue[r]; queue[r] = tmp; }
            for (int j = 0; j < qt; j++) subidx[queue[j]] = j;
            int ne = 0; sst[0] = 0;
            for (int j = 0; j < qt; j++) {
                int x = queue[j];
                for (int t = lst[x]; t < lst[x + 1]; t++) { int y = lnb[t]; if (compId[y] == ncomp) snb[ne++] = subidx[y]; }
                sst[j + 1] = ne;
                isrem[j] = (remstamp[Cl[x]] == ist) ? 1 : 0;
            }
            int sn = -1;
            if (PX > 0 && rndint(100) < PX) {          /* forced variant: exclude one removed vertex */
                int nr = 0;
                for (int j = 0; j < qt; j++) if (isrem[j]) nr++;
                if (nr > 0) {
                    int pick = rndint(nr), excl = -1;
                    for (int j = 0; j < qt; j++) if (isrem[j]) { if (pick-- == 0) { excl = j; break; } }
                    sn = solve_comp(qt, sst, snb, isrem, sol_out, excl);
                    if (sn >= 0) nforced++;
                }
            }
            if (sn < 0) sn = solve_comp(qt, sst, snb, isrem, sol_out, -1);
            for (int t = 0; t < sn; t++) {
                int gx = Cl[queue[sol_out[t]]];
                if (remstamp[gx] != ist) iter_changed = 1;
                add_v(gx);
            }
            ncomp++;
        }
        /* 5. safety: keep the set maximal */
        for (int i = 0; i < nC; i++) { int x = Cl[i]; if (!inS[x] && conf[x] == 0) add_v(x); }

        if (K < K_before) { fprintf(stderr, "INTERNAL: set shrank %d -> %d\n", K_before, K); return 3; }
        if (K == K_before) nfail++;
        nchanged += iter_changed;
        if (K > bestK) {
            if (!verify_set(Sl, K)) { fprintf(stderr, "INTERNAL: invalid set\n"); return 2; }
            bestK = K;
            memcpy(bestSol, Sl, sizeof(int) * K);
            save_sol(of, bestSol, K);
            nimp++;
            fprintf(stderr, "IMPROVED t=%.1f K=%d it=%lld\n", el, K, iter);
        }
    }
    double el = cpu_now() - t0;
    if (!verify_set(bestSol, bestK)) { fprintf(stderr, "INTERNAL: final best invalid\n"); return 2; }
    save_sol(of, bestSol, bestK);
    fprintf(stderr, "END t=%.1f it=%lld best=%d last=%d avgC=%.1f avgRem=%.1f local=%lld exact=%lld abort=%lld ils=%lld nodes=%lld impr=%lld plateau_moves=%d changed=%lld forced=%lld\n",
            el, iter, bestK, K, iter ? (double)sumC / iter : 0.0, iter ? (double)sumR / iter : 0.0, nLocal,
            g_exact, g_abort, g_ils, g_nodes, nimp, nfail, nchanged, nforced);
    if (g_check) fprintf(stderr, "CHECK: exact comps checked=%lld bugs=%lld ils_suboptimal=%lld\n", g_checked, g_bug, g_ilssub);
    printf("best %d\n", bestK);
    return 0;
}
