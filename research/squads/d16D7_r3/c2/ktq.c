/* ktq.c: k-fixed penalty tabu search on a weighted quotient graph (card c2, squad d16D7_r3). Adapted from ktabu.c.
 *
 * usage: ktq QUOT SEED OUT CPU_SECONDS RNG_SEED [STALL_ITERS]
 *   QUOT:  "n", then per vertex "w deg nbr1 ... nbr_deg" (quotient ids 0..n-1, w = orbit size).
 *   SEED:  quotient ids (one per line); only its heavy members are used as a start. "-" = empty start.
 *   OUT:   best total-weight solution under the greedy light fill (quotient ids, one per line, atomic rename).
 *   OUT.exact: best total-weight solution under the exact light fill (same format).
 *
 * Heavy vertices are those of maximum weight (9 for the q9 quotients). The k-fixed tabu of ktabu.c runs on the
 * subgraph induced by the heavy vertices, UNWEIGHTED: k = number of heavy vertices in S, f = heavy-heavy edges in S.
 * Each time f == 0 (a conflict-free heavy set S with |S| = k), the light vertices (weight 3, 1) with no neighbour in S
 * are added to S in two ways, and the total weight 9k + (light weight) is logged:
 *   greedy: repeatedly take the candidate of largest weight, ties broken by the fewest remaining candidate
 *           neighbours, random ties; GREEDY_TRIES randomized runs, the best is kept (the brief's fill);
 *   exact:  maximum-weight independent set of the candidates (branch and bound; at most 64 light vertices).
 * The best totals are written to OUT and OUT.exact when they improve; then k grows exactly as in ktabu.c.
 * Stall: as ktabu.c (elite restore + 3..10 random swaps after STALL_ITERS iterations without a new best f at this k).
 * CPU time is measured with CLOCK_PROCESS_CPUTIME_ID.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define GREEDY_TRIES 200

/* quotient */
static int nq, WH, H, NL;
static int *qw, *qdeg, **qnb;
static int *hid, *hv;              /* quotient id -> heavy index (-1 if light); heavy index -> quotient id */
static int *lid, *lv, *lw;         /* quotient id -> light index (-1 if heavy); light index -> quotient id, weight */
static int *lhdeg, **lhn;          /* light -> heavy neighbours (heavy indices) */
static uint64_t *lmask;            /* light -> bitmask of light neighbours */

/* heavy-induced graph (ktabu.c's n, deg, nb with n = H) */
static int n, D;
static int *deg, **nb;
static int *conf, *inS, *nxt, *prv;
static int *headv[2];              /* headv[g][c]: first vertex of group g (0 outside, 1 in S) with conf == c */
static int *Sl, *Spos, K;          /* members of S, their positions in Sl, and |S| */
static int f;                      /* number of edges inside S */
static long long it;
static long long *tabuE, *tabuL;
static int *Ul, *Vl;
static uint64_t rs = 88172645463325252ULL;

static inline uint64_t rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline int rndint(int m) { return (int)(rnd64() % (uint64_t)m); }

static double cpu_now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &ts);
    return ts.tv_sec + 1e-9 * ts.tv_nsec;
}

static inline void bl_remove(int x) {
    int g = inS[x], c = conf[x];
    if (prv[x] >= 0) nxt[prv[x]] = nxt[x];
    else headv[g][c] = nxt[x];
    if (nxt[x] >= 0) prv[nxt[x]] = prv[x];
}

static inline void bl_insert(int x) {
    int g = inS[x], c = conf[x];
    prv[x] = -1;
    nxt[x] = headv[g][c];
    if (nxt[x] >= 0) prv[nxt[x]] = x;
    headv[g][c] = x;
}

static void add_v(int v) {
    bl_remove(v);
    inS[v] = 1;
    bl_insert(v);
    Spos[v] = K;
    Sl[K++] = v;
    f += conf[v];
    for (int j = 0; j < deg[v]; j++) {
        int w = nb[v][j];
        bl_remove(w); conf[w]++; bl_insert(w);
    }
}

static void rem_v(int u) {
    bl_remove(u);
    inS[u] = 0;
    bl_insert(u);
    int p = Spos[u], last = Sl[--K];
    Sl[p] = last; Spos[last] = p;
    f -= conf[u];
    for (int j = 0; j < deg[u]; j++) {
        int w = nb[u][j];
        bl_remove(w); conf[w]--; bl_insert(w);
    }
}

static int pick_min_outside(void) {
    int cnt = 0;
    for (int c = 0; c < D && cnt == 0; c++)
        for (int x = headv[0][c]; x >= 0; x = nxt[x]) Vl[cnt++] = x;
    return Vl[rndint(cnt)];
}

static int pick_move(int allow, int *pu, int *pv, int *pd) {
    int nU = 0, nV = 0, cs = -1, co = -1;
    for (int c = D - 1; c >= 0 && nU == 0; c--) {
        for (int x = headv[1][c]; x >= 0; x = nxt[x])
            if (allow || tabuL[x] <= it) Ul[nU++] = x;
        if (nU) cs = c;
    }
    if (nU == 0) return 0;
    for (int c = 0; c < D && nV == 0; c++) {
        for (int x = headv[0][c]; x >= 0; x = nxt[x])
            if (allow || tabuE[x] <= it) Vl[nV++] = x;
        if (nV) co = c;
    }
    if (nV == 0) return 0;
    int start = rndint(nU);
    for (int i = 0; i < nU; i++) {
        int u = Ul[(start + i) % nU];
        int dg = deg[u];
        if (dg == 0) continue;
        int off = rndint(dg);
        for (int j = 0; j < dg; j++) {
            int v = nb[u][(off + j) % dg];
            if (!inS[v] && conf[v] == co && (allow || tabuE[v] <= it)) {
                *pu = u; *pv = v; *pd = co - 1 - cs;
                return 1;
            }
        }
    }
    *pu = Ul[rndint(nU)];
    *pv = Vl[rndint(nV)];
    *pd = co - cs;
    return 1;
}

static int verify_indep(void) {
    for (int i = 0; i < K; i++) {
        int u = Sl[i];
        if (!inS[u]) return 0;
        for (int j = 0; j < deg[u]; j++) if (inS[nb[u][j]]) return 0;
    }
    return 1;
}

static int check_state(void) {
    long long tot = 0;
    for (int x = 0; x < n; x++) {
        int c = 0;
        for (int j = 0; j < deg[x]; j++) c += inS[nb[x][j]];
        if (c != conf[x]) return 0;
        if (inS[x]) tot += c;
    }
    return tot == 2LL * f;
}

/* ---- light fill ---- */
static long long kG[256], kE[256];   /* best greedy / exact total per heavy count k */

static uint64_t light_avail(void) {
    uint64_t av = 0;
    for (int l = 0; l < NL; l++) {
        int blocked = 0;
        for (int j = 0; j < lhdeg[l]; j++) if (inS[lhn[l][j]]) { blocked = 1; break; }
        if (!blocked) av |= 1ULL << l;
    }
    return av;
}

static long long bbL; static uint64_t bbSet;
static void bb(uint64_t cand, long long cur, uint64_t chosen) {
    if (cur > bbL) { bbL = cur; bbSet = chosen; }
    if (!cand) return;
    long long ub = cur;
    for (uint64_t c = cand; c; c &= c - 1) ub += lw[__builtin_ctzll(c)];
    if (ub <= bbL) return;
    int bv = -1, bd = -1;
    for (uint64_t c = cand; c; c &= c - 1) {
        int v = __builtin_ctzll(c);
        int d = __builtin_popcountll(lmask[v] & cand);
        if (d > bd) { bd = d; bv = v; }
    }
    if (bd == 0) {                      /* candidates pairwise non-adjacent: take them all */
        long long s = cur;
        for (uint64_t c = cand; c; c &= c - 1) s += lw[__builtin_ctzll(c)];
        if (s > bbL) { bbL = s; bbSet = chosen | cand; }
        return;
    }
    bb(cand & ~lmask[bv] & ~(1ULL << bv), cur + lw[bv], chosen | (1ULL << bv));
    bb(cand & ~(1ULL << bv), cur, chosen);
}

static long long greedy_once(uint64_t avail, uint64_t *chosen) {
    uint64_t alive = avail, ch = 0;
    long long tot = 0;
    while (alive) {
        int best = -1, bw = -1, bdeg = 1 << 30, cnt = 0;
        for (uint64_t c = alive; c; c &= c - 1) {
            int v = __builtin_ctzll(c);
            int dg = __builtin_popcountll(lmask[v] & alive);
            if (lw[v] > bw || (lw[v] == bw && dg < bdeg)) { bw = lw[v]; bdeg = dg; best = v; cnt = 1; }
            else if (lw[v] == bw && dg == bdeg) { cnt++; if (rndint(cnt) == 0) best = v; }
        }
        ch |= 1ULL << best; tot += lw[best];
        alive &= ~lmask[best] & ~(1ULL << best);
    }
    *chosen = ch;
    return tot;
}

static void write_sol(const char *of, uint64_t lset) {
    char tmp[1100];
    snprintf(tmp, sizeof tmp, "%s.tmp", of);
    FILE *o = fopen(tmp, "w");
    if (!o) { perror(tmp); exit(4); }
    for (int i = 0; i < K; i++) fprintf(o, "%d\n", hv[Sl[i]]);
    for (int l = 0; l < NL; l++) if ((lset >> l) & 1) fprintf(o, "%d\n", lv[l]);
    fclose(o);
    rename(tmp, of);
}

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: ktq QUOT SEED OUT CPU_SECONDS RNG_SEED [STALL_ITERS]\n");
        return 1;
    }
    const char *qf = argv[1], *sf = argv[2], *of = argv[3];
    double budget = atof(argv[4]);
    rs ^= (uint64_t)strtoull(argv[5], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 50; i++) rnd64();
    long long STALL = argc > 6 ? atoll(argv[6]) : 3000000LL;
    long long RESTART = argc > 7 ? atoll(argv[7]) : 500000LL;   /* full restart after this many iterations w/o a new f==0 */
    char ofe[1100];
    snprintf(ofe, sizeof ofe, "%s.exact", of);

    /* quotient */
    FILE *fp = fopen(qf, "r");
    if (!fp) { perror(qf); return 1; }
    if (fscanf(fp, "%d", &nq) != 1) return 1;
    qw = malloc(sizeof(int) * nq); qdeg = malloc(sizeof(int) * nq); qnb = malloc(sizeof(int *) * nq);
    for (int i = 0; i < nq; i++) {
        if (fscanf(fp, "%d %d", &qw[i], &qdeg[i]) != 2) { fprintf(stderr, "bad line %d\n", i); return 1; }
        qnb[i] = malloc(sizeof(int) * (qdeg[i] + 1));
        for (int j = 0; j < qdeg[i]; j++) if (fscanf(fp, "%d", &qnb[i][j]) != 1) return 1;
    }
    fclose(fp);
    WH = 0;
    for (int i = 0; i < nq; i++) if (qw[i] > WH) WH = qw[i];
    H = 0;
    for (int i = 0; i < nq; i++) if (qw[i] == WH) H++;
    NL = nq - H;
    if (NL > 64) { fprintf(stderr, "too many light vertices (%d)\n", NL); return 1; }
    hid = malloc(sizeof(int) * nq); hv = malloc(sizeof(int) * H);
    lid = malloc(sizeof(int) * nq); lv = malloc(sizeof(int) * (NL + 1)); lw = malloc(sizeof(int) * (NL + 1));
    int h = 0, l = 0;
    for (int i = 0; i < nq; i++) {
        if (qw[i] == WH) { hid[i] = h; hv[h++] = i; lid[i] = -1; }
        else { lid[i] = l; lv[l] = i; lw[l++] = qw[i]; hid[i] = -1; }
    }
    n = H;
    deg = calloc(n, sizeof(int)); nb = malloc(sizeof(int *) * n);
    for (int a = 0; a < H; a++) {
        int q = hv[a], cnt = 0;
        nb[a] = malloc(sizeof(int) * (qdeg[q] + 1));
        for (int j = 0; j < qdeg[q]; j++) if (hid[qnb[q][j]] >= 0) nb[a][cnt++] = hid[qnb[q][j]];
        deg[a] = cnt;
    }
    lhdeg = calloc(NL + 1, sizeof(int)); lhn = malloc(sizeof(int *) * (NL + 1)); lmask = calloc(NL + 1, sizeof(uint64_t));
    for (int x = 0; x < NL; x++) {
        int q = lv[x];
        lhn[x] = malloc(sizeof(int) * (qdeg[q] + 1));
        for (int j = 0; j < qdeg[q]; j++) {
            int u = qnb[q][j];
            if (hid[u] >= 0) lhn[x][lhdeg[x]++] = hid[u];
            else lmask[x] |= 1ULL << lid[u];
        }
    }
    int maxdeg = 0;
    for (int a = 0; a < n; a++) if (deg[a] > maxdeg) maxdeg = deg[a];
    D = maxdeg + 2;

    conf = calloc(n, sizeof(int));
    inS = calloc(n, sizeof(int));
    nxt = malloc(sizeof(int) * n);
    prv = malloc(sizeof(int) * n);
    headv[0] = malloc(sizeof(int) * D);
    headv[1] = malloc(sizeof(int) * D);
    for (int c = 0; c < D; c++) headv[0][c] = headv[1][c] = -1;
    Sl = malloc(sizeof(int) * n);
    Spos = malloc(sizeof(int) * n);
    tabuE = calloc(n, sizeof(long long));
    tabuL = calloc(n, sizeof(long long));
    Ul = malloc(sizeof(int) * n);
    Vl = malloc(sizeof(int) * n);
    K = 0; f = 0; it = 0;
    for (int x = 0; x < n; x++) bl_insert(x);

    fprintf(stderr, "quotient n=%d weight=%d heavy=%d (induced maxdeg %d) light=%d\n", nq, WH, H, maxdeg, NL);

    /* optional seed: heavy members only */
    if (strcmp(sf, "-") != 0) {
        FILE *sp = fopen(sf, "r");
        if (!sp) { perror(sf); return 1; }
        int v;
        while (fscanf(sp, "%d", &v) == 1) {
            if (v >= 0 && v < nq && hid[v] >= 0 && !inS[hid[v]]) add_v(hid[v]);
        }
        fclose(sp);
        fprintf(stderr, "seed heavy size %d f(seed)=%d\n", K, f);
    }
    add_v(pick_min_outside());
    fprintf(stderr, "start k=%d f=%d\n", K, f);

    int *elite = malloc(sizeof(int) * n);
    int eliteK = K;
    memcpy(elite, Sl, sizeof(int) * K);
    int bestf = f;
    long long last_improve = 0, nrest = 0, last_success = 0, nevents = 0;
    long long bestG = -1, bestE = -1;
    int kbestG = 0, kbestE = 0;
    double t0 = cpu_now(), next_log = 30.0;

    for (;;) {
        it++;
        if ((it & 1023) == 0) {
            double el = cpu_now() - t0;
            if (el >= budget) break;
            if (el >= next_log) {
                next_log += 30.0;
                if (!check_state()) { fprintf(stderr, "INTERNAL STATE ERROR\n"); return 3; }
                fprintf(stderr, "t=%.0f k=%d f=%d bestf=%d it=%lld restarts=%lld events=%lld bestG=%lld bestE=%lld\n",
                        el, K, f, bestf, it, nrest, nevents, bestG, bestE);
            }
        }
        if (it - last_success > RESTART) {          /* full restart: a new random start vertex, S otherwise emptied */
            while (K > 0) rem_v(Sl[0]);
            add_v(rndint(n));
            bestf = f;
            eliteK = K;
            memcpy(elite, Sl, sizeof(int) * K);
            last_improve = it;
            last_success = it;
            nrest++;
            continue;
        }
        if (f == 0) {
            nevents++;
            last_success = it;
            if (!verify_indep()) { fprintf(stderr, "INTERNAL: S not independent\n"); return 2; }
            uint64_t av = light_avail();
            long long Wh = (long long)WH * K;
            long long gl = -1; uint64_t gset = 0;
            for (int t = 0; t < GREEDY_TRIES; t++) {
                uint64_t c = 0; long long s = greedy_once(av, &c);
                if (s > gl) { gl = s; gset = c; }
            }
            bbL = -1; bbSet = 0; bb(av, 0, 0);
            long long G = Wh + (gl < 0 ? 0 : gl), E = Wh + bbL;
            if (K < 256) { if (G > kG[K]) kG[K] = G; if (E > kE[K]) kE[K] = E; }
            if (G > bestG || E > bestE)
                fprintf(stderr, "FOUND k=%d heavy_w=%lld light_avail=%d greedy_total=%lld exact_total=%lld t=%.1f it=%lld\n",
                        K, Wh, __builtin_popcountll(av), G, E, cpu_now() - t0, it);
            if (G > bestG) { bestG = G; kbestG = K; write_sol(of, gset); }
            if (E > bestE) { bestE = E; kbestE = K; write_sol(ofe, bbSet); }
            add_v(pick_min_outside());
            bestf = f;
            eliteK = K;
            memcpy(elite, Sl, sizeof(int) * K);
            last_improve = it;
            continue;
        }

        int cs_all = -1, co_all = -1;
        for (int c = D - 1; c >= 0; c--) if (headv[1][c] >= 0) { cs_all = c; break; }
        for (int c = 0; c < D; c++) if (headv[0][c] >= 0) { co_all = c; break; }
        int u = -1, w = -1, d = 0, asp = 0;
        if (f + (co_all - cs_all - 1) < bestf) {
            if (pick_move(1, &u, &w, &d) && f + d < bestf) asp = 1;
        }
        if (!asp && !pick_move(0, &u, &w, &d)) pick_move(1, &u, &w, &d);
        if (u < 0 || w < 0) { fprintf(stderr, "no move\n"); return 5; }

        int nc = 0;
        for (int i = 0; i < K; i++) if (conf[Sl[i]] > 0) nc++;
        tabuE[u] = it + 7 + rndint(nc + 1);
        rem_v(u);
        add_v(w);
        tabuL[w] = it + 2 + rndint(4);

        if (f < bestf) {
            bestf = f;
            eliteK = K;
            memcpy(elite, Sl, sizeof(int) * K);
            last_improve = it;
        } else if (it - last_improve > STALL) {
            while (K > 0) rem_v(Sl[0]);
            for (int i = 0; i < eliteK; i++) add_v(elite[i]);
            int P = 3 + rndint(8);
            for (int p = 0; p < P; p++) {
                int uu = Sl[rndint(K)], vv;
                do vv = rndint(n); while (inS[vv]);
                rem_v(uu);
                add_v(vv);
            }
            last_improve = it;
            nrest++;
        }
    }
    double el = cpu_now() - t0;
    fprintf(stderr, "END t=%.1f bestG=%lld (k=%d) bestE=%lld (k=%d) it=%lld restarts=%lld events=%lld\n",
            el, bestG, kbestG, bestE, kbestE, it, nrest, nevents);
    printf("bestG %lld bestE %lld events %lld restarts %lld\n", bestG, bestE, nevents, nrest);
    printf("per-k max (k:greedy/exact):");
    for (int k = 1; k < 256; k++) if (kE[k] > 0) printf(" %d:%lld/%lld", k, kG[k], kE[k]);
    printf("\n");
    return 0;
}
