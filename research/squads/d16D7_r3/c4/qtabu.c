/* qtabu.c: k-fixed penalty tabu search on a weighted quotient graph (card c4, squad d16D7_r3).
 *
 * usage: qtabu QUOT OUT CPU_SECONDS RNG_SEED [SEED|-] [STALL_ITERS]
 *   QUOT: "n", then per vertex "w deg nbr1 ... nbr_deg" (quotient ids 0..n-1, as written by ogquot.py).
 *   HW = max weight (3 for qh_pts / qh_lines). The search runs on the heavy vertices (w == HW) only, with the
 *   k-fixed penalty tabu of ktabu.c: S is a k-set, f = number of edges inside S, a move swaps u in S for v outside S
 *   (buckets by conflict count, tabu tenures, aspiration, elite restore on stall). Whenever f == 0 at size K, S is
 *   completed by a maximum-weight independent set of the light vertices (w < HW) with no neighbour in S (branch and
 *   bound on bitmasks, <= 64 candidates; greedy beyond that), and the total HW*K + light weight is compared with the
 *   best so far. OUT receives the best quotient solution (ids, one per line, atomic rename) whenever the total improves.
 *   SEED: optional file of quotient ids (heavy members are used; "-" = start from empty, i.e. greedy growth).
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

static int nq, HW, nh, nl;
static int *qw, *qdeg, **qnb;      /* quotient graph */
static int *hid, *lid, *hq, *lq;   /* quotient id -> heavy index / light index; heavy index -> quotient id; light -> q */
static int *deg, **nb;             /* heavy-induced graph (heavy indices) */
static int *conf, *inS, *nxt, *prv;
static int *headv[2];
static int *Sl, *Spos, K;
static int f;
static long long it;
static long long *tabuE, *tabuL;
static int *Ul, *Vl;
static int D;
static uint64_t rs = 88172645463325252ULL;
static long long bestTotal = -1;
static int bestK = 0;
static const char *outf;

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
    for (int x = 0; x < nh; x++) {
        int c = 0;
        for (int j = 0; j < deg[x]; j++) c += inS[nb[x][j]];
        if (c != conf[x]) return 0;
        if (inS[x]) tot += c;
    }
    return tot == 2LL * f;
}

/* ---- light completion: maximum-weight independent set of the lights with no neighbour in S ---- */
static int *cidx, *cq, ncand;
static uint64_t cadj[64];
static int cw[64];
static uint64_t bbSet;
static int bbBest;
static long long bbNodes;

static void bb(uint64_t cand, int cur, uint64_t cs) {
    if (++bbNodes > 20000000LL) return;
    if (cand == 0) { if (cur > bbBest) { bbBest = cur; bbSet = cs; } return; }
    int ub = cur;
    for (uint64_t m = cand; m; m &= m - 1) ub += cw[__builtin_ctzll(m)];
    if (ub <= bbBest) return;
    int v = __builtin_ctzll(cand);
    uint64_t bit = 1ULL << v;
    bb(cand & ~cadj[v] & ~bit, cur + cw[v], cs | bit);
    bb(cand & ~bit, cur, cs);
}

static void save_list(const char *of, const int *ids, int k) {
    char tmp[1024];
    snprintf(tmp, sizeof tmp, "%s.tmp", of);
    FILE *o = fopen(tmp, "w");
    if (!o) { perror(tmp); exit(4); }
    for (int i = 0; i < k; i++) fprintf(o, "%d\n", ids[i]);
    fclose(o);
    rename(tmp, of);
}

static int *outbuf;
static char *chosen;

/* called when S (size K, independent) is found: complete with lights, record the best total */
static void record(void) {
    ncand = 0;
    for (int j = 0; j < nl; j++) {
        int q = lq[j], ok = 1;
        for (int t = 0; t < qdeg[q]; t++) { int u = qnb[q][t]; if (hid[u] >= 0 && inS[hid[u]]) { ok = 0; break; } }
        if (ok) { cidx[q] = ncand; cq[ncand++] = q; }
    }
    long long lt = 0;
    for (int i = 0; i < ncand; i++) chosen[i] = 0;
    if (ncand <= 64) {
        for (int i = 0; i < ncand; i++) {
            cadj[i] = 0; cw[i] = qw[cq[i]];
            int q = cq[i];
            for (int t = 0; t < qdeg[q]; t++) { int u = qnb[q][t]; if (cidx[u] >= 0) cadj[i] |= 1ULL << cidx[u]; }
        }
        bbSet = 0; bbBest = 0; bbNodes = 0;
        uint64_t all = ncand == 64 ? ~0ULL : ((1ULL << ncand) - 1);
        bb(all, 0, 0);
        for (int i = 0; i < ncand; i++) if (bbSet >> i & 1) { chosen[i] = 1; }
        lt = bbBest;
    } else {
        /* greedy by candidate degree (ascending) */
        int *cdeg = malloc(sizeof(int) * (ncand + 1));
        int *ord = malloc(sizeof(int) * (ncand + 1));
        char *blk = calloc(ncand + 1, 1);
        for (int i = 0; i < ncand; i++) {
            int q = cq[i], c = 0;
            for (int t = 0; t < qdeg[q]; t++) if (cidx[qnb[q][t]] >= 0) c++;
            cdeg[i] = c; ord[i] = i;
        }
        for (int i = 1; i < ncand; i++) { int x = ord[i], j = i; while (j > 0 && cdeg[ord[j-1]] > cdeg[x]) { ord[j] = ord[j-1]; j--; } ord[j] = x; }
        for (int a = 0; a < ncand; a++) {
            int i = ord[a];
            if (blk[i]) continue;
            chosen[i] = 1; lt += qw[cq[i]];
            int q = cq[i];
            for (int t = 0; t < qdeg[q]; t++) { int u = qnb[q][t]; if (cidx[u] >= 0) blk[cidx[u]] = 1; }
        }
        free(cdeg); free(ord); free(blk);
    }
    long long total = (long long)HW * K + lt;
    if (total > bestTotal) {
        bestTotal = total;
        int m = 0;
        for (int i = 0; i < K; i++) outbuf[m++] = hq[Sl[i]];
        for (int i = 0; i < ncand; i++) if (chosen[i]) outbuf[m++] = cq[i];
        save_list(outf, outbuf, m);
        fprintf(stderr, "RECORD heavy=%d lights=%lld total=%lld (%d ids)\n", K, lt, total, m);
    }
    for (int i = 0; i < ncand; i++) cidx[cq[i]] = -1;
    if (K > bestK) bestK = K;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: qtabu QUOT OUT CPU_SECONDS RNG_SEED [SEED|-] [STALL_ITERS]\n");
        return 1;
    }
    const char *qf = argv[1];
    outf = argv[2];
    double budget = atof(argv[3]);
    rs ^= (uint64_t)strtoull(argv[4], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 50; i++) rnd64();
    const char *sf = argc > 5 ? argv[5] : "-";
    long long STALL = argc > 6 ? atoll(argv[6]) : 2000000LL;

    FILE *fp = fopen(qf, "r");
    if (!fp) { perror(qf); return 1; }
    if (fscanf(fp, "%d", &nq) != 1) return 1;
    qw = malloc(sizeof(int) * nq); qdeg = malloc(sizeof(int) * nq); qnb = malloc(sizeof(int *) * nq);
    HW = 0;
    for (int i = 0; i < nq; i++) {
        if (fscanf(fp, "%d %d", &qw[i], &qdeg[i]) != 2) { fprintf(stderr, "bad quotient line %d\n", i); return 1; }
        qnb[i] = malloc(sizeof(int) * (qdeg[i] + 1));
        for (int j = 0; j < qdeg[i]; j++) if (fscanf(fp, "%d", &qnb[i][j]) != 1) return 1;
        if (qw[i] > HW) HW = qw[i];
    }
    fclose(fp);
    hid = malloc(sizeof(int) * nq); lid = malloc(sizeof(int) * nq);
    nh = 0; nl = 0;
    for (int i = 0; i < nq; i++) {
        if (qw[i] == HW) { hid[i] = nh++; lid[i] = -1; }
        else { hid[i] = -1; lid[i] = nl++; }
    }
    hq = malloc(sizeof(int) * (nh + 1)); lq = malloc(sizeof(int) * (nl + 1));
    for (int i = 0; i < nq; i++) { if (hid[i] >= 0) hq[hid[i]] = i; else lq[lid[i]] = i; }
    deg = calloc(nh, sizeof(int));
    nb = malloc(sizeof(int *) * nh);
    int maxdeg = 0;
    for (int h = 0; h < nh; h++) {
        int q = hq[h], c = 0;
        for (int j = 0; j < qdeg[q]; j++) if (hid[qnb[q][j]] >= 0) c++;
        nb[h] = malloc(sizeof(int) * (c + 1));
        for (int j = 0; j < qdeg[q]; j++) { int u = qnb[q][j]; if (hid[u] >= 0) nb[h][deg[h]++] = hid[u]; }
        if (deg[h] > maxdeg) maxdeg = deg[h];
    }
    D = maxdeg + 2;
    fprintf(stderr, "quotient n=%d heavy(w=%d)=%d light=%d heavy-maxdeg=%d\n", nq, HW, nh, nl, maxdeg);

    conf = calloc(nh, sizeof(int));
    inS = calloc(nh, sizeof(int));
    nxt = malloc(sizeof(int) * nh);
    prv = malloc(sizeof(int) * nh);
    headv[0] = malloc(sizeof(int) * D);
    headv[1] = malloc(sizeof(int) * D);
    for (int c = 0; c < D; c++) headv[0][c] = headv[1][c] = -1;
    Sl = malloc(sizeof(int) * nh);
    Spos = malloc(sizeof(int) * nh);
    tabuE = calloc(nh, sizeof(long long));
    tabuL = calloc(nh, sizeof(long long));
    Ul = malloc(sizeof(int) * nh);
    Vl = malloc(sizeof(int) * nh);
    cidx = malloc(sizeof(int) * nq);
    for (int i = 0; i < nq; i++) cidx[i] = -1;
    cq = malloc(sizeof(int) * (nl + 1));
    outbuf = malloc(sizeof(int) * (nq + 1));
    chosen = malloc(nl + 2);
    K = 0; f = 0; it = 0;
    for (int x = 0; x < nh; x++) bl_insert(x);

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
    if (nh > 0) add_v(pick_min_outside());
    fprintf(stderr, "start k=%d f=%d\n", K, f);

    int *elite = malloc(sizeof(int) * nh);
    int eliteK = K;
    memcpy(elite, Sl, sizeof(int) * K);
    int bestf = f;
    long long last_improve = 0, nrest = 0;
    double t0 = cpu_now(), next_log = 30.0;

    for (;;) {
        it++;
        if ((it & 1023) == 0) {
            double el = cpu_now() - t0;
            if (el >= budget) break;
            if (el >= next_log) {
                next_log += 30.0;
                if (!check_state()) { fprintf(stderr, "INTERNAL STATE ERROR\n"); return 3; }
                fprintf(stderr, "t=%.0f k=%d f=%d bestf=%d it=%lld restarts=%lld bestTotal=%lld\n",
                        el, K, f, bestf, it, nrest, bestTotal);
            }
        }
        if (f == 0) {
            if (!verify_indep()) { fprintf(stderr, "INTERNAL: S not independent\n"); return 2; }
            record();
            fprintf(stderr, "FOUND heavy independent set k=%d t=%.1f it=%lld\n", K, cpu_now() - t0, it);
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
                do vv = rndint(nh); while (inS[vv]);
                rem_v(uu);
                add_v(vv);
            }
            last_improve = it;
            nrest++;
        }
    }
    double el = cpu_now() - t0;
    fprintf(stderr, "END t=%.1f bestK=%d bestTotal=%lld last_k=%d bestf(k)=%d it=%lld restarts=%lld\n",
            el, bestK, bestTotal, K, bestf, it, nrest);
    printf("bestTotal %lld bestK %d\n", bestTotal, bestK);
    return 0;
}
