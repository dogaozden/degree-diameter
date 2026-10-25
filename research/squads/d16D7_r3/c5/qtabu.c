/* qtabu.c: k-fixed penalty tabu search on the heavy part of a weighted quotient graph (card c5, squad d16D7_r3).
 *
 * usage: qtabu QUOT SEEDQ OUTQ CPU_SECONDS RNG_SEED [STALL_ITERS]
 *
 * QUOT: "n", then per quotient vertex "w deg nbr_1 ... nbr_deg" (quot/qhF_pts.txt format).
 * SEEDQ: quotient vertex ids (one per line); its heavy vertices start the search (must be independent).
 * Heavy = weight equal to the largest weight (3 here), light = the others (weight 1 here).
 * The k-fixed tabu search of ktabu.c (round 2, card c2) runs on the heavy induced subgraph. Every time it reaches an
 * independent heavy set S (f == 0), the light vertices with no neighbour in S are filled by a maximum independent set
 * (exact branch and bound on the free light vertices; greedy if there are more than 64 light vertices). The total
 * weight sum_w(S) + fill is compared with the best so far, and the best quotient solution is written to OUTQ (atomic
 * rename), after an independence check on the full quotient.
 * f == 0 at level k leads to level k+1 (add the outside heavy vertex with the fewest conflicts), as in ktabu.c.
 * CPU time is measured with CLOCK_PROCESS_CPUTIME_ID.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

static int n, D;                  /* n: number of heavy vertices */
static int *hv, *Wh;              /* heavy index -> quotient id, weight */
static int *deg, **nb;            /* heavy-induced adjacency (heavy indices) */
static int *hdeg, **hlnb;         /* heavy -> light neighbours (light indices) */
static int nL, *lv, *lconf;       /* light index -> quotient id; lconf[l] = |N(l) cap S| */
static int *ldeg, **lln;          /* light-light adjacency lists */
static uint64_t *lmask;           /* light-light adjacency bit masks (nL <= 64) */
static int *conf, *inS, *nxt, *prv;
static int *headv[2];             /* headv[g][c]: first vertex of group g (0 outside, 1 in S) with conf == c */
static int *Sl, *Spos, K;         /* members of S, positions in Sl, |S| */
static int f;                     /* edges inside S */
static long long it;
static long long *tabuE, *tabuL;
static int *Ul, *Vl;
static int NQ, WMAX;
static int *W_all, *DEGQ, **NBQ;  /* full quotient */
static const char *OUTQ;
static long long best_total = -1;
static double t0;
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
    for (int j = 0; j < hdeg[v]; j++) lconf[hlnb[v][j]]++;
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
    for (int j = 0; j < hdeg[u]; j++) lconf[hlnb[u][j]]--;
}

/* outside heavy vertex with the fewest neighbours in S (random among ties, tabu ignored) */
static int pick_min_outside(void) {
    int cnt = 0;
    for (int c = 0; c < D && cnt == 0; c++)
        for (int x = headv[0][c]; x >= 0; x = nxt[x]) Vl[cnt++] = x;
    return Vl[rndint(cnt)];
}

/* best swap among non-tabu candidates (allow != 0: tabu ignored). Returns 0 if no swap exists. */
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

/* full recomputation of conf, f and lconf: returns 1 if the incremental state is consistent */
static int check_state(void) {
    long long tot = 0;
    for (int x = 0; x < n; x++) {
        int c = 0;
        for (int j = 0; j < deg[x]; j++) c += inS[nb[x][j]];
        if (c != conf[x]) return 0;
        if (inS[x]) tot += c;
    }
    if (tot != 2LL * f) return 0;
    for (int l = 0; l < nL; l++) {
        int c = 0;
        for (int i = 0; i < K; i++) for (int j = 0; j < hdeg[Sl[i]]; j++) if (hlnb[Sl[i]][j] == l) c++;
        if (c != lconf[l]) return 0;
    }
    return 1;
}

/* maximum independent set among the free light vertices (lconf == 0), exact by branch and bound on bit masks */
static uint64_t mis_best; static int mis_bestsz;
static void mis_rec(uint64_t P, uint64_t cur, int sz) {
    if (sz + __builtin_popcountll(P) <= mis_bestsz) return;
    if (!P) { mis_bestsz = sz; mis_best = cur; return; }
    int v = -1, dv = 1 << 30;
    for (uint64_t Q = P; Q; Q &= Q - 1) {
        int u = __builtin_ctzll(Q);
        int d = __builtin_popcountll(lmask[u] & P);
        if (d < dv) { dv = d; v = u; }
    }
    mis_rec(P & ~lmask[v] & ~(1ULL << v), cur | (1ULL << v), sz + 1);   /* include v */
    mis_rec(P & ~(1ULL << v), cur, sz);                                  /* exclude v */
}

static int eval_fill(int *chosen) {
    int nf = 0;
    if (nL <= 64) {
        uint64_t P = 0;
        for (int l = 0; l < nL; l++) if (lconf[l] == 0) P |= 1ULL << l;
        mis_bestsz = 0; mis_best = 0;
        mis_rec(P, 0, 0);
        for (int l = 0; l < nL; l++) if ((mis_best >> l) & 1) chosen[nf++] = l;
    } else {                       /* greedy: free light vertex with fewest free light neighbours */
        char *fr = malloc(nL);
        for (int l = 0; l < nL; l++) fr[l] = (lconf[l] == 0);
        for (;;) {
            int bl = -1, bd = 1 << 30;
            for (int l = 0; l < nL; l++) if (fr[l]) {
                int d = 0;
                for (int j = 0; j < ldeg[l]; j++) d += fr[lln[l][j]];
                if (d < bd) { bd = d; bl = l; }
            }
            if (bl < 0) break;
            chosen[nf++] = bl; fr[bl] = 0;
            for (int j = 0; j < ldeg[bl]; j++) fr[lln[bl][j]] = 0;
        }
        free(fr);
    }
    return nf;
}

static void save_quot(const char *of, const int *ids, int cnt) {
    char tmp[1024];
    snprintf(tmp, sizeof tmp, "%s.tmp", of);
    FILE *o = fopen(tmp, "w");
    if (!o) { perror(tmp); exit(4); }
    for (int i = 0; i < cnt; i++) fprintf(o, "%d\n", ids[i]);
    fclose(o);
    rename(tmp, of);
}

static void record(void) {
    int *chosen = malloc(sizeof(int) * (nL > 0 ? nL : 1));
    int nl = eval_fill(chosen);
    long long tot = 0;
    for (int i = 0; i < K; i++) tot += Wh[Sl[i]];
    for (int j = 0; j < nl; j++) tot += W_all[lv[chosen[j]]];
    if (tot > best_total) {
        int cnt = K + nl;
        int *ids = malloc(sizeof(int) * cnt);
        int c = 0;
        for (int i = 0; i < K; i++) ids[c++] = hv[Sl[i]];
        for (int j = 0; j < nl; j++) ids[c++] = lv[chosen[j]];
        char *mark = calloc(NQ, 1);
        for (int i = 0; i < cnt; i++) mark[ids[i]] = 1;
        int ok = 1;
        for (int i = 0; i < cnt && ok; i++)
            for (int j = 0; j < DEGQ[ids[i]]; j++) if (mark[NBQ[ids[i]][j]]) { ok = 0; break; }
        free(mark);
        if (ok) {
            save_quot(OUTQ, ids, cnt);
            best_total = tot;
        } else fprintf(stderr, "INTERNAL: quotient solution not independent, not saved\n");
        free(ids);
    }
    fprintf(stderr, "FOUND k=%d light=%d total=%lld best=%lld t=%.1f it=%lld\n",
            K, nl, tot, best_total, cpu_now() - t0, it);
    free(chosen);
}

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: qtabu QUOT SEEDQ OUTQ CPU_SECONDS RNG_SEED [STALL_ITERS]\n");
        return 1;
    }
    const char *qf = argv[1], *sf = argv[2];
    OUTQ = argv[3];
    double budget = atof(argv[4]);
    rs ^= (uint64_t)strtoull(argv[5], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 50; i++) rnd64();
    long long STALL = argc > 6 ? atoll(argv[6]) : 3000000LL;

    FILE *fp = fopen(qf, "r");
    if (!fp) { perror(qf); return 1; }
    if (fscanf(fp, "%d", &NQ) != 1) return 1;
    W_all = malloc(sizeof(int) * NQ);
    DEGQ = malloc(sizeof(int) * NQ);
    NBQ = malloc(sizeof(int *) * NQ);
    WMAX = 0;
    for (int x = 0; x < NQ; x++) {
        int w, dg;
        if (fscanf(fp, "%d %d", &w, &dg) != 2) { fprintf(stderr, "bad quotient line %d\n", x); return 1; }
        W_all[x] = w; DEGQ[x] = dg;
        NBQ[x] = malloc(sizeof(int) * (dg > 0 ? dg : 1));
        for (int j = 0; j < dg; j++) if (fscanf(fp, "%d", &NBQ[x][j]) != 1) return 1;
        if (w > WMAX) WMAX = w;
    }
    fclose(fp);

    int *hid = malloc(sizeof(int) * NQ), *lid = malloc(sizeof(int) * NQ);
    n = 0; nL = 0;
    for (int x = 0; x < NQ; x++) {
        if (W_all[x] == WMAX) { hid[x] = n++; lid[x] = -1; }
        else { lid[x] = nL++; hid[x] = -1; }
    }
    hv = malloc(sizeof(int) * (n > 0 ? n : 1));
    Wh = malloc(sizeof(int) * (n > 0 ? n : 1));
    lv = malloc(sizeof(int) * (nL > 0 ? nL : 1));
    for (int x = 0; x < NQ; x++) {
        if (hid[x] >= 0) { hv[hid[x]] = x; Wh[hid[x]] = W_all[x]; }
        else lv[lid[x]] = x;
    }
    deg = calloc(n, sizeof(int)); nb = malloc(sizeof(int *) * n);
    hdeg = calloc(n, sizeof(int)); hlnb = malloc(sizeof(int *) * n);
    ldeg = calloc(nL > 0 ? nL : 1, sizeof(int)); lln = malloc(sizeof(int *) * (nL > 0 ? nL : 1));
    lconf = calloc(nL > 0 ? nL : 1, sizeof(int));
    lmask = calloc(nL > 0 ? nL : 1, sizeof(uint64_t));
    for (int x = 0; x < NQ; x++) {
        int ch = 0, cl = 0;
        for (int j = 0; j < DEGQ[x]; j++) { int y = NBQ[x][j]; if (hid[y] >= 0) ch++; else cl++; }
        if (hid[x] >= 0) {
            int h = hid[x], a = 0, b = 0;
            nb[h] = malloc(sizeof(int) * (ch > 0 ? ch : 1));
            hlnb[h] = malloc(sizeof(int) * (cl > 0 ? cl : 1));
            for (int j = 0; j < DEGQ[x]; j++) {
                int y = NBQ[x][j];
                if (hid[y] >= 0) nb[h][a++] = hid[y];
                else hlnb[h][b++] = lid[y];
            }
            deg[h] = a; hdeg[h] = b;
        } else {
            int l = lid[x], a = 0;
            lln[l] = malloc(sizeof(int) * (cl > 0 ? cl : 1));
            for (int j = 0; j < DEGQ[x]; j++) {
                int y = NBQ[x][j];
                if (hid[y] < 0) lln[l][a++] = lid[y];
            }
            ldeg[l] = a;
            if (nL <= 64) for (int j = 0; j < a; j++) lmask[l] |= 1ULL << lln[l][j];
        }
    }
    int maxdeg = 0;
    for (int h = 0; h < n; h++) if (deg[h] > maxdeg) maxdeg = deg[h];
    D = maxdeg + 2;
    fprintf(stderr, "quotient %d vertices: heavy %d (weight %d), light %d\n", NQ, n, WMAX, nL);

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

    FILE *sp = fopen(sf, "r");
    if (!sp) { perror(sf); return 1; }
    int v, s0 = 0;
    while (fscanf(sp, "%d", &v) == 1) {
        if (v >= 0 && v < NQ && hid[v] >= 0 && !inS[hid[v]]) { add_v(hid[v]); s0++; }
    }
    fclose(sp);
    fprintf(stderr, "seed heavy size %d f(seed)=%d\n", K, f);

    t0 = cpu_now();
    if (f == 0) record();
    add_v(pick_min_outside());
    fprintf(stderr, "start k=%d f=%d\n", K, f);

    int *elite = malloc(sizeof(int) * n);
    int eliteK = K;
    memcpy(elite, Sl, sizeof(int) * K);
    int bestf = f;
    long long last_improve = 0, nrest = 0;
    double next_log = 30.0;

    for (;;) {
        it++;
        if ((it & 1023) == 0) {
            double el = cpu_now() - t0;
            if (el >= budget) break;
            if (el >= next_log) {
                next_log += 30.0;
                if (!check_state()) { fprintf(stderr, "INTERNAL STATE ERROR\n"); return 3; }
                fprintf(stderr, "t=%.0f k=%d f=%d bestf=%d best_total=%lld it=%lld restarts=%lld\n",
                        el, K, f, bestf, best_total, it, nrest);
            }
        }
        if (f == 0) {
            if (!verify_indep()) { fprintf(stderr, "INTERNAL: S not independent\n"); return 2; }
            record();
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
    fprintf(stderr, "END t=%.1f best_total=%lld last_k=%d bestf(k)=%d it=%lld restarts=%lld\n",
            el, best_total, K, bestf, it, nrest);
    printf("best_total %lld\n", best_total);
    return 0;
}
