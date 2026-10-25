/* c6/lns.c: large-neighbourhood search with exact sub-solves for a maximum independent set of an orbit graph.
 *
 * usage: lns GRAPH SEED_SOL OUT_SOL CPU_BUDGET_S RNG_SEED [KMIN KMAX KMIN2 KMAX2 NODE_CAP]
 *
 * Each iteration removes a destroy set D of k solution vertices by one of three strategies, used in turn:
 *   0 random: k in [KMIN,KMAX] (default 15..40) random solution vertices;
 *   1 ball:   k in [KMIN2,KMAX2] (default 40..80): T(v) for a random non-solution vertex v, then repeatedly the solution
 *             vertices that share a non-solution neighbour of tightness <= 3 with D (local in the tightness structure);
 *   2 greedy: k in [KMIN2,KMAX2]: start from a random solution vertex and repeatedly add the solution vertex that
 *             would free the most non-solution vertices (vertices whose solution neighbours then all lie in D).
 * The candidate set C is D plus every non-solution vertex whose solution neighbours all lie in D. The maximum
 * independent set of G[C] is solved exactly (bitset branch and reduce: degree <= 1 reductions, max-degree branching,
 * greedy clique-cover bound) with a node cap; the search starts from lower bound |D|-1, so it returns a set of size
 * >= |D| (or D itself if the cap is hit first). The move is accepted when the solution does not shrink (plateau moves
 * change the set at equal size). The solution is saved at every improvement.
 * CPU time is measured with clock(); the run stops at CPU_BUDGET_S.
 */
#define _POSIX_C_SOURCE 200809L
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

typedef uint64_t u64;

#define MAXT 128          /* max solution neighbours stored per vertex */
#define MAXC 1024         /* max candidate-set size given to the exact solver */
#define MAXW (MAXC / 64)
#define MAXD 256          /* max destroy-set size */

static int M, E;
static int *aoff, *anb;   /* CSR adjacency */
static int *snb, *cnt;    /* snb[w*MAXT+i]: i-th solution neighbour of w; cnt[w]: how many */
static char *inS;         /* solution membership */
static int *slist, *spos, nsol;
static int *loc;          /* local index of a vertex inside the candidate set, -1 otherwise */
static u64 *mark, mstamp; /* scratch stamps */
static u64 *inD, dstamp;  /* inD[x] == dstamp  <=>  x is in the current destroy set */
static int *rr, *score;   /* greedy destroy: residual tightness, score of solution vertices */
static int *DV, nd;       /* destroy set */
static int *CV;           /* candidate set, global ids */
static int *perm, *cand;  /* scratch */
static int *TVbuf;        /* new solution part, global ids */
static int *gidC;         /* local -> global id for the exact solver */

static u64 ADJ[MAXC][MAXW];       /* local adjacency bitsets */
static u64 POOL[MAXC + 2][MAXW];  /* candidate bitset per recursion depth */
static int stk[MAXC + 2], sp;     /* vertices taken on the current path (local ids) */
static int bestN, bestCount, bestSetL[MAXC];
static long long nodes, nodeCap;
static int aborted, nC, W;

static long long it_n[3], it_D[3], it_C[3], it_Cmax[3], it_abort[3], it_impr[3], it_plat[3], it_skip[3];

static u64 rs = 88172645463325252ULL;
static inline u64 rnd64(void) { rs ^= rs >> 12; rs ^= rs << 25; rs ^= rs >> 27; return rs * 2685821657736338717ULL; }
static inline int rndn(int n) { return (int)(rnd64() % (u64)n); }

static void die(const char *m) { fprintf(stderr, "lns: %s\n", m); exit(1); }
static void *xmalloc(size_t bytes) { void *p = malloc(bytes ? bytes : 1); if (!p) die("out of memory"); return p; }
static void *xzero(size_t bytes) { void *p = calloc(bytes ? bytes : 1, 1); if (!p) die("out of memory"); return p; }

static void read_graph(const char *fn) {
    FILE *f = fopen(fn, "r");
    if (!f) die("cannot open graph");
    if (fscanf(f, "%d %d", &M, &E) != 2) die("bad graph header");
    int c;
    while ((c = fgetc(f)) != '\n' && c != EOF) { }
    aoff = xmalloc(sizeof(int) * (M + 1));
    anb = xmalloc(sizeof(int) * 2 * (size_t)E);
    size_t LB = 1 << 16;
    char *line = xmalloc(LB);
    int pos = 0;
    for (int v = 0; v < M; v++) {
        if (!fgets(line, (int)LB, f)) die("short graph file");
        char *p = line, *e;
        long idx = strtol(p, &e, 10); p = e;
        if (idx != v) die("graph lines must be in index order");
        strtol(p, &e, 10); p = e;                 /* rep: ignored */
        long d = strtol(p, &e, 10); p = e;
        aoff[v] = pos;
        for (long i = 0; i < d; i++) {
            long w = strtol(p, &e, 10); p = e;
            if (pos >= 2 * E) die("too many adjacency entries");
            anb[pos++] = (int)w;
        }
    }
    aoff[M] = pos;
    free(line);
    fclose(f);
    if (pos != 2 * E) die("adjacency count does not match header");
}

static int read_solution(const char *fn, int *out, int cap) {
    FILE *f = fopen(fn, "r");
    if (!f) die("cannot open solution");
    char buf[256];
    int n = 0;
    while (fgets(buf, sizeof buf, f)) {
        if (buf[0] == '#' || buf[0] == '\n') continue;
        int v;
        if (sscanf(buf, "%d", &v) != 1) continue;
        if (v < 0 || v >= M) die("solution index out of range");
        if (n >= cap) die("solution too large");
        out[n++] = v;
    }
    fclose(f);
    return n;
}

static void sol_add(int v) {
    if (inS[v]) die("internal: double insert");
    if (cnt[v] != 0) die("internal: insert of a vertex with solution neighbours");
    inS[v] = 1;
    spos[v] = nsol;
    slist[nsol++] = v;
    for (int e = aoff[v]; e < aoff[v + 1]; e++) {
        int w = anb[e];
        if (cnt[w] >= MAXT) die("tightness overflow");
        snb[(size_t)w * MAXT + cnt[w]++] = v;
    }
}

static void sol_del(int v) {
    if (!inS[v]) die("internal: delete of a non-solution vertex");
    inS[v] = 0;
    int p = spos[v], last = slist[--nsol];
    slist[p] = last;
    spos[last] = p;
    for (int e = aoff[v]; e < aoff[v + 1]; e++) {
        int w = anb[e];
        int *L = snb + (size_t)w * MAXT;
        int c = cnt[w];
        for (int i = 0; i < c; i++) if (L[i] == v) { L[i] = L[c - 1]; break; }
        cnt[w] = c - 1;
    }
}

static int verify_full(void) {
    int c = 0;
    for (int v = 0; v < M; v++) if (inS[v]) c++;
    if (c != nsol) return 0;
    for (int i = 0; i < nsol; i++) if (!inS[slist[i]]) return 0;
    for (int w = 0; w < M; w++) {
        int k = 0;
        for (int e = aoff[w]; e < aoff[w + 1]; e++) if (inS[anb[e]]) k++;
        if (k != cnt[w]) return 0;
        if (inS[w] && k) return 0;
    }
    return 1;
}

static int cmp_int(const void *a, const void *b) {
    int x = *(const int *)a, y = *(const int *)b;
    return (x > y) - (x < y);
}

static void save_solution(const char *fn) {
    int *tmp = xmalloc(sizeof(int) * (size_t)nsol);
    memcpy(tmp, slist, sizeof(int) * (size_t)nsol);
    qsort(tmp, (size_t)nsol, sizeof(int), cmp_int);
    char tname[4096];
    snprintf(tname, sizeof tname, "%s.tmp", fn);
    FILE *f = fopen(tname, "w");
    if (!f) die("cannot write output");
    for (int i = 0; i < nsol; i++) fprintf(f, "%d\n", tmp[i]);
    fclose(f);
    if (rename(tname, fn) != 0) die("cannot rename output");
    free(tmp);
}

static void shuffle(int *a, int n) {
    for (int i = n - 1; i > 0; i--) {
        int j = rndn(i + 1);
        int t = a[i]; a[i] = a[j]; a[j] = t;
    }
}

/* ---------- destroy strategies: fill DV[0..nd) with solution vertices ---------- */

static inline void add_D(int x) { inD[x] = dstamp; DV[nd++] = x; }

static void destroy_random(int k) {
    nd = 0;
    dstamp++;
    for (int i = 0; i < nsol; i++) perm[i] = slist[i];
    for (int i = 0; i < k; i++) {
        int j = i + rndn(nsol - i);
        int t = perm[i]; perm[i] = perm[j]; perm[j] = t;
        add_D(perm[i]);
    }
}

static void destroy_ball(int k, int lowt) {
    nd = 0;
    dstamp++;
    int v;
    do { v = rndn(M); } while (inS[v] || cnt[v] == 0);
    for (int i = 0; i < cnt[v] && nd < k; i++) add_D(snb[(size_t)v * MAXT + i]);
    while (nd < k) {
        mstamp++;
        int nc = 0;
        for (int i = 0; i < nd; i++) {
            int x = DV[i];
            for (int e = aoff[x]; e < aoff[x + 1]; e++) {
                int w = anb[e];
                if (inS[w] || cnt[w] > lowt) continue;
                for (int t = 0; t < cnt[w]; t++) {
                    int y = snb[(size_t)w * MAXT + t];
                    if (inD[y] == dstamp || mark[y] == mstamp) continue;
                    mark[y] = mstamp;
                    cand[nc++] = y;
                }
            }
        }
        if (nc == 0) {
            int y;
            do { y = slist[rndn(nsol)]; } while (inD[y] == dstamp);
            add_D(y);
            continue;
        }
        shuffle(cand, nc);
        for (int i = 0; i < nc && nd < k; i++) add_D(cand[i]);
    }
}

static void add_D_greedy(int x) {
    add_D(x);
    for (int e = aoff[x]; e < aoff[x + 1]; e++) {
        int w = anb[e];
        if (inS[w]) continue;
        rr[w]--;                       /* rr[w] = number of solution neighbours of w not in D */
        if (rr[w] == 1) {              /* w is now tight only to one solution vertex y outside D: y scores */
            for (int t = 0; t < cnt[w]; t++) {
                int y = snb[(size_t)w * MAXT + t];
                if (inD[y] != dstamp) { score[y]++; break; }
            }
        }
    }
}

static void destroy_greedy(int k) {
    nd = 0;
    dstamp++;
    for (int w = 0; w < M; w++) { rr[w] = cnt[w]; score[w] = 0; }
    for (int w = 0; w < M; w++)
        if (!inS[w] && cnt[w] == 1) score[snb[(size_t)w * MAXT]]++;
    add_D_greedy(slist[rndn(nsol)]);
    while (nd < k) {
        int start = rndn(nsol), best = -1, bs = -1;
        for (int t = 0; t < nsol; t++) {
            int idx = start + t;
            if (idx >= nsol) idx -= nsol;
            int y = slist[idx];
            if (inD[y] == dstamp) continue;
            if (score[y] > bs) { bs = score[y]; best = y; }
        }
        add_D_greedy(best);
    }
}

/* candidate set C = D + non-solution vertices whose solution neighbours all lie in D */
static int build_C(void) {
    mstamp++;
    int n = 0;
    for (int i = 0; i < nd; i++) CV[n++] = DV[i];
    for (int i = 0; i < nd; i++) {
        int x = DV[i];
        for (int e = aoff[x]; e < aoff[x + 1]; e++) {
            int w = anb[e];
            if (inS[w] || mark[w] == mstamp) continue;
            mark[w] = mstamp;
            int ok = 1;
            for (int t = 0; t < cnt[w]; t++)
                if (inD[snb[(size_t)w * MAXT + t]] != dstamp) { ok = 0; break; }
            if (ok) CV[n++] = w;
        }
    }
    return n;
}

/* ---------- exact maximum independent set on the local graph ---------- */

static inline int deg_in(int v, const u64 *P) {
    int c = 0;
    for (int k = 0; k < W; k++) c += __builtin_popcountll(ADJ[v][k] & P[k]);
    return c;
}

/* greedy partition of P into cliques of the local graph: an upper bound on the independent set inside P */
static int cover_bound(const u64 *P) {
    u64 U[MAXW], C2[MAXW];
    for (int k = 0; k < W; k++) U[k] = P[k];
    int cl = 0;
    for (int k = 0; k < W; k++) {
        while (U[k]) {
            int v = k * 64 + __builtin_ctzll(U[k]);
            U[k] &= U[k] - 1;
            cl++;
            for (int j = 0; j < W; j++) C2[j] = ADJ[v][j] & U[j];
            for (;;) {
                int u = -1;
                for (int j = 0; j < W; j++)
                    if (C2[j]) { u = j * 64 + __builtin_ctzll(C2[j]); break; }
                if (u < 0) break;
                U[u >> 6] &= ~(1ULL << (u & 63));
                C2[u >> 6] &= ~(1ULL << (u & 63));
                for (int j = 0; j < W; j++) C2[j] &= ADJ[u][j];
            }
        }
    }
    return cl;
}

static void mis_rec(int depth, int s) {
    if (aborted) return;
    if (++nodes > nodeCap) { aborted = 1; return; }
    u64 *P = POOL[depth];
    int sp0 = sp;
    /* reductions: vertices of degree <= 1 in P are always taken */
    int changed = 1;
    while (changed) {
        changed = 0;
        for (int v = 0; v < nC; v++) {
            if (!((P[v >> 6] >> (v & 63)) & 1ULL)) continue;
            if (deg_in(v, P) <= 1) {
                stk[sp++] = v;
                s++;
                P[v >> 6] &= ~(1ULL << (v & 63));
                for (int k = 0; k < W; k++) P[k] &= ~ADJ[v][k];
                changed = 1;
            }
        }
    }
    int any = 0;
    for (int k = 0; k < W; k++) if (P[k]) { any = 1; break; }
    if (!any) {
        if (s > bestN) {
            bestN = s;
            bestCount = sp;
            memcpy(bestSetL, stk, sizeof(int) * (size_t)sp);
        }
        sp = sp0;
        return;
    }
    if (s + cover_bound(P) <= bestN) { sp = sp0; return; }
    int bv = -1, bd = -1;
    for (int v = 0; v < nC; v++) {
        if (!((P[v >> 6] >> (v & 63)) & 1ULL)) continue;
        int d = deg_in(v, P);
        if (d > bd) { bd = d; bv = v; }
    }
    u64 *Q = POOL[depth + 1];
    for (int k = 0; k < W; k++) Q[k] = P[k] & ~ADJ[bv][k];
    Q[bv >> 6] &= ~(1ULL << (bv & 63));
    stk[sp++] = bv;
    mis_rec(depth + 1, s + 1);
    sp--;
    if (!aborted) {
        for (int k = 0; k < W; k++) Q[k] = P[k];
        Q[bv >> 6] &= ~(1ULL << (bv & 63));
        mis_rec(depth + 1, s);
    }
    sp = sp0;
}

/* solve MIS of the candidate set CV[0..n) (loc[] must already map them); returns 1 if the node cap was hit */
static int solve_local(int n, int lb) {
    nC = n;
    W = (n + 63) / 64;
    for (int i = 0; i < n; i++) {
        int x = CV[i];
        for (int k = 0; k < W; k++) ADJ[i][k] = 0;
        for (int e = aoff[x]; e < aoff[x + 1]; e++) {
            int j = loc[anb[e]];
            if (j >= 0) ADJ[i][j >> 6] |= 1ULL << (j & 63);
        }
        gidC[i] = x;
    }
    for (int k = 0; k < W; k++) POOL[0][k] = 0;
    for (int i = 0; i < n; i++) POOL[0][i >> 6] |= 1ULL << (i & 63);
    bestN = lb;
    bestCount = 0;
    nodes = 0;
    aborted = 0;
    sp = 0;
    mis_rec(0, 0);
    return aborted;
}


static int probe = 1;
static long long pr_total, pr_done, pr_better, pr_exact_gt_D, pr_gain_units;
static long long pr_nodes[100000]; static int pr_n;
static int cmp_ll(const void *a, const void *b) { long long x = *(const long long*)a, y = *(const long long*)b; return (x > y) - (x < y); }

static const char *SNAME[3] = {"random", "ball", "greedy"};

static void print_status(double cpu, long long iter) {
    fprintf(stderr, "t=%.1f iter=%lld nsol=%d", cpu, iter, nsol);
    for (int s = 0; s < 3; s++) {
        long long n = it_n[s] ? it_n[s] : 1;
        fprintf(stderr, " | %s: n=%lld avgD=%.1f avgC=%.1f maxC=%lld abort=%lld impr=%lld plateau=%lld skip=%lld",
                SNAME[s], it_n[s], (double)it_D[s] / n, (double)it_C[s] / n, it_Cmax[s], it_abort[s],
                it_impr[s], it_plat[s], it_skip[s]);
    }
    fprintf(stderr, "\n");
}

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: %s GRAPH SEED OUT CPU_BUDGET_S RNG [KMIN KMAX KMIN2 KMAX2 NODE_CAP]\n", argv[0]);
        return 2;
    }
    const char *gfn = argv[1], *sfn = argv[2], *ofn = argv[3];
    double budget = atof(argv[4]);
    rs = (u64)strtoull(argv[5], NULL, 10) * 0x9E3779B97F4A7C15ULL + 0x1234567ULL;
    if (rs == 0) rs = 1;
    int kmin = argc > 6 ? atoi(argv[6]) : 15;     /* strategy 0 (random): brief's 15..40 */
    int kmax = argc > 7 ? atoi(argv[7]) : 40;
    int kmin2 = argc > 8 ? atoi(argv[8]) : 40;    /* strategies 1 and 2 (ball, greedy) */
    int kmax2 = argc > 9 ? atoi(argv[9]) : 80;
    nodeCap = argc > 10 ? atoll(argv[10]) : 20000;
    if (kmin < 1 || kmax > MAXD || kmin > kmax) die("bad k range");
    if (kmin2 < 1 || kmax2 > MAXD || kmin2 > kmax2) die("bad k range 2");

    read_graph(gfn);
    snb = xmalloc(sizeof(int) * (size_t)M * MAXT);
    cnt = xzero(sizeof(int) * (size_t)M);
    inS = xzero((size_t)M);
    slist = xmalloc(sizeof(int) * (size_t)M);
    spos = xmalloc(sizeof(int) * (size_t)M);
    loc = xmalloc(sizeof(int) * (size_t)M);
    for (int v = 0; v < M; v++) loc[v] = -1;
    mark = xzero(sizeof(u64) * (size_t)M);
    inD = xzero(sizeof(u64) * (size_t)M);
    rr = xmalloc(sizeof(int) * (size_t)M);
    score = xmalloc(sizeof(int) * (size_t)M);
    DV = xmalloc(sizeof(int) * MAXD);
    CV = xmalloc(sizeof(int) * (size_t)M);
    perm = xmalloc(sizeof(int) * (size_t)M);
    cand = xmalloc(sizeof(int) * (size_t)M);
    TVbuf = xmalloc(sizeof(int) * MAXC);
    gidC = xmalloc(sizeof(int) * MAXC);
    mstamp = 0;
    dstamp = 0;

    int *init = xmalloc(sizeof(int) * (size_t)M);
    int n0 = read_solution(sfn, init, M);
    for (int i = 0; i < n0; i++) {
        if (inS[init[i]]) die("duplicate vertex in seed");
        if (cnt[init[i]]) die("seed is not independent");
        sol_add(init[i]);
    }
    int freeadd = 0;
    for (int v = 0; v < M; v++) if (!inS[v] && cnt[v] == 0) { sol_add(v); freeadd++; }
    free(init);
    if (!verify_full()) die("seed failed verification");
    int bestsize = nsol;
    fprintf(stderr, "seed size %d (free vertices added %d), M=%d E=%d\n", nsol, freeadd, M, E);
    save_solution(ofn);

    long long iter = 0;
    double lastrep = 0.0, cpu = 0.0;
    while ((cpu = (double)clock() / CLOCKS_PER_SEC) < budget) {
        iter++;
        int s = (int)(iter % 3);
        int k;
        if (s == 0) {
            k = kmin + rndn(kmax - kmin + 1);
            if (k > nsol) k = nsol;
            destroy_random(k);
        } else {
            k = kmin2 + rndn(kmax2 - kmin2 + 1);
            if (k > nsol) k = nsol;
            if (s == 1) destroy_ball(k, 3);
            else destroy_greedy(k);
        }
        int n = build_C();
        it_n[s]++;
        it_D[s] += nd;
        it_C[s] += n;
        if (n > it_Cmax[s]) it_Cmax[s] = n;

        int tn = nd;
        int *tv = DV;                       /* default: keep D */
        if (n <= MAXC) {
            shuffle(CV, n);
            for (int i = 0; i < n; i++) loc[CV[i]] = i;
            int ab = solve_local(n, nd - 1);
            for (int i = 0; i < n; i++) loc[CV[i]] = -1;
            if (ab) it_abort[s]++;

            if (ab && probe && pr_total < 40) {
                int first = bestN; int firstCount = bestCount;
                long long cap0 = nodeCap; nodeCap = 300000LL;
                for (int i = 0; i < n; i++) loc[CV[i]] = i;
                int ab2 = solve_local(n, nd - 1);
                for (int i = 0; i < n; i++) loc[CV[i]] = -1;
                long long used = nodes;
                nodeCap = cap0;
                int hist = ab2 ? 0 : 1;
                pr_total++; if (!ab2) pr_done++;
                if (!ab2) pr_nodes[pr_n++] = used;
                if (bestN > first) pr_better++;
                if (!ab2 && bestN > nd) pr_exact_gt_D++;
                if (bestCount > 0 && bestN > nd && !ab2) pr_gain_units += bestN - nd;
                (void)hist; (void)firstCount;
                if (pr_n >= 1 && pr_n % 50 == 0) {}
            }

            if (bestCount > 0) {
                for (int i = 0; i < bestCount; i++) TVbuf[i] = gidC[bestSetL[i]];
                tn = bestCount;
                tv = TVbuf;
            }
        } else {
            it_skip[s]++;
        }

        int same = (tn == nd);
        if (same) for (int i = 0; i < tn; i++) if (inD[tv[i]] != dstamp) { same = 0; break; }

        int before = nsol;
        for (int i = 0; i < nd; i++) sol_del(DV[i]);
        for (int i = 0; i < tn; i++) sol_add(tv[i]);
        for (int i = 0; i < n; i++) {
            int c = CV[i];
            if (!inS[c] && cnt[c] == 0) sol_add(c);
        }
        if (nsol < before) die("internal: solution shrank");
        if (nsol > before) it_impr[s]++;
        else if (!same) it_plat[s]++;

        if (nsol > bestsize) {
            bestsize = nsol;
            if (!verify_full()) die("internal: invalid solution after move");
            save_solution(ofn);
            fprintf(stderr, "improved to %d at iter %lld cpu %.1f (strategy %s)\n", nsol, iter, cpu, SNAME[s]);
        }
        if (iter % 100000 == 0 && !verify_full()) die("internal: consistency check failed");
        if (cpu - lastrep >= 30.0) {
            lastrep = cpu;
            print_status(cpu, iter);
        }
    }
    if (probe && pr_n) { qsort(pr_nodes, pr_n, sizeof(long long), cmp_ll);
        fprintf(stderr, "PROBE aborted-then-rerun total=%lld completed=%lld better_than_capped=%lld exact_gt_D=%lld gain_units=%lld\n", pr_total, pr_done, pr_better, pr_exact_gt_D, pr_gain_units);
        fprintf(stderr, "PROBE nodes to complete: median=%lld p90=%lld max=%lld\n", pr_nodes[pr_n/2], pr_nodes[(pr_n*9)/10], pr_nodes[pr_n-1]); }
    if (!verify_full()) die("internal: final check failed");
    save_solution(ofn);
    cpu = (double)clock() / CLOCKS_PER_SEC;
    print_status(cpu, iter);
    fprintf(stdout, "FINAL nsol=%d best=%d iters=%lld cpu=%.1f out=%s\n", nsol, bestsize, iter, cpu, ofn);
    return 0;
}
