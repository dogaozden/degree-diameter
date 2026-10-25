/* wclq.c: card c3 (squad round 3). Maximum-weight clique in an orbit graph.
   Exact: bitset branch and bound (vertices ordered by weight, then degree), greedy weighted-colouring bound.
   If the exact search is cut by its CPU limit, a tabu-style local search (free adds, (1,1)-swaps, perturbation)
   runs for THEUR more CPU seconds from the best clique found so far.
   usage: wclq GRAPH TEXACT THEUR SEED OUT
     GRAPH: binary: int32 K, int32 W (words per row), int32 w[K] (weights), uint64 rows[K*W] (bit j of row i set
            iff i~j; symmetric, zero diagonal; W = ceil(K/64)).
     TEXACT, THEUR: CPU seconds (clock()) for the exact search and for the local search afterwards.
     OUT: text file: "# W K optimal nodes cpu" then one vertex index (GRAPH numbering) per line.
     stdout: "RESULT <weight> <K> <optimal> <nodes> <cpu>".                                                     */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

static int K, W;
static int *wt;            /* weights, internal numbering */
static uint64_t *adj;      /* K*W adjacency rows, internal numbering */
static int *orig;          /* internal -> GRAPH index */
static double TEXACT, THEUR;
static clock_t t0;
static int aborted = 0;
static long long nodes = 0;
static int bestW = 0, nbest = 0;
static int *best, *stk;
static uint64_t **Pb, **Qb, **Cb;
static int **vb, **cs_, **cumb;
static uint64_t rng_s = 88172645463325252ULL;

static double cpu(void) { return (double)(clock() - t0) / CLOCKS_PER_SEC; }
static uint64_t rnd(void) { rng_s ^= rng_s << 13; rng_s ^= rng_s >> 7; rng_s ^= rng_s << 17; return rng_s; }
static inline int adjq(int u, int v) { return (int)((adj[(size_t)u * W + (v >> 6)] >> (v & 63)) & 1); }

static void ensure_depth(int d) {
    if (Pb[d]) return;
    Pb[d] = malloc(8 * (size_t)W); Qb[d] = malloc(8 * (size_t)W); Cb[d] = malloc(8 * (size_t)W);
    vb[d] = malloc(sizeof(int) * (K + 1)); cs_[d] = malloc(sizeof(int) * (K + 1)); cumb[d] = malloc(sizeof(int) * (K + 2));
}

static void expand(int d, int curW) {
    ensure_depth(d + 1);
    uint64_t *P = Pb[d], *Q = Qb[d], *C = Cb[d], *NP = Pb[d + 1];
    int *vs = vb[d], *cs = cs_[d], *cb = cumb[d];
    nodes++;
    if ((nodes & 4095) == 0 && cpu() > TEXACT) aborted = 1;
    if (aborted) return;
    memcpy(Q, P, sizeof(uint64_t) * W);
    int nv = 0, ncol = 0, cum = 0;
    for (;;) {                       /* greedy sequential colouring of P into independent classes */
        int any = 0;
        for (int i = 0; i < W; i++) if (Q[i]) { any = 1; break; }
        if (!any) break;
        ncol++;
        memcpy(C, Q, sizeof(uint64_t) * W);
        int maxw = 0;
        for (int i = 0; i < W; i++) {
            while (C[i]) {
                int b = __builtin_ctzll(C[i]);
                int v = i * 64 + b;
                Q[i] &= ~(1ULL << b);
                C[i] &= ~(1ULL << b);
                const uint64_t *a = &adj[(size_t)v * W];
                for (int j = i; j < W; j++) C[j] &= ~a[j];
                vs[nv] = v; cs[nv] = ncol; nv++;
                if (wt[v] > maxw) maxw = wt[v];
            }
        }
        cum += maxw;
        cb[ncol] = cum;              /* weighted colouring bound for colours 1..ncol */
    }
    for (int i = nv - 1; i >= 0; i--) {
        if (curW + cb[cs[i]] <= bestW) return;
        int v = vs[i];
        const uint64_t *a = &adj[(size_t)v * W];
        int any = 0;
        for (int j = 0; j < W; j++) { NP[j] = P[j] & a[j]; any |= (NP[j] != 0); }
        stk[d] = v;
        if (!any) {
            if (curW + wt[v] > bestW) {
                bestW = curW + wt[v];
                nbest = d + 1;
                for (int k = 0; k <= d; k++) best[k] = stk[k];
            }
        } else {
            expand(d + 1, curW + wt[v]);
            if (aborted) return;
        }
        P[v >> 6] &= ~(1ULL << (v & 63));
    }
}

/* ---- tabu-style local search: used only when the exact search was cut ---- */
static int *inS, *miss, *tabu, *S, nS, sumW, *cand;
static void add_v(int v) {
    inS[v] = 1; S[nS++] = v; sumW += wt[v];
    for (int u = 0; u < K; u++) if (u != v && !adjq(u, v)) miss[u]++;
}
static void rem_v(int v) {
    inS[v] = 0; sumW -= wt[v];
    for (int k = 0; k < nS; k++) if (S[k] == v) { S[k] = S[--nS]; break; }
    for (int u = 0; u < K; u++) if (u != v && !adjq(u, v)) miss[u]--;
}
static int conflict_of(int v) {          /* the unique clique vertex not adjacent to v (miss[v] == 1) */
    for (int k = 0; k < nS; k++) if (!adjq(S[k], v)) return S[k];
    return -1;
}
static void local_search(void) {
    inS = calloc(K, sizeof(int)); miss = calloc(K, sizeof(int)); tabu = calloc(K, sizeof(int));
    S = malloc(sizeof(int) * K); cand = malloc(sizeof(int) * K); nS = 0; sumW = 0;
    int *bestS = malloc(sizeof(int) * K); int nbS = 0, bestSW = 0;
    for (int k = 0; k < nbest; k++) add_v(best[k]);
    long long it = 0;
    while (cpu() < TEXACT + THEUR) {
        it++;
        for (;;) {                       /* free additions: heaviest first, random ties */
            int nc = 0, bw = -1;
            for (int v = 0; v < K; v++) if (!inS[v] && miss[v] == 0) {
                if (wt[v] > bw) { bw = wt[v]; nc = 0; }
                if (wt[v] == bw) cand[nc++] = v;
            }
            if (nc == 0) break;
            add_v(cand[rnd() % nc]);
        }
        if (sumW > bestSW) { bestSW = sumW; nbS = nS; memcpy(bestS, S, sizeof(int) * nS); }
        int nc = 0, bg = -1000000;       /* (1,1)-swaps with non-negative gain, not tabu */
        for (int v = 0; v < K; v++) if (!inS[v] && miss[v] == 1 && tabu[v] <= it) {
            int g = wt[v] - wt[conflict_of(v)];
            if (g > bg) { bg = g; nc = 0; }
            if (g == bg) cand[nc++] = v;
        }
        if (nc > 0 && bg >= 0) {
            int v = cand[rnd() % nc];
            int u = conflict_of(v);
            rem_v(u); tabu[u] = (int)(it + 7 + rnd() % 10);
            add_v(v);
        } else {                         /* perturbation: force a non-tabu vertex with <= 2 conflicts */
            int nf = 0;
            for (int v = 0; v < K; v++) if (!inS[v] && miss[v] <= 2 && tabu[v] <= it) cand[nf++] = v;
            if (nf == 0) continue;
            int v = cand[rnd() % nf];
            for (int k = nS - 1; k >= 0; k--) {
                int u = S[k];
                if (!adjq(u, v)) { rem_v(u); tabu[u] = (int)(it + 7 + rnd() % 10); }
            }
            add_v(v);
        }
        if (sumW > bestSW) { bestSW = sumW; nbS = nS; memcpy(bestS, S, sizeof(int) * nS); }
    }
    if (bestSW > bestW) { bestW = bestSW; nbest = nbS; memcpy(best, bestS, sizeof(int) * nbS); }
    fprintf(stderr, "local search: %lld iterations, best %d\n", it, bestW);
}

int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: wclq GRAPH TEXACT THEUR SEED OUT\n"); return 2; }
    t0 = clock();
    TEXACT = atof(argv[2]); THEUR = atof(argv[3]);
    rng_s ^= (uint64_t)atoll(argv[4]) * 0x9E3779B97F4A7C15ULL; if (!rng_s) rng_s = 1;
    FILE *f = fopen(argv[1], "rb");
    if (!f) { fprintf(stderr, "cannot open %s\n", argv[1]); return 2; }
    int32_t hdr[2];
    if (fread(hdr, 4, 2, f) != 2) return 2;
    int K0 = hdr[0]; W = hdr[1]; K = K0;
    int32_t *w0 = malloc(4 * (size_t)K0);
    if (fread(w0, 4, K0, f) != (size_t)K0) return 2;
    uint64_t *rows0 = malloc(8 * (size_t)K0 * W);
    if (fread(rows0, 8, (size_t)K0 * W, f) != (size_t)K0 * W) return 2;
    fclose(f);
    int *deg = calloc(K, sizeof(int));
    for (int i = 0; i < K; i++) {
        int c = 0;
        for (int j = 0; j < W; j++) c += __builtin_popcountll(rows0[(size_t)i * W + j]);
        deg[i] = c;
    }
    int *perm = malloc(sizeof(int) * K);      /* internal i -> original perm[i]: weight desc, degree desc */
    for (int i = 0; i < K; i++) perm[i] = i;
    for (int i = 1; i < K; i++) {
        int x = perm[i], j = i - 1;
        while (j >= 0 && (w0[perm[j]] < w0[x] || (w0[perm[j]] == w0[x] && deg[perm[j]] < deg[x]))) {
            perm[j + 1] = perm[j]; j--;
        }
        perm[j + 1] = x;
    }
    orig = malloc(sizeof(int) * K);
    int *pos = malloc(sizeof(int) * K);
    for (int i = 0; i < K; i++) { orig[i] = perm[i]; pos[perm[i]] = i; }
    wt = malloc(sizeof(int) * K);
    for (int i = 0; i < K; i++) wt[i] = w0[perm[i]];
    adj = calloc((size_t)K * W, sizeof(uint64_t));
    for (int i = 0; i < K; i++) {
        int oi = perm[i];
        for (int j = 0; j < K0; j++) {
            if ((rows0[(size_t)oi * W + (j >> 6)] >> (j & 63)) & 1) {
                int ij = pos[j];
                adj[(size_t)i * W + (ij >> 6)] |= 1ULL << (ij & 63);
            }
        }
    }
    for (int i = 0; i < K; i++) {
        if (adjq(i, i)) { fprintf(stderr, "diagonal bit set\n"); return 3; }
        for (int j = i + 1; j < K; j++) if (adjq(i, j) != adjq(j, i)) { fprintf(stderr, "asymmetric\n"); return 3; }
    }
    best = malloc(sizeof(int) * (K + 1)); stk = malloc(sizeof(int) * (K + 1));
    Pb = calloc(K + 3, sizeof(uint64_t *)); Qb = calloc(K + 3, sizeof(uint64_t *)); Cb = calloc(K + 3, sizeof(uint64_t *));
    vb = calloc(K + 3, sizeof(int *)); cs_ = calloc(K + 3, sizeof(int *)); cumb = calloc(K + 3, sizeof(int *));
    /* greedy start: from every vertex, grow a clique inside its neighbourhood, heaviest vertex first */
    {
        uint64_t *cd = malloc(8 * (size_t)W);
        int *cl = malloc(sizeof(int) * (K + 1));
        for (int v0 = 0; v0 < K; v0++) {
            memcpy(cd, &adj[(size_t)v0 * W], 8 * (size_t)W);
            int ncl = 0, cw = wt[v0]; cl[ncl++] = v0;
            for (;;) {
                int bv = -1;
                for (int i = 0; i < W; i++) {
                    uint64_t x = cd[i];
                    while (x) { int b = __builtin_ctzll(x); x &= x - 1; int v = i * 64 + b;
                        if (bv < 0 || wt[v] > wt[bv]) bv = v; }
                }
                if (bv < 0) break;
                cl[ncl++] = bv; cw += wt[bv];
                for (int i = 0; i < W; i++) cd[i] &= adj[(size_t)bv * W + i];
            }
            if (cw > bestW) { bestW = cw; nbest = ncl; memcpy(best, cl, sizeof(int) * ncl); }
        }
        free(cd); free(cl);
    }
    ensure_depth(0);
    for (int i = 0; i < W; i++) Pb[0][i] = 0;
    for (int v = 0; v < K; v++) Pb[0][v >> 6] |= 1ULL << (v & 63);
    expand(0, 0);
    int optimal = !aborted;
    if (aborted) {
        fprintf(stderr, "exact search cut at %.1f s after %lld nodes (best %d); local search\n", cpu(), nodes, bestW);
        local_search();
    }
    FILE *g = fopen(argv[5], "w");
    if (!g) { fprintf(stderr, "cannot write %s\n", argv[5]); return 2; }
    fprintf(g, "# %d %d %d %lld %.2f\n", bestW, K, optimal, nodes, cpu());
    for (int k = 0; k < nbest; k++) fprintf(g, "%d\n", orig[best[k]]);
    fclose(g);
    printf("RESULT %d %d %d %lld %.2f\n", bestW, K, optimal, nodes, cpu());
    return 0;
}
