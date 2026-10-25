// orbclq.c: G-invariant partial ovoids of Q(6,q), i.e. pairwise opposite point sets of the split Cayley hexagon H(q).
// Points of Q(x) = x0x4 + x1x5 + x2x6 - x3^2 = 0 in PG(6,q), q prime; x, y opposite in H(q) iff
// B(x,y) = x0y4+x4y0+x1y5+x5y1+x2y6+x6y2-2x3y3 != 0.
// Reads generator matrices of a group G of similitudes (7x7, row-major, acting on column vectors: x -> M x),
// computes the G-orbits on points, keeps the "good" orbits (internally pairwise non-orthogonal), builds the
// orbit compatibility graph and searches a maximum-weight clique (weight = orbit size): multi-neighbourhood tabu
// search (ADD / SWAP / DROP moves, restarts and kicks from the best clique), optionally an exact branch and bound
// when the graph is small. The final union is re-checked point by point.
//
// usage: orbclq GENS [-q Q] [-t SECONDS] [-s SEED] [-w WARM_POINTS] [-o OUT_POINTS] [-x EXACT_MAX_K] [-v]
//   GENS: integers, '#' starts a comment; each consecutive 49 integers form one generator.
//   WARM_POINTS / OUT_POINTS: one point per line, 7 coordinates.
// stdout: a summary line "RESULT q=.. order_bound=.. orbits=.. good=K best=W (n orbits) exact=0|1 time=.."
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <math.h>

static int q = 11;
static int npts;
static uint8_t *P;        // npts*7
static int32_t *lookup;   // q^7
static int inv[64];

static double now(void) { struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts); return ts.tv_sec + 1e-9 * ts.tv_nsec; }
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline int rndi(int n) { return (int)(rnd() % (uint64_t)n); }

static inline int Bf(const uint8_t *x, const uint8_t *y) {
    int s = x[0]*y[4] + x[4]*y[0] + x[1]*y[5] + x[5]*y[1] + x[2]*y[6] + x[6]*y[2] + (q-2)*x[3]*y[3];
    return s % q;
}
static inline long code_of(const int *v) { long c = 0; for (int i = 6; i >= 0; i--) c = c * q + v[i]; return c; }
static int normalize(int *v) { // returns 0 if zero vector
    int i = 0; while (i < 7 && v[i] % q == 0) i++;
    if (i == 7) return 0;
    int s = inv[((v[i] % q) + q) % q];
    for (int j = 0; j < 7; j++) v[j] = (((v[j] % q) + q) % q) * s % q;
    return 1;
}
static void enum_points(void) {
    long tot = 1; for (int i = 0; i < 7; i++) tot *= q;
    lookup = malloc(sizeof(int32_t) * tot);
    for (long c = 0; c < tot; c++) lookup[c] = -1;
    int cap = 1 << 20; P = malloc(7 * (size_t)cap); npts = 0;
    int v[7];
    for (long c = 0; c < tot; c++) {
        long t = c; for (int i = 0; i < 7; i++) { v[i] = t % q; t /= q; }
        int i = 0; while (i < 7 && v[i] == 0) i++;
        if (i == 7 || v[i] != 1) continue;
        if ((v[0]*v[4] + v[1]*v[5] + v[2]*v[6] - v[3]*v[3]) % q) continue;
        if (npts == cap) { cap *= 2; P = realloc(P, 7 * (size_t)cap); }
        for (int j = 0; j < 7; j++) P[7*npts + j] = v[j];
        lookup[c] = npts++;
    }
}
static int point_index(const int *w0) {
    int v[7]; for (int j = 0; j < 7; j++) v[j] = w0[j];
    if (!normalize(v)) return -1;
    return lookup[code_of(v)];
}

// ---------------- graph ----------------
static int K;                 // good orbits
static int W64;               // words per row
static uint64_t *adj;         // K*W64 compatibility bitsets
static int *wt;               // weights
static inline int ADJ(int a, int b) { return (adj[(size_t)a*W64 + (b>>6)] >> (b & 63)) & 1; }

// ---------------- tabu search (MN/TS style) ----------------
static int *inC, *miss, *sumNA, *clq, csz, cw;
static long *tabu;
static int *best, bsz, bw;
static int *gbest, gbsz, gbw;

static void ls_reset(void) {
    memset(inC, 0, sizeof(int)*K); memset(miss, 0, sizeof(int)*K); memset(sumNA, 0, sizeof(int)*K);
    csz = 0; cw = 0;
}
static void c_add(int u) {
    inC[u] = 1; clq[csz++] = u; cw += wt[u];
    const uint64_t *row = adj + (size_t)u*W64;
    for (int w = 0; w < W64; w++) {
        uint64_t m = ~row[w];
        if (w == W64-1 && (K & 63)) m &= (1ULL << (K & 63)) - 1;
        while (m) { int b = __builtin_ctzll(m); m &= m-1; int v = (w<<6) + b; if (v != u) { miss[v]++; sumNA[v] += u; } }
    }
}
static void c_del(int u) {
    inC[u] = 0; cw -= wt[u];
    for (int i = 0; i < csz; i++) if (clq[i] == u) { clq[i] = clq[--csz]; break; }
    const uint64_t *row = adj + (size_t)u*W64;
    for (int w = 0; w < W64; w++) {
        uint64_t m = ~row[w];
        if (w == W64-1 && (K & 63)) m &= (1ULL << (K & 63)) - 1;
        while (m) { int b = __builtin_ctzll(m); m &= m-1; int v = (w<<6) + b; if (v != u) { miss[v]--; sumNA[v] -= u; } }
    }
}
static void greedy_fill(void) {
    for (;;) {
        int bv = -1, bwt = -1, cnt = 0;
        for (int v = 0; v < K; v++) if (!inC[v] && miss[v] == 0) {
            if (wt[v] > bwt) { bwt = wt[v]; bv = v; cnt = 1; }
            else if (wt[v] == bwt && rndi(++cnt) == 0) bv = v;
        }
        if (bv < 0) break;
        c_add(bv);
    }
}
static void save_if_better(void) {
    if (cw > bw) { bw = cw; bsz = csz; memcpy(best, clq, sizeof(int)*csz); }
}

static void tabu_search(double tlimit, int verbose, int have_warm) {
    double t0 = now();
    long it = 0, last_imp = 0;
    int L = 4000 + 2*K;
    gbw = -1;
    if (!have_warm) { ls_reset(); c_add(rndi(K)); greedy_fill(); }
    bw = -1; save_if_better();
    gbw = bw; gbsz = bsz; memcpy(gbest, best, sizeof(int)*bsz);
    int restarts = 0;
    while (1) {
        it++;
        if ((it & 255) == 0 && now() - t0 > tlimit) break;
        // evaluate moves
        int addv = -1, addg = -1000000, ca = 0;
        int swv = -1, swu = -1, swg = -1000000, cs = 0;
        int nOM = 0;
        for (int v = 0; v < K; v++) {
            if (inC[v]) continue;
            int m = miss[v];
            if (m == 0) {
                int g = wt[v];
                int ok = tabu[v] <= it || cw + g > gbw;
                if (!ok) continue;
                if (g > addg) { addg = g; addv = v; ca = 1; } else if (g == addg && rndi(++ca) == 0) addv = v;
            } else if (m == 1) {
                nOM++;
                int u = sumNA[v];
                int g = wt[v] - wt[u];
                int ok = tabu[v] <= it || cw + g > gbw;
                if (!ok) continue;
                if (g > swg) { swg = g; swv = v; swu = u; cs = 1; } else if (g == swg && rndi(++cs) == 0) { swv = v; swu = u; }
            }
        }
        int dru = -1, drg = -1000000, cd = 0;
        for (int i = 0; i < csz; i++) { int u = clq[i]; int g = -wt[u]; if (g > drg) { drg = g; dru = u; cd = 1; } else if (g == drg && rndi(++cd) == 0) dru = u; }
        // choose
        if (addv >= 0 && addg >= swg) {
            c_add(addv);
        } else if (swv >= 0 && (addv < 0 ? 1 : swg > addg) && (swg >= drg || dru < 0)) {
            c_add(swv); c_del(swu); tabu[swu] = it + 7 + rndi(nOM + 1 > 10 ? 10 : nOM + 1);
        } else if (dru >= 0) {
            c_del(dru); tabu[dru] = it + 7;
        }
        if (cw > bw) { save_if_better(); last_imp = it; }
        if (bw > gbw) {
            gbw = bw; gbsz = bsz; memcpy(gbest, best, sizeof(int)*bsz);
            if (verbose) fprintf(stderr, "  [%.1fs it=%ld restarts=%d] best %d (%d orbits)\n", now()-t0, it, restarts, gbw, gbsz);
        }
        if (it - last_imp > L) {
            // restart: alternate random restart and kick from the global best
            restarts++;
            ls_reset();
            for (int v = 0; v < K; v++) tabu[v] = 0;
            if (restarts % 2) {
                // kick: keep a random 60-85% of the global best
                int keep = (int)(gbsz * (0.6 + 0.25 * (rnd() % 1000) / 1000.0));
                int tmp[gbsz]; memcpy(tmp, gbest, sizeof(int)*gbsz);
                for (int i = 0; i < gbsz; i++) { int j = i + rndi(gbsz - i); int t = tmp[i]; tmp[i] = tmp[j]; tmp[j] = t; }
                for (int i = 0; i < keep; i++) c_add(tmp[i]);
                // forbid re-adding the removed ones for a while
                for (int i = keep; i < gbsz; i++) tabu[tmp[i]] = it + 50 + rndi(50);
            } else {
                c_add(rndi(K));
            }
            greedy_fill();
            bw = -1; save_if_better(); last_imp = it;
        }
    }
    if (verbose) fprintf(stderr, "  tabu: %ld iterations, %d restarts, %.1fs\n", it, restarts, now()-t0);
}

// ---------------- exact branch and bound (small K) ----------------
static int bb_best; static int *bb_sol, bb_solsz; static int *bb_cur, bb_cursz; static double bb_t0, bb_tl; static int bb_abort; static long bb_nodes;
static void bb_rec(int *cand, int nc, int curw) {
    if (bb_abort) return;
    if ((++bb_nodes & 1023) == 0 && now() - bb_t0 > bb_tl) { bb_abort = 1; return; }
    if (nc == 0) { if (curw > bb_best) { bb_best = curw; bb_solsz = bb_cursz; memcpy(bb_sol, bb_cur, sizeof(int)*bb_cursz); } return; }
    // greedy colouring bound: colour classes are independent sets, bound = sum of max weight per class
    int *col = malloc(sizeof(int)*nc), *order = malloc(sizeof(int)*nc), *cmax = malloc(sizeof(int)*nc);
    int ncol = 0; int *left = malloc(sizeof(int)*nc); int nl = nc; memcpy(left, cand, sizeof(int)*nc);
    int no = 0; int *ub = malloc(sizeof(int)*nc); int acc = 0;
    while (nl > 0) {
        int *cls = malloc(sizeof(int)*nl); int ncl = 0; int mx = 0;
        int *rest = malloc(sizeof(int)*nl); int nr = 0;
        for (int i = 0; i < nl; i++) {
            int v = left[i], ok = 1;
            for (int j = 0; j < ncl; j++) if (ADJ(v, cls[j])) { ok = 0; break; }
            if (ok) { cls[ncl++] = v; if (wt[v] > mx) mx = wt[v]; } else rest[nr++] = v;
        }
        acc += mx;
        for (int j = 0; j < ncl; j++) { order[no] = cls[j]; ub[no] = acc; col[no] = ncol; no++; }
        cmax[ncol++] = mx;
        free(cls); memcpy(left, rest, sizeof(int)*nr); nl = nr; free(rest);
    }
    for (int i = no - 1; i >= 0; i--) {
        if (curw + ub[i] <= bb_best) break;
        int v = order[i];
        int *nc2 = malloc(sizeof(int)*i); int n2 = 0;
        for (int j = 0; j < i; j++) if (ADJ(v, order[j])) nc2[n2++] = order[j];
        bb_cur[bb_cursz++] = v;
        bb_rec(nc2, n2, curw + wt[v]);
        bb_cursz--;
        free(nc2);
        if (bb_abort) break;
    }
    free(col); free(order); free(cmax); free(left); free(ub);
}

int main(int argc, char **argv) {
    if (argc < 2) { fprintf(stderr, "usage: orbclq GENS [-q Q] [-t SEC] [-s SEED] [-w WARM] [-o OUT] [-x EXACTK] [-v]\n"); return 1; }
    const char *gfile = argv[1], *warm = NULL, *out = NULL; double tl = 60; int exactK = 400, verbose = 0; long seed = 1;
    for (int i = 2; i < argc; i++) {
        if (!strcmp(argv[i], "-q")) q = atoi(argv[++i]);
        else if (!strcmp(argv[i], "-t")) tl = atof(argv[++i]);
        else if (!strcmp(argv[i], "-s")) seed = atol(argv[++i]);
        else if (!strcmp(argv[i], "-w")) warm = argv[++i];
        else if (!strcmp(argv[i], "-o")) out = argv[++i];
        else if (!strcmp(argv[i], "-x")) exactK = atoi(argv[++i]);
        else if (!strcmp(argv[i], "-v")) verbose = 1;
    }
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 10; i++) rnd();
    double T0 = now();
    for (int a = 1; a < q; a++) for (int b = 1; b < q; b++) if (a*b % q == 1) inv[a] = b;
    enum_points();
    // generators
    FILE *f = fopen(gfile, "r"); if (!f) { perror(gfile); return 1; }
    int *vals = NULL, nv = 0, cap = 0; char line[4096];
    while (fgets(line, sizeof line, f)) {
        char *h = strchr(line, '#'); if (h) *h = 0;
        char *p = line; char *e;
        for (;;) { long x = strtol(p, &e, 10); if (e == p) break; if (nv == cap) { cap = cap ? 2*cap : 256; vals = realloc(vals, sizeof(int)*cap); } vals[nv++] = (int)x; p = e; }
    }
    fclose(f);
    if (nv % 49 || nv == 0) { fprintf(stderr, "generator file: %d integers, not a multiple of 49\n", nv); return 1; }
    int ng = nv / 49;
    int32_t **perm = malloc(sizeof(int32_t*) * ng);
    for (int g = 0; g < ng; g++) {
        perm[g] = malloc(sizeof(int32_t) * npts);
        int *M = vals + 49*g;
        for (int p = 0; p < npts; p++) {
            int w[7];
            for (int r = 0; r < 7; r++) { int s = 0; for (int c = 0; c < 7; c++) s += M[7*r+c] * P[7*p+c]; w[r] = ((s % q) + q) % q; }
            int j = point_index(w);
            if (j < 0) { fprintf(stderr, "generator %d does not preserve the quadric (point %d)\n", g, p); return 1; }
            perm[g][p] = j;
        }
    }
    // orbits
    int32_t *lab = malloc(sizeof(int32_t)*npts); for (int p = 0; p < npts; p++) lab[p] = -1;
    int32_t *stack = malloc(sizeof(int32_t)*npts);
    int norb = 0; int32_t *ostart = malloc(sizeof(int32_t)*(npts+1)); int32_t *opts = malloc(sizeof(int32_t)*npts); int pos = 0;
    int maxo = 0;
    for (int p = 0; p < npts; p++) if (lab[p] < 0) {
        int sp = 0; stack[sp++] = p; lab[p] = norb; ostart[norb] = pos;
        while (sp) { int x = stack[--sp]; opts[pos++] = x; for (int g = 0; g < ng; g++) { int y = perm[g][x]; if (lab[y] < 0) { lab[y] = norb; stack[sp++] = y; } } }
        int sz = pos - ostart[norb]; if (sz > maxo) maxo = sz;
        norb++;
    }
    ostart[norb] = pos;
    // good orbits
    int *good = malloc(sizeof(int)*norb); K = 0;
    int *gidx = malloc(sizeof(int)*norb);
    for (int o = 0; o < norb; o++) {
        gidx[o] = -1;
        const uint8_t *r = P + 7*(size_t)opts[ostart[o]]; int ok = 1;
        for (int k = ostart[o] + 1; k < ostart[o+1]; k++) if (Bf(r, P + 7*(size_t)opts[k]) == 0) { ok = 0; break; }
        if (ok) { gidx[o] = K; good[K++] = o; }
    }
    long hist[64] = {0};
    for (int i = 0; i < K; i++) { int s = ostart[good[i]+1] - ostart[good[i]]; int b = 0; while ((1 << (b+1)) <= s) b++; hist[b]++; }
    fprintf(stderr, "points %d, generators %d, orbits %d (max size %d), good orbits %d [%.1fs]\n", npts, ng, norb, maxo, K, now()-T0);
    {   // orbit size histogram: size x count (good count)
        int *cnt = calloc(maxo + 1, sizeof(int)), *gcnt = calloc(maxo + 1, sizeof(int));
        for (int o = 0; o < norb; o++) { int s = ostart[o+1] - ostart[o]; cnt[s]++; if (gidx[o] >= 0) gcnt[s]++; }
        fprintf(stderr, "orbit sizes (size:count/good):");
        for (int s = 1; s <= maxo; s++) if (cnt[s]) fprintf(stderr, " %d:%d/%d", s, cnt[s], gcnt[s]);
        fprintf(stderr, "\n"); free(cnt); free(gcnt);
    }
    if (K == 0) { printf("RESULT q=%d orbits=%d good=0 best=0\n", q, norb); return 0; }
    W64 = (K + 63) / 64;
    adj = calloc((size_t)K * W64, sizeof(uint64_t));
    if (!adj) { fprintf(stderr, "out of memory for K=%d\n", K); return 1; }
    wt = malloc(sizeof(int)*K);
    for (int i = 0; i < K; i++) wt[i] = ostart[good[i]+1] - ostart[good[i]];
    long nedge = 0;
    for (int i = 0; i < K; i++) {
        const uint8_t *r = P + 7*(size_t)opts[ostart[good[i]]];
        int d[7] = { r[4], r[5], r[6], (q-2)*r[3] % q, r[0], r[1], r[2] };
        for (int j = i + 1; j < K; j++) {
            int o = good[j], ok = 1;
            for (int k = ostart[o]; k < ostart[o+1]; k++) {
                const uint8_t *y = P + 7*(size_t)opts[k];
                int s = d[0]*y[0] + d[1]*y[1] + d[2]*y[2] + d[3]*y[3] + d[4]*y[4] + d[5]*y[5] + d[6]*y[6];
                if (s % q == 0) { ok = 0; break; }
            }
            if (ok) { adj[(size_t)i*W64 + (j>>6)] |= 1ULL << (j&63); adj[(size_t)j*W64 + (i>>6)] |= 1ULL << (i&63); nedge++; }
        }
    }
    double dens = K > 1 ? 2.0*nedge/((double)K*(K-1)) : 0;
    fprintf(stderr, "compatibility graph: K=%d edges=%ld density %.4f [%.1fs]\n", K, nedge, dens, now()-T0);
    inC = calloc(K, sizeof(int)); miss = calloc(K, sizeof(int)); sumNA = calloc(K, sizeof(int)); clq = malloc(sizeof(int)*K);
    tabu = calloc(K, sizeof(long)); best = malloc(sizeof(int)*K); gbest = malloc(sizeof(int)*K);
    int have_warm = 0;
    if (warm) {
        FILE *wf = fopen(warm, "r"); if (!wf) { perror(warm); return 1; }
        char *inset = calloc(npts, 1); int nw = 0;
        while (fgets(line, sizeof line, wf)) {
            char *h = strchr(line, '#'); if (h) *h = 0;
            int v[7]; if (sscanf(line, "%d %d %d %d %d %d %d", v, v+1, v+2, v+3, v+4, v+5, v+6) != 7) continue;
            int j = point_index(v); if (j >= 0) { inset[j] = 1; nw++; }
        }
        fclose(wf);
        ls_reset();
        int nin = 0;
        for (int i = 0; i < K; i++) {
            int o = good[i], all = 1;
            for (int k = ostart[o]; k < ostart[o+1]; k++) if (!inset[opts[k]]) { all = 0; break; }
            if (all && miss[i] == 0) { c_add(i); nin++; }
        }
        fprintf(stderr, "warm start: %d points read, %d orbits inside (weight %d)\n", nw, nin, cw);
        greedy_fill();
        have_warm = 1; free(inset);
    }
    int exact = 0;
    tabu_search(K <= exactK ? (tl < 10 ? tl : 10) : tl, verbose, have_warm);
    if (K <= exactK) {
        bb_best = gbw; bb_sol = malloc(sizeof(int)*K); bb_cur = malloc(sizeof(int)*K); bb_solsz = 0; bb_cursz = 0;
        bb_t0 = now(); bb_tl = tl; bb_abort = 0; bb_nodes = 0;
        int *cand = malloc(sizeof(int)*K); for (int i = 0; i < K; i++) cand[i] = i;
        bb_rec(cand, K, 0);
        if (!bb_abort) exact = 1;
        if (bb_best > gbw && bb_solsz) { gbw = bb_best; gbsz = bb_solsz; memcpy(gbest, bb_sol, sizeof(int)*bb_solsz); }
        fprintf(stderr, "branch and bound: %s, %ld nodes, best %d\n", exact ? "complete" : "time limit", bb_nodes, gbw);
    }
    // verify the union point by point
    int n = 0; for (int i = 0; i < gbsz; i++) n += wt[gbest[i]];
    int32_t *S = malloc(sizeof(int32_t)*n); int m = 0;
    for (int i = 0; i < gbsz; i++) { int o = good[gbest[i]]; for (int k = ostart[o]; k < ostart[o+1]; k++) S[m++] = opts[k]; }
    long bad = 0;
    for (int a = 0; a < m; a++) for (int b = a+1; b < m; b++) if (Bf(P + 7*(size_t)S[a], P + 7*(size_t)S[b]) == 0) bad++;
    if (out) {
        FILE *of = fopen(out, "w");
        fprintf(of, "# %d pairwise non-orthogonal points of Q(6,%d) (orbclq %s, %d orbits)\n", m, q, gfile, gbsz);
        for (int a = 0; a < m; a++) { const uint8_t *x = P + 7*(size_t)S[a]; fprintf(of, "%d %d %d %d %d %d %d\n", x[0],x[1],x[2],x[3],x[4],x[5],x[6]); }
        fclose(of);
    }
    printf("RESULT q=%d orbits=%d good=%d density=%.4f best=%d norb_used=%d exact=%d pairs_orthogonal=%ld time=%.1f\n",
           q, norb, K, dens, m, gbsz, exact, bad, now()-T0);
    return bad ? 2 : 0;
}
