/* bicay.c: bipartite bi-Cayley graphs BiCay(G; R, L, S) whose two G-orbits each meet both colour classes.
 *
 * G a group with an index-2 subgroup E (parity par(g) = 0 on E, 1 off E). Vertices (g, i), g in G, i in {0, 1}.
 * Edges: (g,0) ~ (r g, 0) for r in R;  (g,1) ~ (l g, 1) for l in L;  (g,0) ~ (s g, 1) for s in S.
 * R, L are inverse-closed subsets of G \ E, S is a subset of E containing 1 (normalised), |S| = a, |R| = |L| = b.
 * Then colour(g, i) = par(g) xor i is a proper 2-colouring and the graph is (a+b)-regular on 2|G| vertices.
 * Right multiplication (g, i) -> (g x, i) is an automorphism, so diameter <= D iff (1,0) and (1,1) reach all
 * 2|G| vertices within distance D. The (5,5) record on 360 vertices (beyond-haar-d5) is such a graph:
 * G = S3 x D30, a = 2, b = 3.
 * Cost = number of vertices at distance > D from (1,0) plus from (1,1); cost 0 <=> diameter <= D.
 *
 * usage: bicay GROUPFILE   (format of bicay_export.g: m, table, parity row, A, A automorphisms fixing E)
 * env: A (|S|, 2), B (|R| = |L|, 4), D (5), MODE (exh | sa), SECS (time cap, 600), SEED, MAXSOL (stop after this
 *      many solutions, 5), EDGES (write the best graph as an edge list), SHARD=k/K (exh: only S-reps with index = k
 *      mod K), ITERS (sa: steps per restart, 200000), T0 (2), T1 (0.05),
 *      SOL="s1 s2 .. | r1 .. | l1 .." (evaluate this graph only, write EDGES if set),
 *      NOFILTER=1 (exh: no prefilter; by default L must first cover the part of (E,0) that the L-free walks of
 *      length <= 4 from (1,0) miss, which is necessary for cost 0; "best" then ranges over the survivors only)
 * Output lines: "SOL S ... | R ... | L ..." for cost-0 graphs, "RESULT best <cost> ..." at the end.
 */
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXM 1024
static int m, D = 5, a = 2, b = 4;
static uint16_t *mul; static int inv_[MAXM], par[MAXM];
static int naut; static uint16_t *aut;
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
#define MUL(x, y) mul[(size_t)(x) * m + (y)]

/* ---- evaluation ---- */
static int S[16], R[16], L[16], nS, nR, nL;
static int dist_[2 * MAXM], stamp_[2 * MAXM], stampv = 0, q_[2 * MAXM];
static int reach_from(int o) {      /* number of vertices within distance D of (1, o) */
    stampv++;
    int h = 0, t = 0, v0 = o * m;
    stamp_[v0] = stampv; dist_[v0] = 0; q_[t++] = v0;
    while (h < t) {
        int v = q_[h++], d = dist_[v]; if (d == D) continue;
        int g = v < m ? v : v - m, i = v >= m;
        int nb[16], k = 0;
        if (!i) { for (int j = 0; j < nR; j++) nb[k++] = MUL(R[j], g); for (int j = 0; j < nS; j++) nb[k++] = m + MUL(S[j], g); }
        else { for (int j = 0; j < nL; j++) nb[k++] = m + MUL(L[j], g); for (int j = 0; j < nS; j++) nb[k++] = MUL(inv_[S[j]], g); }
        for (int j = 0; j < k; j++) { int w = nb[j]; if (stamp_[w] != stampv) { stamp_[w] = stampv; dist_[w] = d + 1; q_[t++] = w; } }
    }
    return t;
}
static int cost_full(void) { return (2 * m - reach_from(0)) + (2 * m - reach_from(1)); }

/* ---- odd classes and inverse-closed odd sets of size b ---- */
static int ncls, cls[MAXM][2], clsz[MAXM], clsof[MAXM];
static int nsets; static int *sets;    /* nsets x b elements (sorted) */
static void build_classes(void) {
    ncls = 0;
    for (int g = 0; g < m; g++) clsof[g] = -1;
    for (int g = 0; g < m; g++) if (par[g] && clsof[g] < 0) {
        int h = inv_[g]; cls[ncls][0] = g; cls[ncls][1] = h; clsz[ncls] = (h == g) ? 1 : 2; clsof[g] = clsof[h] = ncls; ncls++; }
}
static int cmpint(const void *x, const void *y) { return *(const int *)x - *(const int *)y; }
static int cur[16], ncur, curc[16]; static size_t setcap; static int *setcls, *setncl;
static long NSETMAX = 3000000;
static void gen_sets(int start, int size) {
    if (nsets > NSETMAX) return;
    if (size == b) {
        if ((size_t)nsets >= setcap) { setcap = setcap ? 2 * setcap : 1024; sets = realloc(sets, sizeof(int) * b * setcap);
            setcls = realloc(setcls, sizeof(int) * b * setcap); setncl = realloc(setncl, sizeof(int) * setcap); }
        memcpy(setcls + (size_t)nsets * b, curc, sizeof(int) * ncur); setncl[nsets] = ncur;
        int tmp[16]; memcpy(tmp, cur, sizeof(int) * b); qsort(tmp, b, sizeof(int), cmpint);
        memcpy(sets + (size_t)nsets * b, tmp, sizeof(int) * b); nsets++; return; }
    for (int c = start; c < ncls; c++) {
        if (size + clsz[c] > b) continue;
        cur[size] = cls[c][0]; if (clsz[c] == 2) cur[size + 1] = cls[c][1];
        curc[ncur++] = c;
        gen_sets(c + 1, size + clsz[c]);
        ncur--;
    }
}
/* image of a sorted set under automorphism x, sorted; compare */
static int lexcmp(const int *u, const int *v, int n) { for (int i = 0; i < n; i++) if (u[i] != v[i]) return u[i] < v[i] ? -1 : 1; return 0; }
static void img(const uint16_t *al, const int *u, int n, int *out) { for (int i = 0; i < n; i++) out[i] = al[u[i]]; qsort(out, n, sizeof(int), cmpint); }

/* ---- exact prefilter on (E,0) from (1,0): even walks of length <= 4 (backtracking allowed) ---- */
#define MAXW ((MAXM + 63) / 64)
static int WW; static uint64_t need[MAXW], *covc; static int Evec[MAXM];
#define SETB(bs, x) ((bs)[(x) >> 6] |= 1ULL << ((x) & 63))
static void prep_filter(void) {      /* uses S, R (nS = a, nR = b) */
    uint64_t c0[MAXW]; memset(c0, 0, sizeof c0);
    SETB(c0, 0);
    for (int i = 0; i < nR; i++) for (int j = 0; j < nR; j++) SETB(c0, MUL(R[j], R[i]));
    for (int i = 0; i < nS; i++) for (int j = 0; j < nS; j++) SETB(c0, MUL(inv_[S[j]], S[i]));
    for (int i1 = 0; i1 < nR; i1++) for (int i2 = 0; i2 < nR; i2++) { int x = MUL(R[i2], R[i1]);
        for (int i3 = 0; i3 < nR; i3++) { int y = MUL(R[i3], x); for (int i4 = 0; i4 < nR; i4++) SETB(c0, MUL(R[i4], y)); }
        for (int j = 0; j < nS; j++) for (int k = 0; k < nS; k++) { SETB(c0, MUL(MUL(inv_[S[k]], S[j]), x)); SETB(c0, MUL(x, MUL(inv_[S[k]], S[j]))); } }
    for (int i1 = 0; i1 < nR; i1++) for (int i3 = 0; i3 < nR; i3++) for (int j = 0; j < nS; j++) for (int k = 0; k < nS; k++)
        SETB(c0, MUL(MUL(R[i3], MUL(inv_[S[k]], S[j])), R[i1]));
    for (int j1 = 0; j1 < nS; j1++) for (int j2 = 0; j2 < nS; j2++) { int x = MUL(inv_[S[j2]], S[j1]);
        for (int j3 = 0; j3 < nS; j3++) for (int j4 = 0; j4 < nS; j4++) SETB(c0, MUL(MUL(inv_[S[j4]], S[j3]), x)); }
    for (int w = 0; w < WW; w++) need[w] = 0;
    for (int g = 0; g < m; g++) if (!par[g] && !((c0[g >> 6] >> (g & 63)) & 1)) SETB(need, g);
    for (int c = 0; c < ncls; c++) {
        uint64_t *cv = covc + (size_t)c * WW; memset(cv, 0, 8 * WW);
        for (int u = 0; u < clsz[c]; u++) { int l = cls[c][u];
            for (int j = 0; j < nS; j++) for (int k = 0; k < nS; k++) { int x = MUL(MUL(inv_[S[k]], l), S[j]);
                for (int i = 0; i < nR; i++) { SETB(cv, MUL(x, R[i])); SETB(cv, MUL(R[i], x)); }
                for (int u2 = 0; u2 < clsz[c]; u2++) SETB(cv, MUL(MUL(MUL(inv_[S[k]], cls[c][u2]), l), S[j])); } }
        for (int w = 0; w < WW; w++) cv[w] &= need[w];
    }
}
static int pass_filter(int setidx) {
    uint64_t acc[MAXW]; const int *cl = setcls + (size_t)setidx * b; int nc = setncl[setidx];
    for (int w = 0; w < WW; w++) acc[w] = 0;
    for (int i = 0; i < nc; i++) { const uint64_t *cv = covc + (size_t)cl[i] * WW; for (int w = 0; w < WW; w++) acc[w] |= cv[w]; }
    for (int i = 0; i < nc; i++) for (int j = 0; j < nc; j++) if (i != j)
        for (int u = 0; u < clsz[cl[i]]; u++) for (int v = 0; v < clsz[cl[j]]; v++) { int x = MUL(cls[cl[j]][v], cls[cl[i]][u]);
            for (int sj = 0; sj < nS; sj++) for (int sk = 0; sk < nS; sk++) SETB(acc, MUL(MUL(inv_[S[sk]], x), S[sj])); }
    for (int w = 0; w < WW; w++) if (need[w] & ~acc[w]) return 0;
    return 1;
}

static void print_sol(FILE *f, const char *tag, int c) {
    fprintf(f, "%s %d S", tag, c); for (int i = 0; i < nS; i++) fprintf(f, " %d", S[i]);
    fprintf(f, " | R"); for (int i = 0; i < nR; i++) fprintf(f, " %d", R[i]);
    fprintf(f, " | L"); for (int i = 0; i < nL; i++) fprintf(f, " %d", L[i]); fprintf(f, "\n"); fflush(f);
}
static void write_edges(const char *fn) {
    FILE *f = fopen(fn, "w"); if (!f) return;
    fprintf(f, "%d\n", 2 * m);
    for (int g = 0; g < m; g++) {
        for (int j = 0; j < nR; j++) { int h = MUL(R[j], g); if (g < h) fprintf(f, "%d %d\n", g, h); }
        for (int j = 0; j < nL; j++) { int h = MUL(L[j], g); if (g < h) fprintf(f, "%d %d\n", m + g, m + h); }
        for (int j = 0; j < nS; j++) fprintf(f, "%d %d\n", g, m + MUL(S[j], g));
    }
    fclose(f);
}

int main(int argc, char **argv) {
    if (argc < 2) { fprintf(stderr, "usage: bicay GROUPFILE\n"); return 2; }
    FILE *f = fopen(argv[1], "r"); if (!f || fscanf(f, "%d", &m) != 1 || m > MAXM) return 2;
    mul = malloc(sizeof(uint16_t) * m * m);
    for (int i = 0; i < m * m; i++) { int x; if (fscanf(f, "%d", &x) != 1) return 2; mul[i] = x; }
    for (int i = 0; i < m; i++) if (fscanf(f, "%d", &par[i]) != 1) return 2;
    if (fscanf(f, "%d", &naut) != 1) naut = 1;
    aut = malloc(sizeof(uint16_t) * m * (naut > 0 ? naut : 1));
    for (int k = 0; k < naut; k++) for (int x = 0; x < m; x++) { int y; if (fscanf(f, "%d", &y) != 1) return 2; aut[(size_t)k * m + x] = y; }
    fclose(f);
    for (int i = 0; i < m; i++) for (int j = 0; j < m; j++) if (MUL(i, j) == 0) inv_[i] = j;
    const char *gs;
    if ((gs = getenv("D"))) D = atoi(gs);
    if ((gs = getenv("A"))) a = atoi(gs);
    if ((gs = getenv("B"))) b = atoi(gs);
    double SECS = getenv("SECS") ? atof(getenv("SECS")) : 600;
    int MAXSOL = getenv("MAXSOL") ? atoi(getenv("MAXSOL")) : 5;
    const char *MODE = getenv("MODE") ? getenv("MODE") : "exh", *EDGES = getenv("EDGES");
    rs ^= getenv("SEED") ? (uint64_t)atoll(getenv("SEED")) * 0x9E3779B97F4A7C15ULL : 0; for (int i = 0; i < 20; i++) rnd();
    int shk = 0, shK = 1; if ((gs = getenv("SHARD"))) sscanf(gs, "%d/%d", &shk, &shK);
    int FILTER = getenv("NOFILTER") ? 0 : 1;
    WW = (m + 63) / 64;
    build_classes();
    covc = malloc(sizeof(uint64_t) * (ncls + 1) * WW);
    int neven = 0, even[MAXM]; for (int g = 1; g < m; g++) if (!par[g]) even[neven++] = g;
    nS = a; nR = nL = b;
    if ((gs = getenv("NSETMAX"))) NSETMAX = atol(gs);
    gen_sets(0, 0);
    if (nsets > NSETMAX) { printf("RESULT skipped: more than %ld odd %d-sets\n", NSETMAX, b); return 0; }
    fprintf(stderr, "m=%d a=%d b=%d D=%d: %d odd classes, %d inverse-closed odd %d-sets, %d automorphisms\n", m, a, b, D, ncls, nsets, b, naut);
    if (nsets == 0) { printf("RESULT best -1 (no odd set of size %d)\n", b); return 0; }
    if ((gs = getenv("SOL"))) {
        int *X[3] = {S, R, L}, *nX[3] = {&nS, &nR, &nL}, part = 0; nS = nR = nL = 0;
        for (const char *p = gs; *p; ) { if (*p == '|') { part++; p++; continue; }
            if (*p >= '0' && *p <= '9') { int v = (int)strtol(p, (char **)&p, 10); if (part < 3) X[part][(*nX[part])++] = v; } else p++; }
        for (int i = 0; i < nS; i++) if (par[S[i]]) { printf("RESULT error S element %d is odd\n", S[i]); return 1; }
        for (int i = 0; i < nR; i++) if (!par[R[i]]) { printf("RESULT error R element %d is even\n", R[i]); return 1; }
        for (int i = 0; i < nL; i++) if (!par[L[i]]) { printf("RESULT error L element %d is even\n", L[i]); return 1; }
        int c = cost_full(); print_sol(stdout, "EVAL", c); if (EDGES) write_edges(EDGES); return 0;
    }
    double t0 = now(); int best = 1 << 30, nsol = 0; long long nev = 0;
    int bS[16], bR[16], bL[16];
    if (!strcmp(MODE, "exh")) {
        /* S = {1} u T, T an (a-1)-subset of E \ {1}, canonical under Aut; R canonical under Stab(S); every L */
        int t[16], k = a - 1, nrep = 0, done = 1; long long nSR = 0;
        int *stab = malloc(sizeof(int) * (naut > 0 ? naut : 1));
        for (int i = 0; i < k; i++) t[i] = i;
        if (k == 0) t[0] = 0;
        for (;;) {
            if (k > 0 && t[k - 1] >= neven) break;
            int T[16]; for (int i = 0; i < k; i++) T[i] = even[t[i]];
            int canon = 1, ns = 0;
            for (int x = 0; x < naut && canon; x++) {
                int im[16]; img(aut + (size_t)x * m, T, k, im); int c = lexcmp(im, T, k);
                if (c < 0) canon = 0; else if (c == 0) stab[ns++] = x; }
            if (naut == 0) { stab[ns++] = -1; }
            if (canon) {
                if (nrep++ % shK == shk) {
                    S[0] = 0; for (int i = 0; i < k; i++) S[i + 1] = T[i];
                    for (int r = 0; r < nsets; r++) {
                        const int *Rr = sets + (size_t)r * b; int ok = 1;
                        for (int y = 0; y < ns && ok; y++) { if (stab[y] < 0) continue; int im[16]; img(aut + (size_t)stab[y] * m, Rr, b, im); if (lexcmp(im, Rr, b) < 0) ok = 0; }
                        if (!ok) continue;
                        nSR++;
                        memcpy(R, Rr, sizeof(int) * b);
                        if (FILTER) prep_filter();
                        for (int l = 0; l < nsets; l++) {
                            if (FILTER && !pass_filter(l)) continue;
                            memcpy(L, sets + (size_t)l * b, sizeof(int) * b);
                            nev++;
                            int c0 = 2 * m - reach_from(0);
                            if (c0 > best) continue;
                            int c = c0 + (2 * m - reach_from(1));
                            if (c < best) { best = c; memcpy(bS, S, sizeof S); memcpy(bR, R, sizeof R); memcpy(bL, L, sizeof L);
                                fprintf(stderr, "  best %d at %.1fs (S-rep %d, %lld evals)\n", best, now() - t0, nrep, nev); }
                            if (c == 0) { print_sol(stdout, "SOL", 0); if (++nsol >= MAXSOL) goto out_exh; }
                        }
                        if (now() - t0 > SECS) { done = 0; goto out_exh; }
                    }
                }
            }
            if (k == 0) break;
            /* next k-subset */
            int i = k - 1; while (i >= 0 && t[i] == neven - k + i) i--;
            if (i < 0) break;
            t[i]++; for (int j = i + 1; j < k; j++) t[j] = t[j - 1] + 1;
        }
    out_exh:
        fprintf(stderr, "exh: %d S-reps, %lld (S,R) pairs, %lld evaluations, %.1fs, %s\n", nrep, nSR, nev, now() - t0,
                done && nsol < MAXSOL ? "COMPLETE" : "partial");
        printf("RESULT best %d mode exh sols %d evals %lld time %.1f %s\n", best, nsol, nev, now() - t0, done && nsol < MAXSOL ? "COMPLETE" : "PARTIAL");
    } else {
        /* simulated annealing over (S, R, L) */
        long ITERS = getenv("ITERS") ? atol(getenv("ITERS")) : 200000;
        double T0 = getenv("T0") ? atof(getenv("T0")) : 2, T1 = getenv("T1") ? atof(getenv("T1")) : 0.05;
        int restarts = 0;
        while (now() - t0 < SECS && nsol < MAXSOL) {
            restarts++;
            S[0] = 0; for (int i = 1; i < a; i++) { int x, dup; do { x = even[rnd() % neven]; dup = 0; for (int j = 1; j < i; j++) dup |= S[j] == x; } while (dup); S[i] = x; }
            int ri = rnd() % nsets, li = rnd() % nsets;
            memcpy(R, sets + (size_t)ri * b, sizeof(int) * b); memcpy(L, sets + (size_t)li * b, sizeof(int) * b);
            int c = cost_full(); nev++;
            for (long it = 0; it < ITERS && now() - t0 < SECS; it++) {
                double T = T0 * pow(T1 / T0, (double)it / ITERS);
                int oS[16], oR[16], oL[16]; memcpy(oS, S, sizeof S); memcpy(oR, R, sizeof R); memcpy(oL, L, sizeof L);
                int mv = rnd() % 3;
                if (mv == 0 && a > 1) { int i = 1 + rnd() % (a - 1), x, dup; do { x = even[rnd() % neven]; dup = 0; for (int j = 1; j < a; j++) dup |= S[j] == x; } while (dup); S[i] = x; }
                else { int *X = (mv == 1 || a == 1) ? R : L;
                    /* replace the set by a random set sharing all but one class (or a random set, 10%) */
                    if (rnd01() < 0.1) memcpy(X, sets + (size_t)(rnd() % nsets) * b, sizeof(int) * b);
                    else { int tries = 0; for (;;) { const int *Y = sets + (size_t)(rnd() % nsets) * b; int common = 0;
                            for (int u = 0; u < b; u++) for (int v = 0; v < b; v++) common += X[u] == Y[v];
                            if (common >= b - 2 || ++tries > 200) { memcpy(X, Y, sizeof(int) * b); break; } } } }
                int c2 = cost_full(); nev++;
                if (c2 <= c || rnd01() < exp((c - c2) / T)) { c = c2;
                    if (c < best) { best = c; memcpy(bS, S, sizeof S); memcpy(bR, R, sizeof R); memcpy(bL, L, sizeof L);
                        fprintf(stderr, "  best %d at %.1fs (restart %d)\n", best, now() - t0, restarts); }
                    if (c == 0) { print_sol(stdout, "SOL", 0); nsol++; break; } }
                else { memcpy(S, oS, sizeof S); memcpy(R, oR, sizeof R); memcpy(L, oL, sizeof L); }
            }
        }
        printf("RESULT best %d mode sa sols %d evals %lld restarts %d time %.1f\n", best, nsol, nev, restarts, now() - t0);
    }
    if (best < (1 << 30)) {
        memcpy(S, bS, sizeof S); memcpy(R, bR, sizeof R); memcpy(L, bL, sizeof L);
        print_sol(stdout, "BEST", cost_full());
        if (EDGES) write_edges(EDGES);
    }
    return 0;
}
