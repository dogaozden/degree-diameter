/* tri.c: tri-Cayley graphs TriCay(G; R0,R1,R2; S01,S12,S02) on 3|G| vertices (card c1, round s65r1).
 *
 * G: group with index-2 subgroup E, parity par(g) = 0 on E, 1 off E (bicay format file).
 * Vertices v = i*m + g, i in {0,1,2}.  Colour(g,i) = par(g) xor c_i with c = (0,1,0) (WLOG, see notes).
 * Edges: loops (g,i) ~ (r g, i), r in R_i (inverse-closed, odd);
 *        links (g,i) ~ (s g, j) for s in S_ij (i<j stored), with S_ji = S_ij^{-1}.
 * Parities: S01, S12 subset of E (normalised: contain 1), S02 subset of G\E (odd), R_i odd.
 * Degree of orbit i: |R_i| + sum_j |S_ij| = 6.  Right multiplication is an automorphism, so the diameter is
 * <= D iff BFS from (1,0), (1,1), (1,2) reaches all 3m vertices within D.
 * cost = sum over the 3 sources of vertices at distance > D.
 *
 * usage: tri GROUPFILE     env: SPLIT="a b c" (|S01|,|S02|,|S12|; |R0|=6-a-b, |R1|=6-a-c, |R2|=6-b-c)
 *        SECS (60), SEED, ITERS (200000), T0 (2), T1 (0.05), D (5), OUT (edge list of best graph),
 *        SOL="v:..."  (optional: not used)
 * Output: "RESULT best <cost> ..." and "BEST ..." lines; OUT gets the best graph as an edge list (n = 3m).
 */
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXM 1024
static int m, D = 5;
static uint16_t *mul;
static int inv_[MAXM], par[MAXM];
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
#define MUL(x, y) mul[(size_t)(x) * m + (y)]

/* ---- classes of odd elements (inverse pairs / odd involutions) ---- */
static int ncls, clsA[MAXM], clsB[MAXM], clsSz[MAXM], clsof[MAXM];
static int neven, even_[MAXM];   /* even non-identity elements */
static int nodd, odd_[MAXM];

/* ---- state ---- */
static int a, b, c, r[3];          /* a=|S01|, b=|S02|, c=|S12|, r[i]=|R_i| */
static int S01[16], S02[16], S12[16];
static int rc[3][8], nrc[3];       /* R_i as class ids */
/* moves: for orbit i, list of (x, j): neighbour (x*g, j) */
static int mvx[3][32], mvj[3][32], mvn[3];

static void build_moves(void) {
    for (int i = 0; i < 3; i++) mvn[i] = 0;
    for (int i = 0; i < 3; i++) for (int k = 0; k < nrc[i]; k++) {
        int cl = rc[i][k];
        mvx[i][mvn[i]] = clsA[cl]; mvj[i][mvn[i]] = i; mvn[i]++;
        if (clsSz[cl] == 2) { mvx[i][mvn[i]] = clsB[cl]; mvj[i][mvn[i]] = i; mvn[i]++; }
    }
    for (int k = 0; k < a; k++) { int s = S01[k];
        mvx[0][mvn[0]] = s; mvj[0][mvn[0]] = 1; mvn[0]++; mvx[1][mvn[1]] = inv_[s]; mvj[1][mvn[1]] = 0; mvn[1]++; }
    for (int k = 0; k < b; k++) { int s = S02[k];
        mvx[0][mvn[0]] = s; mvj[0][mvn[0]] = 2; mvn[0]++; mvx[2][mvn[2]] = inv_[s]; mvj[2][mvn[2]] = 0; mvn[2]++; }
    for (int k = 0; k < c; k++) { int s = S12[k];
        mvx[1][mvn[1]] = s; mvj[1][mvn[1]] = 2; mvn[1]++; mvx[2][mvn[2]] = inv_[s]; mvj[2][mvn[2]] = 1; mvn[2]++; }
}

/* ---- evaluation: BFS from (1,i0), count reached within D ---- */
static int dist_[3 * MAXM], stamp_[3 * MAXM], stampv = 0, q_[3 * MAXM];
static int reach_from(int i0) {
    stampv++;
    int h = 0, t = 0, v0 = i0 * m;
    stamp_[v0] = stampv; dist_[v0] = 0; q_[t++] = v0;
    while (h < t) {
        int v = q_[h++], d = dist_[v]; if (d == D) continue;
        int g = v % m, i = v / m;
        for (int k = 0; k < mvn[i]; k++) {
            int w = mvj[i][k] * m + MUL(mvx[i][k], g);
            if (stamp_[w] != stampv) { stamp_[w] = stampv; dist_[w] = d + 1; q_[t++] = w; }
        }
    }
    return t;
}
static int cost_full(void) { build_moves(); int cst = 0; for (int i0 = 0; i0 < 3; i0++) cst += 3 * m - reach_from(i0); return cst; }

static void write_edges(const char *fn) {
    FILE *f = fopen(fn, "w"); if (!f) return;
    fprintf(f, "%d\n", 3 * m);
    for (int i = 0; i < 3; i++) for (int g = 0; g < m; g++) {
        int v = i * m + g;
        for (int k = 0; k < mvn[i]; k++) { int w = mvj[i][k] * m + MUL(mvx[i][k], g); if (v < w) fprintf(f, "%d %d\n", v, w); }
    }
    fclose(f);
}
static void print_state(FILE *f, const char *tag, int cst) {
    fprintf(f, "%s %d S01", tag, cst); for (int k = 0; k < a; k++) fprintf(f, " %d", S01[k]);
    fprintf(f, " | S12"); for (int k = 0; k < c; k++) fprintf(f, " %d", S12[k]);
    fprintf(f, " | S02"); for (int k = 0; k < b; k++) fprintf(f, " %d", S02[k]);
    for (int i = 0; i < 3; i++) { fprintf(f, " | R%d", i); for (int k = 0; k < nrc[i]; k++) fprintf(f, " %d", clsA[rc[i][k]]);
        for (int k = 0; k < nrc[i]; k++) if (clsSz[rc[i][k]] == 2) fprintf(f, "/%d", clsB[rc[i][k]]); }
    fprintf(f, "\n"); fflush(f);
}

/* random composition of R_i with total size r, classes distinct */
static int pick_class_of_size(int sz, int *present_ids, int npres) {
    int cand[MAXM], nc = 0;
    for (int k = 0; k < ncls; k++) if (clsSz[k] == sz) {
        int ok = 1; for (int p = 0; p < npres; p++) if (present_ids[p] == k) { ok = 0; break; }
        if (ok) cand[nc++] = k; }
    if (nc == 0) return -1;
    return cand[rnd() % nc];
}
static int init_R(int i) {
    nrc[i] = 0; int tot = 0;
    while (tot < r[i]) {
        int rem = r[i] - tot; int sz = (rem >= 2 && rnd() % 2) ? 2 : 1;
        int k = pick_class_of_size(sz, rc[i], nrc[i]);
        if (k < 0) { sz = 3 - sz; k = pick_class_of_size(sz, rc[i], nrc[i]); if (k < 0 || sz > rem) return 0; }
        rc[i][nrc[i]++] = k; tot += sz;
    }
    return 1;
}
static int in_list(const int *x, int n, int v) { for (int k = 0; k < n; k++) if (x[k] == v) return 1; return 0; }
static void init_sets(void) {
    S01[0] = 0; for (int k = 1; k < a; k++) { int x; do { x = even_[rnd() % neven]; } while (in_list(S01, k, x)); S01[k] = x; }
    S12[0] = 0; for (int k = 1; k < c; k++) { int x; do { x = even_[rnd() % neven]; } while (in_list(S12, k, x)); S12[k] = x; }
    for (int k = 0; k < b; k++) { int x; do { x = odd_[rnd() % nodd]; } while (in_list(S02, k, x)); S02[k] = x; }
}

int main(int argc, char **argv) {
    if (argc < 2) { fprintf(stderr, "usage: tri GROUPFILE\n"); return 2; }
    FILE *f = fopen(argv[1], "r"); if (!f || fscanf(f, "%d", &m) != 1 || m > MAXM) return 2;
    mul = malloc(sizeof(uint16_t) * m * m);
    for (int i = 0; i < m * m; i++) { int x; if (fscanf(f, "%d", &x) != 1) return 2; mul[i] = x; }
    for (int i = 0; i < m; i++) if (fscanf(f, "%d", &par[i]) != 1) return 2;
    fclose(f);
    for (int i = 0; i < m; i++) for (int j = 0; j < m; j++) if (MUL(i, j) == 0) inv_[i] = j;
    const char *gs;
    if ((gs = getenv("D"))) D = atoi(gs);
    a = 2; b = 2; c = 2;
    if ((gs = getenv("SPLIT"))) sscanf(gs, "%d %d %d", &a, &b, &c);
    r[0] = 6 - a - b; r[1] = 6 - a - c; r[2] = 6 - b - c;
    if (r[0] < 0 || r[1] < 0 || r[2] < 0) { printf("RESULT infeasible split\n"); return 1; }
    double SECS = getenv("SECS") ? atof(getenv("SECS")) : 60;
    long ITERS = getenv("ITERS") ? atol(getenv("ITERS")) : 200000;
    double T0 = getenv("T0") ? atof(getenv("T0")) : 2, T1 = getenv("T1") ? atof(getenv("T1")) : 0.05;
    rs ^= getenv("SEED") ? (uint64_t)atoll(getenv("SEED")) * 0x9E3779B97F4A7C15ULL : 0; for (int i = 0; i < 20; i++) rnd();
    const char *OUT = getenv("OUT");
    /* classes of odd elements */
    ncls = 0; neven = 0; nodd = 0;
    for (int g = 0; g < m; g++) clsof[g] = -1;
    for (int g = 1; g < m; g++) if (!par[g]) even_[neven++] = g;
    for (int g = 0; g < m; g++) if (par[g]) odd_[nodd++] = g;
    for (int g = 0; g < m; g++) if (par[g] && clsof[g] < 0) {
        int h = inv_[g]; clsA[ncls] = g; clsB[ncls] = h; clsSz[ncls] = (h == g) ? 1 : 2; clsof[g] = clsof[h] = ncls; ncls++; }
    int nsing = 0; for (int k = 0; k < ncls; k++) nsing += clsSz[k] == 1;
    fprintf(stderr, "m=%d split a=%d b=%d c=%d r=(%d,%d,%d) even=%d odd=%d odd-classes=%d (involutions %d)\n",
            m, a, b, c, r[0], r[1], r[2], neven, nodd, ncls, nsing);
    if (a > 0 && (a == 0)) {}
    /* feasibility of R compositions */
    for (int i = 0; i < 3; i++) if (r[i] % 2 == 1 && nsing == 0) { printf("RESULT infeasible: odd |R| but no odd involution\n"); return 1; }
    if (a > neven + 1 || c > neven + 1 || b > nodd) { printf("RESULT infeasible: too few elements\n"); return 1; }

    double t0 = now();
    int best = 1 << 30; int bS01[16], bS12[16], bS02[16], bR[3][8], bnR[3], bnrc[3];
    long long nev = 0; int restarts = 0;
    while (now() - t0 < SECS) {
        restarts++;
        int ok = 1; for (int i = 0; i < 3; i++) ok &= init_R(i);
        if (!ok) continue;
        init_sets();
        build_moves();
        int cst = cost_full(); nev++;
        for (long it = 0; it < ITERS && now() - t0 < SECS; it++) {
            double T = T0 * pow(T1 / T0, (double)it / ITERS);
            int oS01[16], oS12[16], oS02[16], oRc[3][8], oN[3];
            memcpy(oS01, S01, sizeof S01); memcpy(oS12, S12, sizeof S12); memcpy(oS02, S02, sizeof S02);
            memcpy(oRc, rc, sizeof rc); memcpy(oN, nrc, sizeof nrc);
            /* choose a slot: 0 = S01 (non-identity), 1 = S12, 2 = S02, 3 = R class */
            int tot = (a > 1 ? a - 1 : 0) + (c > 1 ? c - 1 : 0) + b + (r[0] + r[1] + r[2] > 0 ? nrc[0] + nrc[1] + nrc[2] : 0);
            if (tot == 0) break;
            int pick = rnd() % tot, kind = -1, idx = 0;
            int n0 = (a > 1 ? a - 1 : 0), n1 = (c > 1 ? c - 1 : 0);
            if (pick < n0) { kind = 0; idx = 1 + pick; }
            else if (pick < n0 + n1) { kind = 1; idx = 1 + pick - n0; }
            else if (pick < n0 + n1 + b) { kind = 2; idx = pick - n0 - n1; }
            else { int q = pick - n0 - n1 - b; kind = 3;
                for (int i = 0; i < 3; i++) { if (q < nrc[i]) { idx = i * 8 + q; break; } q -= nrc[i]; } }
            if (kind == 0) { int x; do { x = even_[rnd() % neven]; } while (in_list(S01, a, x)); S01[idx] = x; }
            else if (kind == 1) { int x; do { x = even_[rnd() % neven]; } while (in_list(S12, c, x)); S12[idx] = x; }
            else if (kind == 2) { int x; do { x = odd_[rnd() % nodd]; } while (in_list(S02, b, x)); S02[idx] = x; }
            else { int i = idx / 8, k = idx % 8; int cl = rc[i][k]; int sz = clsSz[cl];
                int nc = pick_class_of_size(sz, rc[i], nrc[i]);
                if (nc < 0) continue;
                rc[i][k] = nc; }
            build_moves();
            int c2 = cost_full(); nev++;
            if (c2 <= cst || rnd01() < exp((cst - c2) / T)) { cst = c2;
                if (cst < best) { best = cst; memcpy(bS01, S01, sizeof S01); memcpy(bS12, S12, sizeof S12); memcpy(bS02, S02, sizeof S02);
                    memcpy(bR, rc, sizeof rc); memcpy(bnR, nrc, sizeof nrc);
                    fprintf(stderr, "  best %d at %.1fs (restart %d it %ld)\n", best, now() - t0, restarts, it); }
                if (cst == 0) break;
            } else {
                memcpy(S01, oS01, sizeof S01); memcpy(S12, oS12, sizeof S12); memcpy(S02, oS02, sizeof S02);
                memcpy(rc, oRc, sizeof rc); memcpy(nrc, oN, sizeof nrc);
            }
        }
        if (best == 0) break;
    }
    /* restore best and report */
    memcpy(S01, bS01, sizeof S01); memcpy(S12, bS12, sizeof S12); memcpy(S02, bS02, sizeof S02);
    memcpy(rc, bR, sizeof rc); memcpy(nrc, bnR, sizeof nrc);
    build_moves();
    int fin = cost_full();
    printf("RESULT best %d split %d %d %d m %d n %d restarts %d evals %lld time %.1f\n", fin, a, b, c, m, 3 * m, restarts, nev, now() - t0);
    print_state(stdout, "BEST", fin);
    if (OUT && best < (1 << 30)) { write_edges(OUT); }
    return 0;
}
