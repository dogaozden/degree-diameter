/* c04: degree-17 route-chart lift over a Haar controller H(G,S), |S|=4 (letter c = position in S).
   Letter 0 carries the 5-element translation set {lam*b_0 : lam in F4} u {e}; letters 1..3 carry {lam*b_c}.
   Lift: A(g,x) ~ B(g s_c, A_c x + w) for w in W_c; x in F4^4 (256 fibre values).
   G acts by left multiplication on the controller and commutes with the lift, so the all-pairs condition
   reduces to 512 representatives A(1,x), B(1,y).  cost = sum over representatives of vertices NOT within
   distance 5 (0 iff the lift has diameter <= 5).
   groups: Z_n x| Z_k (r^k = 1 mod n), elements (a,i) -> index a*k+i, identity 0.
   usage: haar17 chart seconds_per_group seed [outprefix]   (env LO, HI: order range, default 69..80) */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdint.h>
#include <time.h>

static const int MUL4[4][4] = {{0,0,0,0},{0,1,2,3},{0,2,3,1},{0,3,1,2}};
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t xr(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline int rnd(int n) { return (int)(xr() % (uint64_t)n); }
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }
static int gcd_(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }

#define DEG 17
#define NF 256
int M, *gm, *gi, *rp;
int chA[4][16], chB[4][4];
int linA[4][NF], linInv[4][NF];
int S[4], eV, Wv[4][5], nW[4];
int NV, *nb, *vis, *qu, stamp = 0;

static int vid(const int *v) { return v[0] | (v[1] << 2) | (v[2] << 4) | (v[3] << 6); }
static void unid(int id, int *v) { for (int i = 0; i < 4; i++) v[i] = (id >> (2 * i)) & 3; }

static void build_group(int n, int k, int r) {
    M = n * k;
    rp = realloc(rp, sizeof(int) * k); rp[0] = 1 % n;
    for (int i = 1; i < k; i++) rp[i] = (rp[i - 1] * r) % n;
    gm = realloc(gm, sizeof(int) * M * M); gi = realloc(gi, sizeof(int) * M);
    for (int a = 0; a < n; a++) for (int i = 0; i < k; i++) for (int b = 0; b < n; b++) for (int j = 0; j < k; j++)
        gm[(a * k + i) * M + (b * k + j)] = ((a + rp[i] * b) % n) * k + ((i + j) % k);
    for (int g = 0; g < M; g++) for (int h = 0; h < M; h++) if (gm[g * M + h] == 0) gi[g] = h;
}

static int setup_chart(const char *f) {
    FILE *fp = fopen(f, "r"); if (!fp) return 0;
    for (int c = 0; c < 4; c++) for (int i = 0; i < 16; i++) if (fscanf(fp, "%d", &chA[c][i]) != 1) return 0;
    for (int c = 0; c < 4; c++) for (int i = 0; i < 4; i++) if (fscanf(fp, "%d", &chB[c][i]) != 1) return 0;
    fclose(fp); return 1;
}

static int matrices_ok(void) {
    for (int c = 0; c < 4; c++) {
        for (int x = 0; x < NF; x++) {
            int v[4], o[4]; unid(x, v);
            for (int r = 0; r < 4; r++) { int s = 0; for (int q = 0; q < 4; q++) s ^= MUL4[chA[c][r * 4 + q]][v[q]]; o[r] = s; }
            linA[c][x] = vid(o);
        }
        int seen[NF]; memset(seen, 0, sizeof seen);
        for (int x = 0; x < NF; x++) { if (seen[linA[c][x]]) return 0; seen[linA[c][x]] = 1; }
        for (int x = 0; x < NF; x++) linInv[c][linA[c][x]] = x;
    }
    return 1;
}

/* rebuild translations and neighbour table for the current S, eV; returns 0 if eV is not a valid extra vector */
static int rebuild(void) {
    for (int c = 0; c < 4; c++) {
        nW[c] = 0;
        for (int l = 0; l < 4; l++) { int v[4]; for (int i = 0; i < 4; i++) v[i] = MUL4[l][chB[c][i]]; Wv[c][nW[c]++] = vid(v); }
    }
    for (int l = 0; l < 4; l++) if (Wv[0][l] == eV) return 0;
    Wv[0][nW[0]++] = eV;
    NV = 2 * M * NF;
    for (int v = 0; v < NV; v++) {
        int *p = nb + (size_t)v * DEG, j = 0;
        if (v < M * NF) {
            int g = v / NF, x = v % NF;
            for (int c = 0; c < 4; c++) for (int t = 0; t < nW[c]; t++)
                p[j++] = M * NF + gm[g * M + S[c]] * NF + (linA[c][x] ^ Wv[c][t]);
        } else {
            int u = v - M * NF, h = u / NF, y = u % NF;
            for (int c = 0; c < 4; c++) for (int t = 0; t < nW[c]; t++)
                p[j++] = gm[h * M + gi[S[c]]] * NF + linInv[c][y ^ Wv[c][t]];
        }
    }
    return 1;
}

/* sum over the 512 representatives of unreached vertices within distance 5; stops once above limit */
static int STEP = 1;   /* screening: every STEP-th representative, scaled by STEP */
static long cost_lim(long limit) {
    long tot = 0;
    for (int s = 0; s < 512; s += STEP) {
        int src = s < NF ? s : (M * NF + (s - NF));   /* identity group element is 0 */
        stamp++;
        int head = 0, tail = 0; qu[tail++] = src; vis[src] = stamp;
        for (int d = 0; d < 5; d++) {
            int end = tail;
            for (; head < end; head++) {
                const int *p = nb + (size_t)qu[head] * DEG;
                for (int j = 0; j < DEG; j++) { int u = p[j]; if (vis[u] != stamp) { vis[u] = stamp; qu[tail++] = u; } }
            }
        }
        tot += (long)(NV - tail) * STEP;
        if (tot > limit) return tot;
    }
    return tot;
}

static int in_set(int x, const int *a, int n) { for (int i = 0; i < n; i++) if (a[i] == x) return 1; return 0; }

static void write_edges(const char *fn) {
    FILE *f = fopen(fn, "w"); if (!f) return;
    fprintf(f, "%d\n", NV);
    for (int v = 0; v < M * NF; v++) { const int *p = nb + (size_t)v * DEG; for (int j = 0; j < DEG; j++) fprintf(f, "%d %d\n", v, p[j]); }
    fclose(f);
}

/* simulated annealing over (S ordered, eV) for the group currently built; returns best cost */
static long n_evals = 0;
static long anneal(double secs, int *bS, int *bE) {
    int ok = 0; STEP = getenv("STEP") ? atoi(getenv("STEP")) : 1;
    while (!ok) {
        for (int i = 0; i < 4; i++) { int g; do { g = 1 + rnd(M - 1); } while (in_set(g, S, i)); S[i] = g; }
        eV = rnd(NF);
        ok = rebuild();
    }
    long cur = cost_lim(1L << 60), best = cur;
    memcpy(bS, S, sizeof S); *bE = eV;
    double T0 = 0.02 * (double)cur + 1.0, T1 = 1.0, t0 = now(), tnow;
    while ((tnow = now() - t0) < secs && best > 0) {
        double T = T0 * pow(T1 / T0, tnow / secs);
        int oS[4], oE = eV; memcpy(oS, S, sizeof S);
        int mv = rnd(3);
        if (mv == 0) { int i = rnd(4), g; do { g = 1 + rnd(M - 1); } while (in_set(g, S, 4)); S[i] = g; }
        else if (mv == 1) eV = rnd(NF);
        else { int i = rnd(4), j = rnd(4), t = S[i]; S[i] = S[j]; S[j] = t; }
        if (!rebuild()) { memcpy(S, oS, sizeof S); eV = oE; rebuild(); continue; }
        double u = ((xr() >> 11) + 1) * (1.0 / 9007199254740992.0);
        double thr = (double)cur - T * log(u);
        long c = cost_lim((long)thr); n_evals++;
        if ((double)c <= thr) {
            cur = c;
            if (cur < best) { best = cur; memcpy(bS, S, sizeof S); *bE = eV; }
        } else { memcpy(S, oS, sizeof S); eV = oE; rebuild(); }
    }
    return best;
}

int main(int argc, char **argv) {
    if (argc < 4) { fprintf(stderr, "usage: haar17 chart seconds_per_group seed [outprefix]\n"); return 1; }
    if (!setup_chart(argv[1])) { fprintf(stderr, "chart read fail\n"); return 2; }
    if (!matrices_ok()) { fprintf(stderr, "chart matrices singular\n"); return 3; }
    double secs = atof(argv[2]);
    rs ^= (uint64_t)atoll(argv[3]) * 0x9E3779B97F4A7C15ULL;
    for (int i = 0; i < 10; i++) xr();
    const char *outp = argc > 4 ? argv[4] : "best";
    int lo = 69, hi = 80;
    if (getenv("LO")) lo = atoi(getenv("LO"));
    if (getenv("HI")) hi = atoi(getenv("HI"));
    int maxN = 2 * 80 * NF;
    nb = malloc(sizeof(int) * (size_t)maxN * DEG);
    vis = calloc(maxN, sizeof(int));
    qu = malloc(sizeof(int) * maxN);
    long global_best = -1;
    if (getenv("EVAL")) {  /* EVAL="n k r s0 s1 s2 s3 e" : evaluate one configuration, dump edges to env DUMP */
        int n_, k_, r_, s0, s1, s2, s3, e_;
        sscanf(getenv("EVAL"), "%d %d %d %d %d %d %d %d", &n_, &k_, &r_, &s0, &s1, &s2, &s3, &e_);
        build_group(n_, k_, r_); S[0] = s0; S[1] = s1; S[2] = s2; S[3] = s3; eV = e_;
        if (!rebuild()) { printf("invalid e\n"); return 4; }
        printf("EVAL cost=%ld NV=%d\n", cost_lim(1L << 60), NV);
        if (getenv("DUMP")) write_edges(getenv("DUMP"));
        return 0;
    }
    for (int m = lo; m <= hi; m++) {
        for (int k = 1; k <= m; k++) {
            if (m % k) continue;
            int n = m / k;
            for (int r = 1; r < n || (k == 1 && r == 1); r++) {
                if (k == 1) { if (r != 1) break; }
                else if (n < 2 || gcd_(r, n) != 1) continue;
                long p = 1 % n;
                for (int i = 0; i < k; i++) p = (p * r) % n;
                if (k > 1 && p != 1 % n) continue;
                if (k == 1 && n == 1) continue;
                /* k == 1: cyclic Z_m with n = m (r = 1 only) */
                if (k == 1) { build_group(m, 1, 1); }
                else build_group(n, k, r);
                int bS[4], bE = 0;
                long best = anneal(secs, bS, &bE);
                printf("G m=%d n=%d k=%d r=%d best=%ld evals=%ld S=%d,%d,%d,%d e=%d\n", M, n, k, r, best, n_evals, bS[0], bS[1], bS[2], bS[3], bE); n_evals = 0;
                fflush(stdout);
                if (global_best < 0 || best < global_best) global_best = best;
                STEP = 1;
                if (best == 0) {
                    memcpy(S, bS, sizeof S); eV = bE; rebuild(); STEP = 1;
                    if (cost_lim(0) == 0) {
                        char fn[256]; sprintf(fn, "%s_n%d.edges", outp, NV);
                        write_edges(fn);
                        printf("WROTE %s\n", fn);
                    }
                    fflush(stdout);
                }
                if (k == 1) break;
            }
        }
    }
    printf("GLOBAL_BEST %ld\n", global_best);
    return 0;
}
