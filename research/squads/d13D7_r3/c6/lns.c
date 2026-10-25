/* lns.c: squad round 3, card c6: large neighbourhood search (LNS) with GEOMETRIC REGION BLOCKS.
   Derived from research/squads/d13D7_r2/c6/lns.c (round 2). Its state, exact step, acceptance rule and conflict-driven
   moves are kept; block types defined by geometry (not by conflicts) are added.

   Problem: R = a set of pairwise opposite points of H(11) (points of Q(6,11); x, y opposite iff B(x,y) != 0 mod 11).
   State: inR, cnt[x] = #{r in R, r != x, B(x,r) = 0}; points of R have cnt = 0.
   Move: remove a block D from R; candidates C = points not in R with cnt = 0 after the removal (D plus the points of
   perp(D) blocked only by D); exact maximum pairwise-opposite subset of C (branch and bound, greedy colouring bound,
   node limit) with lower bound |D|: larger -> accept; equal -> accepted with probability PPLAT (random maximal subset of
   C); otherwise D is restored.

   usage: lns HEXFILE INIT_IDX OUT_IDX CPU_SECONDS SEED [MODE CMAX JMAX GMAX PFIBER NODELIMIT PGEO BMIN BMAX PPLAT]
     MODE 0 (default): LNS.  MODE 1: histogram of c[x] over non-R points, self-test only.
     MODE 2: probe, writes no output: for each geometric type 150 sampled blocks; prints mean |D|, mean |C|, cases with
             |C| > MAXC, node-limit hits, and how often the exact step finds a larger set. R is restored every time.
     PGEO (default 0.7): probability that a move uses a geometric block (G1, G2, G3 with equal probability); otherwise
             the round-2 moves (fibre move with probability PFIBER, else the conflict-driven block).
     BMIN, BMAX (default 50, 120): a geometric block is grown by uniting regions of one type until it holds at least
             BMIN points of R; a region that would push it above BMAX is rejected.
     PPLAT (default 0.5): probability of accepting an equal-size set (random maximal subset of C) when no larger set is found.

   Geometric block types. A block is R n X for a region X of H(11):
     G1 point:      X = z^perp = {y : B(z,y) = 0}, z a uniform random point of Q(6,11) outside R. R n z^perp is the set
                    N_R(z) of R-conflicts of z (about |R|/11 points); z itself becomes a candidate, since all its
                    conflicts were removed. A block unites several such sets N_R(z_1) u N_R(z_2) u ...
     G2 hyperplane: X = v^perp for a uniform random nonzero vector v of F_11^7, singular or not. B(v,y) = w(v).y with
                    w(v) = (v4, v5, v6, -2 v3, v0, v1, v2), and v -> w(v) is a bijection of F_11^7, so v is drawn as a
                    uniform nonzero coefficient vector a = w(v) and the block is {r in R : a.r = 0 mod 11}.
                    A block unites several such hyperplane sections.
     G3 line tube:  X = Near4(L), the points at incidence distance <= 4 from a line L: L itself and the 1452 points
                    collinear with a point of L (1464 points). R n Near4(L) has at most 12 points (two points of R
                    collinear with a common point of L are non-opposite), so the tube grows by a random walk of lines:
                    each new line meets a line already in the tube, and the R points of its Near4 are united into D.
   Regions are added one at a time until the block holds BMIN points, so a typical block has 50-120 points. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>

#define QQ 11
#define KK 12          /* q+1: lines per point and points per line */
#define MAXC 1024      /* cap on the candidate set for the exact step */
#define PMAX 16200     /* |perp(x)| = 16104 */
#define NEAR4 1464     /* |Near4(L)| = 12 + 12*11*11 */
#define MAXLINES 400   /* cap on the number of lines of one tube */
#define NKIND 5        /* block kinds: 0 conflict-driven, 1 fibre, 2 G1 point, 3 G2 hyperplane, 4 G3 line tube */

static int N, NL;
static int32_t *lp, *pl;   /* NL x KK point indices of lines; N x KK line indices of points */
static uint8_t *co;        /* N x 7 coordinates */
static int8_t *wd;         /* N x 7: B(x,y) = sum_k wd[x][k]*co[y][k] mod 11 */
static uint8_t *inR, *mark, *inD, *inS;
static int32_t *cnt;       /* cnt[x] = #{r in R, r != x, B(x,r) = 0} */
static int32_t *R, *posR; static int m = 0;
static int32_t tbuf[PMAX], tbuf2[PMAX], tR[PMAX], tnear[NEAR4 + 8];
static uint32_t *nst; static uint32_t nstamp = 0;

static uint64_t rs = 0x9E3779B97F4A7C15ULL;
static inline uint64_t rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }

static inline int Bxy(int x, int y) {
    const int8_t *w = wd + 7L * x; const uint8_t *v = co + 7L * y;
    int s = w[0]*v[0] + w[1]*v[1] + w[2]*v[2] + w[3]*v[3] + w[4]*v[4] + w[5]*v[5] + w[6]*v[6];
    s %= QQ; return s < 0 ? s + QQ : s;
}

/* all y != x with B(x,y) = 0 (16104 of them), written to out */
static int perp(int x, int32_t *out) {
    int n = 0;
    for (int a = 0; a < KK; a++) {
        int L1 = pl[(size_t)x * KK + a];
        for (int b = 0; b < KK; b++) {
            int p1 = lp[(size_t)L1 * KK + b];
            if (p1 == x) continue;
            out[n++] = p1;
            for (int d = 0; d < KK; d++) {
                int L2 = pl[(size_t)p1 * KK + d];
                if (L2 == L1) continue;
                for (int e = 0; e < KK; e++) {
                    int p2 = lp[(size_t)L2 * KK + e];
                    if (p2 != p1) out[n++] = p2;
                }
            }
        }
    }
    return n;
}

static void addR(int x) {
    inR[x] = 1; posR[x] = m; R[m++] = x;
    int n = perp(x, tbuf);
    for (int i = 0; i < n; i++) cnt[tbuf[i]]++;
}
static void delR(int x) {
    inR[x] = 0; int p = posR[x]; R[p] = R[--m]; posR[R[p]] = p;
    int n = perp(x, tbuf);
    for (int i = 0; i < n; i++) cnt[tbuf[i]]--;
}

/* ---- exact maximum pairwise-opposite subset (max clique of the opposition graph) on local indices ---- */
static uint8_t A[MAXC][MAXC];          /* A[i][j] = 1 iff i, j opposite */
static int nC, Cv[MAXC], perm[MAXC];
static int bestk, bestv[MAXC], curv[MAXC];
static long nodes, nodelimit;

static void expand(int depth, const int *P, int np) {
    if (++nodes > nodelimit) return;
    int ord[MAXC], col[MAXC], rem[MAXC], cls[MAXC], nxt[MAXC];
    int nord = 0, color = 0, nrem = np;
    memcpy(rem, P, sizeof(int) * np);
    while (nrem > 0) {   /* greedy colouring; a colour class is a set of pairwise non-opposite points */
        color++;
        int ncls = 0, nn = 0;
        for (int i = 0; i < nrem; i++) {
            int v = rem[i], ok = 1;
            for (int j = 0; j < ncls; j++) if (A[cls[j]][v]) { ok = 0; break; }
            if (ok) cls[ncls++] = v; else nxt[nn++] = v;
        }
        for (int j = 0; j < ncls; j++) { ord[nord] = cls[j]; col[nord] = color; nord++; }
        memcpy(rem, nxt, sizeof(int) * nn); nrem = nn;
    }
    for (int i = nord - 1; i >= 0; i--) {
        if (depth + col[i] <= bestk) return;
        int v = ord[i];
        curv[depth] = v;
        int newP[MAXC], nn = 0;
        for (int j = 0; j < i; j++) if (A[v][ord[j]]) newP[nn++] = ord[j];
        if (nn == 0) {
            if (depth + 1 > bestk) { bestk = depth + 1; memcpy(bestv, curv, sizeof(int) * (depth + 1)); }
        } else expand(depth + 1, newP, nn);
        if (nodes > nodelimit) return;
    }
}

static void write_set(const char *fn, const int32_t *S, int k, const char *tag) {
    FILE *f = fopen(fn, "w"); if (!f) return;
    fprintf(f, "# %s: %d points, pairwise opposite (lns r3 c6, H(11) point indices)\n", tag, k);
    for (int i = 0; i < k; i++) fprintf(f, "%d\n", S[i]);
    fclose(f);
}
static double cpu(void) { return (double)clock() / CLOCKS_PER_SEC; }

static int verify_state(void) {   /* recompute everything from scratch */
    for (int i = 0; i < m; i++) for (int j = i + 1; j < m; j++) if (Bxy(R[i], R[j]) == 0) return 1;
    for (int x = 0; x < N; x++) {
        int c = 0; for (int i = 0; i < m; i++) if (R[i] != x && Bxy(x, R[i]) == 0) c++;
        if (c != cnt[x]) return 2;
    }
    return 0;
}

/* ---- geometry of the regions ---- */
/* the 1464 points at incidence distance <= 4 from line L (L, and the points collinear with a point of L) */
static int near4_points(int L, int32_t *out) {
    int n = 0;
    for (int b = 0; b < KK; b++) {
        int x = lp[(size_t)L * KK + b];
        out[n++] = x;
        for (int a = 0; a < KK; a++) {
            int L2 = pl[(size_t)x * KK + a];
            if (L2 == L) continue;
            for (int c = 0; c < KK; c++) { int p = lp[(size_t)L2 * KK + c]; if (p != x) out[n++] = p; }
        }
    }
    return n;
}

/* R points of Near4(L) that are not in the block (inD), written to out */
static int near4_R_new(int L, int32_t *out) {
    int n = near4_points(L, tnear);
    nstamp++;
    for (int i = 0; i < n; i++) nst[tnear[i]] = nstamp;
    int c = 0;
    for (int i = 0; i < m; i++) { int r = R[i]; if (nst[r] == nstamp && !inD[r]) out[c++] = r; }
    return c;
}

/* G2 membership: a . r = 0 mod 11 for the coefficient vector a (= w(v) for the hyperplane v^perp) */
static inline int on_hyp(const int *a, int r) {
    const uint8_t *v = co + 7L * r; int s = 0;
    for (int k = 0; k < 7; k++) s += a[k] * v[k];
    return s % QQ == 0;
}

/* G1: union of N_R(z) over random points z of Q(6,11) outside R, until BMIN points of R */
static int blk_point(int32_t *Dl, int bmin, int bmax) {
    int nD = 0;
    for (int t = 0; t < 400 && nD < bmin; t++) {
        int z = rndint(N); if (inR[z]) continue;
        int add = 0;
        for (int i = 0; i < m; i++) { int r = R[i]; if (!inD[r] && Bxy(z, r) == 0) add++; }
        if (nD + add > bmax) continue;
        for (int i = 0; i < m; i++) { int r = R[i]; if (!inD[r] && Bxy(z, r) == 0) { Dl[nD++] = r; inD[r] = 1; } }
    }
    for (int i = 0; i < nD; i++) inD[Dl[i]] = 0;
    return nD;
}

/* G2: union of R n {a.y = 0} over random nonzero coefficient vectors a (a = w(v), v uniform nonzero in F_11^7) */
static int blk_hyper(int32_t *Dl, int bmin, int bmax) {
    int nD = 0;
    for (int t = 0; t < 400 && nD < bmin; t++) {
        int a[7], nz;
        do { nz = 0; for (int k = 0; k < 7; k++) { a[k] = rndint(QQ); nz |= a[k]; } } while (!nz);
        int add = 0;
        for (int i = 0; i < m; i++) { int r = R[i]; if (!inD[r] && on_hyp(a, r)) add++; }
        if (nD + add > bmax) continue;
        for (int i = 0; i < m; i++) { int r = R[i]; if (!inD[r] && on_hyp(a, r)) { Dl[nD++] = r; inD[r] = 1; } }
    }
    for (int i = 0; i < nD; i++) inD[Dl[i]] = 0;
    return nD;
}

/* G3: union of R n Near4(L) over a random walk of lines (each new line meets a line of the tube) */
static int blk_tube(int32_t *Dl, int bmin, int bmax) {
    static int Sl[MAXLINES];
    int nD = 0, ns = 0;
    int L0 = rndint(NL);
    int c0 = near4_R_new(L0, tR);
    for (int i = 0; i < c0; i++) { Dl[nD++] = tR[i]; inD[tR[i]] = 1; }
    Sl[ns++] = L0; inS[L0] = 1;
    for (int t = 0; t < 2000 && nD < bmin && ns < MAXLINES; t++) {
        int Ls = Sl[rndint(ns)];
        int x = lp[(size_t)Ls * KK + rndint(KK)];
        int M = pl[(size_t)x * KK + rndint(KK)];
        if (inS[M]) continue;
        int c = near4_R_new(M, tR);
        if (nD + c > bmax) continue;
        inS[M] = 1; Sl[ns++] = M;
        for (int i = 0; i < c; i++) { Dl[nD++] = tR[i]; inD[tR[i]] = 1; }
    }
    for (int i = 0; i < ns; i++) inS[Sl[i]] = 0;
    for (int i = 0; i < nD; i++) inD[Dl[i]] = 0;
    return nD;
}

static int geo_block(int kind, int32_t *Dl, int bmin, int bmax) {
    if (kind == 2) return blk_point(Dl, bmin, bmax);
    if (kind == 3) return blk_hyper(Dl, bmin, bmax);
    return blk_tube(Dl, bmin, bmax);
}

/* round-2 fibre move: all R points with the same affine fibre key as a random R point (x0 = 1 points only) */
static int fibre_block(int32_t *Dl) {
    int nD = 0, r = -1;
    for (int t = 0; t < 100 && r < 0; t++) { int x = R[rndint(m)]; if (co[7L * x] == 1) r = x; }
    if (r < 0) return 0;
    /* key = (b, e, f, c - 9a) with a = x1, b = x2, c = x3, e = x5, f = x6 */
    int kb = co[7L*r+2], ke = co[7L*r+5], kf = co[7L*r+6], kc = ((co[7L*r+3] - 9 * co[7L*r+1]) % QQ + 2 * QQ) % QQ;
    for (int i = 0; i < m; i++) { int x = R[i]; if (co[7L*x] != 1) continue;
        int xc = ((co[7L*x+3] - 9 * co[7L*x+1]) % QQ + 2 * QQ) % QQ;
        if (co[7L*x+2] == kb && co[7L*x+5] == ke && co[7L*x+6] == kf && xc == kc) Dl[nD++] = x; }
    return nD;
}

/* round-2 conflict-driven block: D = N_R(y) for a seed y (non-R, 1 <= cnt <= cmax), grown greedily by low-count
   neighbours. Returns |D| >= 1, or -1 if no seed was found. */
static int conf_block(int32_t *Dl, int cmax, int jmax, int gmax) {
    int nD = 0, y = -1;
    for (long tr = 0; tr < 5000000L; tr++) { int x = rndint(N); if (!inR[x] && cnt[x] >= 1 && cnt[x] <= cmax) { y = x; break; } }
    if (y < 0) return -1;
    for (int i = 0; i < m; i++) if (Bxy(y, R[i]) == 0) { Dl[nD++] = R[i]; inD[R[i]] = 1; }
    int target = nD; if (jmax > nD) target = nD + rndint(jmax - nD + 1);
    int steps = rndint(gmax + 1);
    for (int s = 0; s < steps && nD < target; s++) {
        int r = Dl[rndint(nD)];
        int n = perp(r, tbuf2);
        int bz = -1, bcost = 1 << 30, nb = 0;
        for (int k = 0; k < 24; k++) {
            int z = tbuf2[rndint(n)];
            if (inR[z] || z == y || cnt[z] == 0 || cnt[z] > cmax + 2) continue;
            int cost = 0; for (int i = 0; i < m; i++) if (!inD[R[i]] && Bxy(z, R[i]) == 0) cost++;
            if (cost == 0) continue;
            if (cost < bcost) { bcost = cost; bz = z; nb = 1; }
            else if (cost == bcost && rndint(++nb) == 0) bz = z;
        }
        if (bz < 0 || nD + bcost > target) continue;
        for (int i = 0; i < m; i++) if (!inD[R[i]] && Bxy(bz, R[i]) == 0) { Dl[nD++] = R[i]; inD[R[i]] = 1; }
    }
    for (int i = 0; i < nD; i++) inD[Dl[i]] = 0;
    return nD;
}

/* removes D from R, collects the candidates into Cv[0..nC), builds the opposition graph and runs the exact step with
   lower bound nD (result in bestk / bestv). Returns 0 if the candidate set exceeds MAXC (R is then R minus D: the
   caller restores D). */
static int remove_and_search(const int32_t *Dl, int nD) {
    for (int i = 0; i < nD; i++) delR(Dl[i]);
    nC = 0; int over = 0;
    for (int i = 0; i < nD; i++) { int x = Dl[i]; mark[x] = 1; Cv[nC++] = x; }
    for (int i = 0; i < nD && !over; i++) {
        int n = perp(Dl[i], tbuf2);
        for (int j = 0; j < n && !over; j++) { int x = tbuf2[j];
            if (!inR[x] && cnt[x] == 0 && !mark[x]) { if (nC < MAXC) { mark[x] = 1; Cv[nC++] = x; } else over = 1; } }
    }
    for (int i = 0; i < nC; i++) mark[Cv[i]] = 0;
    if (over) return 0;
    for (int i = 0; i < nC; i++) { A[i][i] = 0; for (int j = i + 1; j < nC; j++) { uint8_t o = (Bxy(Cv[i], Cv[j]) != 0); A[i][j] = A[j][i] = o; } }
    for (int i = 0; i < nC; i++) perm[i] = i;
    for (int i = nC - 1; i > 0; i--) { int j = rndint(i + 1), t = perm[i]; perm[i] = perm[j]; perm[j] = t; }
    bestk = nD; nodes = 0;
    expand(0, perm, nC);
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: lns HEXFILE INIT_IDX OUT_IDX CPU_SECONDS SEED [MODE CMAX JMAX GMAX PFIBER NODELIMIT PGEO BMIN BMAX PPLAT]\n"); return 1; }
    FILE *f = fopen(argv[1], "rb"); if (!f) return 1;
    int32_t hdr[3]; if (fread(hdr, 4, 3, f) != 3) return 1;
    int q = hdr[0]; N = hdr[1]; NL = hdr[2];
    if (q != QQ || KK != q + 1) { fprintf(stderr, "unexpected q %d\n", q); return 1; }
    lp = malloc(4L * NL * KK); if (fread(lp, 4, (size_t)NL * KK, f) != (size_t)NL * KK) return 1;
    co = malloc(7L * N); if (fread(co, 1, 7L * N, f) != 7L * N) return 1; fclose(f);
    pl = malloc(4L * N * KK); int *lc = calloc(N, sizeof(int));
    for (int l = 0; l < NL; l++) for (int k = 0; k < KK; k++) { int p = lp[(size_t)l * KK + k]; pl[(size_t)p * KK + lc[p]++] = l; }
    for (int p = 0; p < N; p++) if (lc[p] != KK) { fprintf(stderr, "point %d on %d lines\n", p, lc[p]); return 1; }
    free(lc);
    wd = malloc(7L * N);
    for (int x = 0; x < N; x++) {
        const uint8_t *s = co + 7L * x; int8_t *w = wd + 7L * x;
        w[0] = s[4]; w[1] = s[5]; w[2] = s[6]; w[3] = (QQ - (2 * s[3]) % QQ) % QQ; w[4] = s[0]; w[5] = s[1]; w[6] = s[2];
    }
    inR = calloc(N, 1); mark = calloc(N, 1); inD = calloc(N, 1); inS = calloc(NL, 1);
    cnt = calloc(N, sizeof(int32_t)); nst = calloc(N, sizeof(uint32_t));
    R = malloc(4L * N); posR = malloc(4L * N);
    double secs = atof(argv[4]);
    rs ^= (uint64_t)atoll(argv[5]) * 0x2545F4914F6CDD1DULL; for (int i = 0; i < 10; i++) rnd64();
    int mode = argc > 6 ? atoi(argv[6]) : 0;
    int cmax = argc > 7 ? atoi(argv[7]) : 3, jmax = argc > 8 ? atoi(argv[8]) : 40, gmax = argc > 9 ? atoi(argv[9]) : 6;
    double pfiber = argc > 10 ? atof(argv[10]) : 0.2;
    nodelimit = argc > 11 ? atol(argv[11]) : 20000;
    double pgeo = argc > 12 ? atof(argv[12]) : 0.7;
    int bmin = argc > 13 ? atoi(argv[13]) : 50, bmax = argc > 14 ? atoi(argv[14]) : 120;
    double pplat = argc > 15 ? atof(argv[15]) : 0.5;
    if (bmin < 1 || bmax < bmin || bmax > MAXC / 2) { fprintf(stderr, "bad BMIN/BMAX\n"); return 1; }

    /* self-test 1: perp enumeration equals {y != x : B(x,y) = 0} */
    for (int t = 0; t < 3; t++) {
        int x = (t == 0) ? 0 : rndint(N); int n = perp(x, tbuf); int ref = 0, bad = 0;
        for (int y = 0; y < N; y++) if (y != x && Bxy(x, y) == 0) ref++;
        if (n != 16104 || ref != n) bad = 1;
        for (int i = 0; i < n && !bad; i++) if (Bxy(x, tbuf[i]) != 0 || tbuf[i] == x) bad = 1;
        for (int i = 0; i < n; i++) mark[tbuf[i]] = 1;
        int distinct = 0; for (int i = 0; i < n; i++) distinct += mark[tbuf[i]];
        for (int i = 0; i < n; i++) mark[tbuf[i]] = 0;
        if (distinct != n) bad = 1;
        fprintf(stderr, "selftest point %d: perp size %d (scan %d) %s\n", x, n, ref, bad ? "FAILS" : "ok");
        if (bad) return 1;
    }
    /* self-test 2: Near4(L) has 1464 distinct points; G2 test a = w(z) for a point z equals B(z,.) = 0 (so the
       hyperplane of a singular vector is z^perp) */
    for (int t = 0; t < 3; t++) {
        int L = rndint(NL); int n = near4_points(L, tnear), bad = (n != NEAR4);
        nstamp++; for (int i = 0; i < n; i++) { if (nst[tnear[i]] == nstamp) bad = 1; nst[tnear[i]] = nstamp; }
        int z = rndint(N); int a[7];
        for (int k = 0; k < 7; k++) a[k] = wd[7L * z + k];
        for (int u = 0; u < 2000; u++) { int y = rndint(N); if (on_hyp(a, y) != (Bxy(z, y) == 0)) bad = 1; }
        fprintf(stderr, "selftest line %d: Near4 size %d, hyperplane check %s\n", L, n, bad ? "FAILS" : "ok");
        if (bad) return 1;
    }

    /* initial set (pairwise opposite, checked through cnt) */
    FILE *g = fopen(argv[2], "r"); if (!g) return 1; char buf[256];
    while (fgets(buf, sizeof buf, g)) { int v; if (buf[0] == '#' || sscanf(buf, "%d", &v) != 1) continue;
        if (v < 0 || v >= N || inR[v]) { fprintf(stderr, "bad or repeated point %d\n", v); return 1; }
        if (cnt[v] != 0) { fprintf(stderr, "initial set not pairwise opposite (point %d)\n", v); return 1; }
        addR(v); }
    fclose(g);
    fprintf(stderr, "initial |R| = %d\n", m);
    int nfree = 0;   /* greedy fill: points opposite to all of R (none expected for a maximal set) */
    for (int x = 0; x < N; x++) if (!inR[x] && cnt[x] == 0) { addR(x); nfree++; }
    if (nfree) fprintf(stderr, "added %d free points, |R| = %d\n", nfree, m);

    int32_t *Dl = malloc(4L * PMAX), S[MAXC];

    if (mode == 1) {
        long hist[32] = {0};
        for (int x = 0; x < N; x++) if (!inR[x]) { int k = cnt[x] < 31 ? cnt[x] : 31; hist[k]++; }
        for (int k = 0; k < 32; k++) if (hist[k]) fprintf(stderr, "c=%d: %ld points\n", k, hist[k]);
        return 0;
    }
    if (mode == 2) {   /* probe the geometric block types; R is restored after every sample */
        for (int kind = 2; kind <= 4; kind++) {
            int nsamp = 0, nover = 0, nimpr = 0, nlim = 0, dmin = 1 << 30, dmax = 0; double sD = 0, sC = 0, sN = 0;
            for (int t = 0; t < 150; t++) {
                int nD = geo_block(kind, Dl, bmin, bmax);
                if (nD == 0) continue;
                nsamp++; sD += nD; if (nD < dmin) dmin = nD; if (nD > dmax) dmax = nD;
                int ok = remove_and_search(Dl, nD);
                if (!ok) nover++;
                else { sC += nC; sN += nodes; if (nodes > nodelimit) nlim++; if (bestk > nD) nimpr++; }
                for (int i = 0; i < nD; i++) addR(Dl[i]);
            }
            int ns = nsamp ? nsamp : 1;
            fprintf(stderr, "probe G%d: samples %d, |D| mean %.1f (min %d, max %d), |C| mean %.1f, over-cap %d, "
                    "node-limit hits %d, mean nodes %.0f, larger set found %d\n", kind - 1, nsamp, sD / ns,
                    dmin, dmax, sC / ns, nover, nlim, sN / ns, nimpr);
        }
        fprintf(stderr, "after probes |R| = %d\n", m);
        return verify_state() ? 1 : 0;
    }

    /* LNS */
    int best = m; int32_t *bestR = malloc(4L * N); memcpy(bestR, R, 4L * m);
    long iters = 0, improv = 0, plat = 0, skipped = 0, nempty = 0, sumC = 0, nonempty = 0;
    long kmoves[NKIND] = {0}, kskip[NKIND] = {0}, kimpr[NKIND] = {0}, kplat[NKIND] = {0};
    double ksumD[NKIND] = {0}, ksumC[NKIND] = {0};
    double lastrep = 0;
    while (cpu() < secs) {
        iters++;
        int kind = 0, nD = 0;
        if (rndint(1000) < (int)(pgeo * 1000)) { kind = 2 + rndint(3); nD = geo_block(kind, Dl, bmin, bmax); }
        else if (rndint(1000) < (int)(pfiber * 1000) && m > 1) { kind = 1; nD = fibre_block(Dl); }
        else {
            kind = 0; nD = conf_block(Dl, cmax, jmax, gmax);
            if (nD < 0) { cmax++; if (cmax > 40) break; continue; }
        }
        if (nD == 0) { nempty++; continue; }
        if (nD > MAXC / 2) continue;
        kmoves[kind]++; ksumD[kind] += nD;
        /* 4.-5. remove D, candidates; 6. exact step with lower bound nD */
        if (!remove_and_search(Dl, nD)) {
            skipped++; kskip[kind]++;
            for (int i = 0; i < nD; i++) addR(Dl[i]);
            continue;
        }
        sumC += nC; nonempty++; ksumC[kind] += nC;
        int accept = 0, k = 0;
        if (bestk > nD) { accept = 1; k = bestk; for (int i = 0; i < k; i++) S[i] = Cv[bestv[i]]; }
        else if (rndint(1000) < (int)(pplat * 1000)) {
            /* random maximal opposite subset of C (in random order): larger -> improvement, equal -> plateau */
            int chosen[MAXC], nc = 0;
            for (int t = 0; t < nC; t++) { int v = perm[t], good = 1;
                for (int j = 0; j < nc; j++) if (!A[v][chosen[j]]) { good = 0; break; }
                if (good) chosen[nc++] = v; }
            if (nc >= nD) { accept = 1; k = nc; for (int i = 0; i < k; i++) S[i] = Cv[chosen[i]];
                if (nc == nD) { plat++; kplat[kind]++; } }
        }
        if (accept) {
            if (k > nD) { improv++; kimpr[kind]++; }
            for (int i = 0; i < k; i++) addR(S[i]);
        } else {
            for (int i = 0; i < nD; i++) addR(Dl[i]);
        }
        if (m > best) {
            best = m; memcpy(bestR, R, 4L * m);
            write_set(argv[3], bestR, best, "best so far");
            fprintf(stderr, "[%.1fs] it %ld: new best %d (kind %d, |D| %d)\n", cpu(), iters, best, kind, nD);
        }
        if (cpu() - lastrep > 30) {
            lastrep = cpu();
            fprintf(stderr, "[%.0fs] it %ld |R|=%d best=%d improv=%ld plateau=%ld | moves conf/fib/G1/G2/G3 = "
                    "%ld/%ld/%ld/%ld/%ld, mean |D| G1/G2/G3 %.0f/%.0f/%.0f, mean |C| G1/G2/G3 %.0f/%.0f/%.0f, skipped %ld\n",
                    cpu(), iters, m, best, improv, plat, kmoves[0], kmoves[1], kmoves[2], kmoves[3], kmoves[4],
                    kmoves[2] ? ksumD[2] / kmoves[2] : 0.0, kmoves[3] ? ksumD[3] / kmoves[3] : 0.0,
                    kmoves[4] ? ksumD[4] / kmoves[4] : 0.0, kmoves[2] ? ksumC[2] / kmoves[2] : 0.0,
                    kmoves[3] ? ksumC[3] / kmoves[3] : 0.0, kmoves[4] ? ksumC[4] / kmoves[4] : 0.0, skipped);
        }
    }
    fprintf(stderr, "done: %ld iterations, best %d, improv %ld, plateau %ld, skipped %ld, empty %ld, avg|C| %.1f\n",
            iters, best, improv, plat, skipped, nempty, nonempty ? (double)sumC / nonempty : 0.0);
    for (int kd = 0; kd < NKIND; kd++) if (kmoves[kd])
        fprintf(stderr, "  kind %d: moves %ld, improving %ld, plateau %ld, skipped %ld, mean |D| %.1f, mean |C| %.1f\n",
                kd, kmoves[kd], kimpr[kd], kplat[kd], kskip[kd], ksumD[kd] / kmoves[kd], ksumC[kd] / kmoves[kd]);
    int vs = verify_state();
    if (vs) fprintf(stderr, "WARNING: state verification failed (%d)\n", vs);
    write_set(argv[3], bestR, best, "best");
    printf("best %d\n", best);
    return 0;
}
