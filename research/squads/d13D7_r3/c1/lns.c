/* lns.c: squad round 3, card c1 (Haiku). The round-2 LNS of card c6 (research/squads/d13D7_r2/c6/lns.c) extended
   with two block types. Every block removes a set D of R points; its candidate set C is D plus every non-R point whose
   only R-blockers lie in D (cnt == 0 after the removal). The exact maximum pairwise-opposite subset S of C (branch and
   bound, greedy colouring bound, node limit, lower bound |D|) replaces D if |S| > |D|; an equal-size subset replaces D
   with probability pplat (plateau move); otherwise D is restored.

   (1) SWEEP: D = {x} for every x in R, in random order. C = {x} plus the private candidates of x (points blocked only
       by x). Improvements are applied at once; plateau moves (a swap x -> y, y a private candidate) with probability
       PSWEEP. Sweeps repeat while a sweep grows |R|.
   (2) HUB: D = {x1, x2}. x1 = the R point with the most private candidates, x2 = the second one (tried once per state,
       with probability 1/4); otherwise a random pair among the TOPK points with the most private candidates.
       C = D plus the points blocked only by D (private candidates of x1 and x2, and points blocked by both).
   (3) LNS: the c6 random blocks: seed y with 1 <= cnt <= CMAX, D = N_R(y) grown greedily by low-count neighbours
       (or a whole affine fibre, with probability PFIBER).

   Driver (MODE 2): sweeps until a sweep does not grow |R|; then FBUDGET fallback iterations (HUB with probability PHUB,
   else LNS); back to the sweeps as soon as a fallback block grows |R|.  MODE 0: the c6 driver (LNS only).
   MODE 1: statistics of the initial set (cnt histogram, private-candidate counts, one dry sweep) and exit.

   usage: lns HEXFILE INIT_IDX OUT_IDX CPU_SECONDS SEED [MODE CMAX JMAX GMAX PFIBER NODELIMIT PSWEEP PHUB FBUDGET PHUBPLAT TOPK]
   defaults: MODE 2, CMAX 3, JMAX 40, GMAX 6, PFIBER 0.2, NODELIMIT 20000, PSWEEP 0.3, PHUB 0.3, FBUDGET 300,
   PHUBPLAT 0.5, TOPK 20 (the LNS plateau probability is 0.5, as in c6).  OUT_IDX is rewritten whenever |R| grows.

   Non-opposite points of x (B(x,y)=0, y != x) are exactly the 16104 points at distance 2 or 4 from x in the
   incidence graph; they are enumerated by the paths x-L1-p1-L2-p2 (girth 12: each point occurs once).
   State: R (pairwise opposite), inR, cnt[x] = #{r in R, r != x, B(x,r) = 0}; points of R have cnt = 0.  */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>

#define QQ 11
#define KK 12          /* q+1: lines per point and points per line */
#define MAXC 1024      /* cap on the candidate set of one block */
#define PMAX 16200     /* |perp(x)| = 16104 */

static int N, NL;
static int32_t *lp, *pl;   /* NL x KK point indices of lines; N x KK line indices of points */
static uint8_t *co;        /* N x 7 coordinates */
static int8_t *wd;         /* N x 7: B(x,y) = sum_k wd[x][k]*co[y][k] mod 11 */
static uint8_t *inR, *mark, *inD;
static int32_t *cnt;       /* cnt[x] = #{r in R, r != x, B(x,r) = 0} */
static int32_t *R, *posR; static int m = 0;
static int32_t *privc; static int privvalid = 0;   /* privc[x] (x in R) = #{y : cnt[y] == 1, B(x,y) = 0} */
static long stateid = 0;                           /* increases whenever R changes for good */
static int32_t tbuf[PMAX], tbuf2[PMAX], tbuf3[PMAX], Dl[PMAX];
static int32_t *ordbuf, *snapbuf;
static int cmax = 3, jmax = 40, gmax = 6; static double pfiber = 0.2;
static const double pplat_lns = 0.5;
static int dry = 0, last_nC = 0, last_k = 0;
static long blk_n = 0, blk_sumC = 0, blk_maxC = 0, blk_nodes = 0, blk_trunc = 0;   /* block statistics */

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
static void changed(void) { privvalid = 0; stateid++; }

/* ---- exact maximum pairwise-opposite subset (max clique of the opposition graph) on local indices ---- */
static uint8_t A[MAXC][MAXC];          /* A[i][j] = 1 iff i, j opposite */
static int nC, Cv[MAXC];
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

/* One block move. D (nD points of R) is removed; C = D plus the points whose only R-blockers were in D; S = exact
   maximum pairwise-opposite subset of C (lower bound nD, node limit).  |S| > nD: S replaces D (returns |S| - nD).
   |S| == nD: a plateau move (S replaces D if it is a different set) with probability pplat (*plat = 1 if it changed
   the set).  Otherwise D is restored (returns 0).  dry: restore always; last_nC / last_k report the block. */
static int repair(const int32_t *D, int nD, double pplat, long nodelim, int *plat) {
    int i, j;
    *plat = 0;
    for (i = 0; i < nD; i++) delR(D[i]);
    nC = 0; int over = 0;
    for (i = 0; i < nD; i++) { mark[D[i]] = 1; Cv[nC++] = D[i]; }
    for (i = 0; i < nD && !over; i++) {
        int n = perp(D[i], tbuf3);
        for (j = 0; j < n && !over; j++) { int x = tbuf3[j];
            if (!inR[x] && cnt[x] == 0 && !mark[x]) { if (nC < MAXC) { mark[x] = 1; Cv[nC++] = x; } else over = 1; } }
    }
    for (i = 0; i < nC; i++) mark[Cv[i]] = 0;
    if (over) { for (i = 0; i < nD; i++) addR(D[i]); last_nC = -1; last_k = nD; return 0; }
    last_nC = nC;
    for (i = 0; i < nC; i++) { A[i][i] = 0; for (j = i + 1; j < nC; j++) { uint8_t o = (Bxy(Cv[i], Cv[j]) != 0); A[i][j] = A[j][i] = o; } }
    int perm[MAXC];
    for (i = 0; i < nC; i++) perm[i] = i;
    for (i = nC - 1; i > 0; i--) { j = rndint(i + 1); int t = perm[i]; perm[i] = perm[j]; perm[j] = t; }
    bestk = nD; nodes = 0; nodelimit = nodelim;
    expand(0, perm, nC);
    last_k = bestk;
    blk_n++; blk_sumC += nC; if (nC > blk_maxC) blk_maxC = nC; blk_nodes += nodes; if (nodes > nodelimit) blk_trunc++;
    if (dry) { for (i = 0; i < nD; i++) addR(D[i]); return 0; }
    int accept = 0, k = 0; int32_t S[MAXC];
    if (bestk > nD) { accept = 1; k = bestk; for (i = 0; i < k; i++) S[i] = Cv[bestv[i]]; }
    else if (rndint(1000) < (int)(pplat * 1000)) {
        /* random maximal opposite subset of C (in random order): larger -> improvement, equal -> plateau */
        int chosen[MAXC], nc = 0;
        for (int t = 0; t < nC; t++) { int v = perm[t], ok = 1;
            for (j = 0; j < nc; j++) if (!A[v][chosen[j]]) { ok = 0; break; }
            if (ok) chosen[nc++] = v; }
        if (nc >= nD) { accept = 1; k = nc; for (i = 0; i < k; i++) S[i] = Cv[chosen[i]]; }
    }
    if (!accept) { for (i = 0; i < nD; i++) addR(D[i]); return 0; }
    int chg = 0;
    for (i = 0; i < nD; i++) inD[D[i]] = 1;
    for (i = 0; i < k; i++) if (!inD[S[i]]) chg = 1;
    for (i = 0; i < nD; i++) inD[D[i]] = 0;
    for (i = 0; i < k; i++) addR(S[i]);
    if (k > nD) { changed(); return k - nD; }
    if (chg) { *plat = 1; changed(); }
    return 0;
}

static void write_set(const char *fn, const int32_t *S, int k, const char *tag) {
    FILE *f = fopen(fn, "w"); if (!f) return;
    fprintf(f, "# %s: %d points, pairwise opposite (squad r3 c1: lns with sweep and hub blocks, H(11) point indices)\n", tag, k);
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

/* private candidate counts of the R points: privc[x] = #{y not in R : cnt[y] == 1, B(x,y) = 0}. Only the few points
   with exactly one R-blocker matter, so each is attached to its blocker by a scan over R (no perp enumeration). */
static void compute_priv(void) {
    for (int i = 0; i < m; i++) privc[R[i]] = 0;
    for (int y = 0; y < N; y++) {
        if (inR[y] || cnt[y] != 1) continue;
        for (int i = 0; i < m; i++) { int x = R[i]; if (Bxy(x, y) == 0) { privc[x]++; break; } }
    }
    privvalid = 1;
}

/* ---- move 1: exhaustive (1,k) sweep ---- */
static long sw_tries = 0, sw_impr = 0, sw_plat = 0, sw_sweeps = 0;
static int sweep_round(double pplat, long nodelim) {
    int n = m, imp = 0;
    for (int i = 0; i < n; i++) snapbuf[i] = R[i];
    for (int i = n - 1; i > 0; i--) { int j = rndint(i + 1); int32_t t = snapbuf[i]; snapbuf[i] = snapbuf[j]; snapbuf[j] = t; }
    for (int t = 0; t < n; t++) {
        int32_t x = snapbuf[t];
        if (!inR[x]) continue;
        int plat = 0;
        sw_tries++;
        int g = repair(&x, 1, pplat, nodelim, &plat);
        if (g > 0) { imp++; sw_impr++; }
        sw_plat += plat;
    }
    sw_sweeps++;
    return imp;
}

/* ---- move 2: two-hub block ---- */
static long hub_tries = 0, hub_impr = 0, hub_plat = 0;
static int cmp_priv_desc(const void *a, const void *b) {
    int32_t x = *(const int32_t *)a, y = *(const int32_t *)b;
    return privc[y] - privc[x];
}
static int hub_move(int topk, double pplat, long nodelim) {
    if (m < 2) return 0;
    if (!privvalid) compute_priv();
    for (int i = 0; i < m; i++) ordbuf[i] = R[i];
    for (int i = m - 1; i > 0; i--) { int j = rndint(i + 1); int32_t t = ordbuf[i]; ordbuf[i] = ordbuf[j]; ordbuf[j] = t; }
    qsort(ordbuf, m, sizeof(int32_t), cmp_priv_desc);      /* most private candidates first (random ties) */
    int K = topk < m ? topk : m; if (K < 2) K = 2;
    static long top2_state = -1;
    int32_t D[2];
    if (rndint(4) == 0 && top2_state != stateid) { top2_state = stateid; D[0] = ordbuf[0]; D[1] = ordbuf[1]; }
    else { int i = rndint(K), j = rndint(K - 1); if (j >= i) j++; D[0] = ordbuf[i]; D[1] = ordbuf[j]; }
    int plat = 0;
    int g = repair(D, 2, pplat, nodelim, &plat);
    hub_tries++; if (g > 0) hub_impr++; hub_plat += plat;
    return g > 0;
}

/* ---- move 3: the c6 random LNS block (returns 1 if |R| grew) ---- */
static long lns_tries = 0, lns_impr = 0, lns_plat = 0;
static int lns_iter(long nodelim) {
    int m0 = m, nD = 0;
    if (rndint(1000) < (int)(pfiber * 1000) && m > 1) {
        /* fibre move: all R points with the same affine fibre key as a random R point (x0 = 1 points only) */
        int r = -1;
        for (int t = 0; t < 100 && r < 0; t++) { int x = R[rndint(m)]; if (co[7L * x] == 1) r = x; }
        if (r < 0) return 0;
        /* key = (b, e, f, c - 9a) with a = x1, b = x2, c = x3, e = x5, f = x6 */
        int kb = co[7L*r+2], ke = co[7L*r+5], kf = co[7L*r+6], kc = ((co[7L*r+3] - 9 * co[7L*r+1]) % QQ + 2 * QQ) % QQ;
        for (int i = 0; i < m; i++) { int x = R[i]; if (co[7L*x] != 1) continue;
            int xc = ((co[7L*x+3] - 9 * co[7L*x+1]) % QQ + 2 * QQ) % QQ;
            if (co[7L*x+2] == kb && co[7L*x+5] == ke && co[7L*x+6] == kf && xc == kc) Dl[nD++] = x; }
    } else {
        /* 1. seed y: non-R point with 1 <= cnt <= cmax */
        int y = -1;
        for (long tr = 0; tr < 5000000L; tr++) { int x = rndint(N); if (!inR[x] && cnt[x] >= 1 && cnt[x] <= cmax) { y = x; break; } }
        if (y < 0) { if (cmax < 40) cmax++; return 0; }
        /* 2. D = N_R(y) */
        for (int i = 0; i < m; i++) if (Bxy(y, R[i]) == 0) { Dl[nD++] = R[i]; inD[R[i]] = 1; }
        /* 3. greedy growth by low-cnt neighbours z of a random D point, adding N_R(z) \ D */
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
    }
    /* 4-6. remove D, exact repair on the freed candidates */
    int plat = 0;
    int g = repair(Dl, nD, pplat_lns, nodelim, &plat);
    lns_tries++; if (g > 0) lns_impr++; lns_plat += plat;
    return m > m0;
}

static void report(const char *tag, const char *out, int *best, double t) {
    if (m > *best) {
        *best = m;
        write_set(out, R, m, "best so far");
        fprintf(stderr, "[%.1fs] %s: new best %d\n", t, tag, m);
    }
}

int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: lns HEXFILE INIT_IDX OUT_IDX CPU_SECONDS SEED [MODE CMAX JMAX GMAX PFIBER NODELIMIT PSWEEP PHUB FBUDGET PHUBPLAT TOPK]\n"); return 1; }
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
    inR = calloc(N, 1); mark = calloc(N, 1); inD = calloc(N, 1); cnt = calloc(N, sizeof(int32_t));
    R = malloc(4L * N); posR = malloc(4L * N); privc = calloc(N, sizeof(int32_t));
    ordbuf = malloc(4L * N); snapbuf = malloc(4L * N);
    double secs = atof(argv[4]);
    rs ^= (uint64_t)atoll(argv[5]) * 0x2545F4914F6CDD1DULL; for (int i = 0; i < 10; i++) rnd64();
    int mode = argc > 6 ? atoi(argv[6]) : 2;
    cmax = argc > 7 ? atoi(argv[7]) : 3; jmax = argc > 8 ? atoi(argv[8]) : 40; gmax = argc > 9 ? atoi(argv[9]) : 6;
    pfiber = argc > 10 ? atof(argv[10]) : 0.2;
    long nodelimit_g = argc > 11 ? atol(argv[11]) : 20000;
    double psweep = argc > 12 ? atof(argv[12]) : 0.3;
    double phub = argc > 13 ? atof(argv[13]) : 0.3;
    long fbudget = argc > 14 ? atol(argv[14]) : 300;
    double phubplat = argc > 15 ? atof(argv[15]) : 0.5;
    int topk = argc > 16 ? atoi(argv[16]) : 20;

    /* self-test: perp enumeration equals {y != x : B(x,y) = 0} */
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

    /* initial set (pairwise opposite, checked through cnt) */
    FILE *g = fopen(argv[2], "r"); if (!g) return 1; char buf[256];
    while (fgets(buf, sizeof buf, g)) { int v; if (buf[0] == '#' || sscanf(buf, "%d", &v) != 1) continue;
        if (v < 0 || v >= N || inR[v]) { fprintf(stderr, "bad or repeated point %d\n", v); return 1; }
        if (cnt[v] != 0) { fprintf(stderr, "initial set not pairwise opposite (point %d)\n", v); return 1; }
        addR(v); }
    fclose(g);
    fprintf(stderr, "initial |R| = %d\n", m);
    { int aug = 0; for (int x = 0; x < N; x++) if (!inR[x] && cnt[x] == 0) { addR(x); aug++; }
      if (aug) fprintf(stderr, "augmented %d free points\n", aug); }

    if (mode == 1) {
        long hist[32] = {0};
        for (int x = 0; x < N; x++) if (!inR[x]) { int k = cnt[x] < 31 ? cnt[x] : 31; hist[k]++; }
        for (int k = 0; k < 32; k++) if (hist[k]) fprintf(stderr, "c=%d: %ld points\n", k, hist[k]);
        compute_priv();
        long ph[64] = {0}; int pmax = 0, pmin = 1 << 30; long psum = 0;
        for (int i = 0; i < m; i++) { int c = privc[R[i]]; ph[c < 63 ? c : 63]++; psum += c; if (c > pmax) pmax = c; if (c < pmin) pmin = c; }
        fprintf(stderr, "private candidates per R point: min %d max %d mean %.2f\n", pmin, pmax, (double)psum / m);
        for (int k = 0; k < 64; k++) if (ph[k]) fprintf(stderr, "  privc=%d: %ld R points\n", k, ph[k]);
        /* dry sweep: exact (1,k) block value for every x in R */
        for (int i = 0; i < m; i++) snapbuf[i] = R[i];
        int nb = m, gains = 0, maxC = 0; long sumC = 0; double t0 = cpu();
        for (int i = 0; i < nb; i++) {
            int32_t x = snapbuf[i]; int plat = 0;
            dry = 1; repair(&x, 1, 0.0, nodelimit_g, &plat); dry = 0;
            if (last_k > 1) gains++;
            if (last_nC > maxC) maxC = last_nC;
            if (last_nC > 0) sumC += last_nC;
        }
        fprintf(stderr, "dry sweep: %d R points, %d with a (1,k) gain, max |C| %d, mean |C| %.2f, %.3fs\n",
                nb, gains, maxC, (double)sumC / nb, cpu() - t0);
        printf("best %d\n", m);
        return 0;
    }

    int best = m;
    write_set(argv[3], R, m, "initial");     /* fallback output in case the run is killed */
    double lastrep = 0;
    long nfb = 0, nswp = 0;
    if (mode == 0) {   /* c6 driver: LNS only */
        while (cpu() < secs) {
            lns_iter(nodelimit_g); nswp++;
            report("lns", argv[3], &best, cpu());
            if (cpu() - lastrep > 30) { lastrep = cpu();
                fprintf(stderr, "[%.0fs] it %ld |R|=%d lns_impr=%ld plateau=%ld\n", cpu(), nswp, m, lns_impr, lns_plat); }
        }
    } else {           /* MODE 2: sweeps, then hub/LNS fallback */
        while (cpu() < secs) {
            int si;
            do {
                si = sweep_round(psweep, nodelimit_g);
                report("sweep", argv[3], &best, cpu());
            } while (si > 0 && cpu() < secs);
            for (long t = 0; t < fbudget && cpu() < secs; t++) {
                int m0 = m;
                if (rndint(1000) < (int)(phub * 1000)) hub_move(topk, phubplat, nodelimit_g);
                else lns_iter(nodelimit_g);
                nfb++;
                report("fallback", argv[3], &best, cpu());
                if (m > m0) break;
            }
            if (cpu() - lastrep > 30) { lastrep = cpu();
                fprintf(stderr, "[%.0fs] |R|=%d best=%d sweeps=%ld sw_impr=%ld sw_plat=%ld hub=%ld/%ld/%ld lns=%ld/%ld/%ld fb=%ld\n",
                        cpu(), m, best, sw_sweeps, sw_impr, sw_plat, hub_tries, hub_impr, hub_plat, lns_tries, lns_impr, lns_plat, nfb); }
        }
    }
    fprintf(stderr, "done: |R| %d best %d | sweeps %ld tries %ld impr %ld plateau %ld | hub %ld impr %ld plateau %ld | lns %ld impr %ld plateau %ld | fallback %ld\n",
            m, best, sw_sweeps, sw_tries, sw_impr, sw_plat, hub_tries, hub_impr, hub_plat, lns_tries, lns_impr, lns_plat, nfb);
    fprintf(stderr, "blocks %ld: mean |C| %.2f, max |C| %ld, mean nodes %.1f, node-limit hits %ld\n",
            blk_n, blk_n ? (double)blk_sumC / blk_n : 0.0, blk_maxC, blk_n ? (double)blk_nodes / blk_n : 0.0, blk_trunc);
    int vs = verify_state();
    if (vs) fprintf(stderr, "WARNING: state verification failed (%d)\n", vs);
    write_set(argv[3], R, m, vs ? "UNVERIFIED" : "best");
    printf("best %d\n", m);
    return vs ? 2 : 0;
}
