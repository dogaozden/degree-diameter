/* lns.c: squad round 2, card c6: large neighbourhood search (LNS) on the full problem: a large set R of
   pairwise opposite points of the split Cayley hexagon H(11) (points of Q(6,11), B(x,y) != 0 mod 11).

   usage: lns HEXFILE INIT_IDX OUT_IDX CPU_SECONDS SEED [MODE CMAX JMAX GMAX PFIBER NODELIMIT]
     MODE 0 (default): LNS.  MODE 1: histogram of c[x] over non-R points and self-test only.

   Non-opposite points of x (B(x,y)=0, y != x) are exactly the 16104 points at distance 2 or 4 from x in the
   incidence graph; they are enumerated by the paths x-L1-p1-L2-p2 (girth 12: each point occurs once).
   State: R (pairwise opposite), inR, cnt[x] = #{r in R, r != x, B(x,r) = 0}; points of R have cnt = 0.
   Move: seed y (non-R, 1 <= cnt <= CMAX) -> D = N_R(y), grown greedily by low-cnt neighbours (or a whole
   fibre of the affine fibration, with probability PFIBER); remove D; candidates C = {x not in R: cnt = 0}
   (D plus points of perp(D) blocked only by D).  Exact maximum pairwise-opposite subset of C (branch and bound,
   greedy colouring bound, node limit) with lower bound |D|: larger -> accept; equal -> plateau move accepted with
   probability PPLAT (random maximal subset); otherwise D is restored. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>

#define QQ 11
#define KK 12          /* q+1: lines per point and points per line */
#define MAXC 1024      /* cap on the candidate set for the exact step */
#define PMAX 16200     /* |perp(x)| = 16104 */

static int N, NL;
static int32_t *lp, *pl;   /* NL x KK point indices of lines; N x KK line indices of points */
static uint8_t *co;        /* N x 7 coordinates */
static int8_t *wd;         /* N x 7: B(x,y) = sum_k wd[x][k]*co[y][k] mod 11 */
static uint8_t *inR, *mark, *inD;
static int32_t *cnt;       /* cnt[x] = #{r in R, r != x, B(x,r) = 0} */
static int32_t *R, *posR; static int m = 0;
static int32_t tbuf[PMAX], tbuf2[PMAX];

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

static void write_set(const char *fn, const int32_t *S, int k, const char *tag) {
    FILE *f = fopen(fn, "w"); if (!f) return;
    fprintf(f, "# %s: %d points, pairwise opposite (lns c6, H(11) point indices)\n", tag, k);
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

int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: lns HEXFILE INIT_IDX OUT_IDX CPU_SECONDS SEED [MODE CMAX JMAX GMAX PFIBER NODELIMIT]\n"); return 1; }
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
    R = malloc(4L * N); posR = malloc(4L * N);
    double secs = atof(argv[4]);
    rs ^= (uint64_t)atoll(argv[5]) * 0x2545F4914F6CDD1DULL; for (int i = 0; i < 10; i++) rnd64();
    int mode = argc > 6 ? atoi(argv[6]) : 0;
    int cmax = argc > 7 ? atoi(argv[7]) : 3, jmax = argc > 8 ? atoi(argv[8]) : 40, gmax = argc > 9 ? atoi(argv[9]) : 6;
    double pfiber = argc > 10 ? atof(argv[10]) : 0.2;
    nodelimit = argc > 11 ? atol(argv[11]) : 20000;
    double pplat = 0.5;

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

    if (mode == 1) {
        long hist[32] = {0};
        for (int x = 0; x < N; x++) if (!inR[x]) { int k = cnt[x] < 31 ? cnt[x] : 31; hist[k]++; }
        for (int k = 0; k < 32; k++) if (hist[k]) fprintf(stderr, "c=%d: %ld points\n", k, hist[k]);
        return 0;
    }

    int best = m; int32_t *bestR = malloc(4L * N); memcpy(bestR, R, 4L * m);
    int32_t *Dl = malloc(4L * PMAX), S[MAXC];
    long iters = 0, improv = 0, plat = 0, skipped = 0, nfib = 0, sumC = 0, nonempty = 0;
    double lastrep = 0;
    while (cpu() < secs) {
        iters++;
        int nD = 0;
        if (rndint(1000) < (int)(pfiber * 1000) && m > 1) {
            /* fibre move: all R points with the same affine fibre key as a random R point (x0 = 1 points only) */
            int r = -1;
            for (int t = 0; t < 100 && r < 0; t++) { int x = R[rndint(m)]; if (co[7L * x] == 1) r = x; }
            if (r < 0) continue;
            int key = (co[7L*r+2]*1 + 0) ; (void)key;
            /* key = (b, e, f, c - 9a) with a = x1, b = x2, c = x3, e = x5, f = x6 */
            int kb = co[7L*r+2], ke = co[7L*r+5], kf = co[7L*r+6], kc = ((co[7L*r+3] - 9 * co[7L*r+1]) % QQ + 2 * QQ) % QQ;
            for (int i = 0; i < m; i++) { int x = R[i]; if (co[7L*x] != 1) continue;
                int xc = ((co[7L*x+3] - 9 * co[7L*x+1]) % QQ + 2 * QQ) % QQ;
                if (co[7L*x+2] == kb && co[7L*x+5] == ke && co[7L*x+6] == kf && xc == kc) { Dl[nD++] = x; inD[x] = 1; } }
            for (int i = 0; i < nD; i++) inD[Dl[i]] = 0;
            nfib++;
        } else {
            /* 1. seed y: non-R point with 1 <= cnt <= cmax */
            int y = -1;
            for (long tr = 0; tr < 5000000L; tr++) { int x = rndint(N); if (!inR[x] && cnt[x] >= 1 && cnt[x] <= cmax) { y = x; break; } }
            if (y < 0) { cmax++; if (cmax > 40) break; continue; }
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
        /* 4. remove D */
        for (int i = 0; i < nD; i++) delR(Dl[i]);
        /* 5. candidates: D plus points of perp(D) with cnt = 0 and not in R (marks used for de-duplication) */
        nC = 0; int over = 0;
        for (int i = 0; i < nD; i++) { int x = Dl[i]; mark[x] = 1; Cv[nC++] = x; }
        for (int i = 0; i < nD && !over; i++) {
            int n = perp(Dl[i], tbuf2);
            for (int j = 0; j < n && !over; j++) { int x = tbuf2[j];
                if (!inR[x] && cnt[x] == 0 && !mark[x]) { if (nC < MAXC) { mark[x] = 1; Cv[nC++] = x; } else over = 1; } }
        }
        for (int i = 0; i < nC; i++) mark[Cv[i]] = 0;
        if (over) { skipped++; for (int i = 0; i < nD; i++) addR(Dl[i]); continue; }
        sumC += nC; nonempty++;
        /* 6. opposition graph on C; exact search for an opposite subset larger than nD */
        for (int i = 0; i < nC; i++) { A[i][i] = 0; for (int j = i + 1; j < nC; j++) { uint8_t o = (Bxy(Cv[i], Cv[j]) != 0); A[i][j] = A[j][i] = o; } }
        int perm[MAXC]; for (int i = 0; i < nC; i++) perm[i] = i;
        for (int i = nC - 1; i > 0; i--) { int j = rndint(i + 1), t = perm[i]; perm[i] = perm[j]; perm[j] = t; }
        bestk = nD; nodes = 0;
        expand(0, perm, nC);
        int accept = 0, k = 0;
        if (bestk > nD) {
            accept = 1; k = bestk; for (int i = 0; i < k; i++) S[i] = Cv[bestv[i]];
        } else if (rndint(1000) < (int)(pplat * 1000)) {
            /* random maximal opposite subset of C (in random order): larger -> improvement, equal -> plateau */
            int chosen[MAXC], nc = 0;
            for (int t = 0; t < nC; t++) { int v = perm[t], ok = 1;
                for (int j = 0; j < nc; j++) if (!A[v][chosen[j]]) { ok = 0; break; }
                if (ok) chosen[nc++] = v; }
            if (nc >= nD) { accept = 1; k = nc; for (int i = 0; i < k; i++) S[i] = Cv[chosen[i]]; if (nc == nD) plat++; }
        }
        if (accept) {
            if (k > nD) improv++;
            for (int i = 0; i < k; i++) addR(S[i]);
        } else {
            for (int i = 0; i < nD; i++) addR(Dl[i]);
        }
        if (m > best) {
            best = m; memcpy(bestR, R, 4L * m);
            write_set(argv[3], bestR, best, "best so far");
            fprintf(stderr, "[%.1fs] it %ld: new best %d\n", cpu(), iters, best);
        }
        if (cpu() - lastrep > 30) {
            lastrep = cpu();
            fprintf(stderr, "[%.0fs] it %ld |R|=%d best=%d improv=%ld plateau=%ld fibre=%ld skipped=%ld avg|C|=%.1f\n",
                    cpu(), iters, m, best, improv, plat, nfib, skipped, nonempty ? (double)sumC / nonempty : 0.0);
        }
    }
    fprintf(stderr, "done: %ld iterations, best %d, improv %ld, plateau %ld, fibre %ld, skipped %ld, avg|C| %.1f\n",
            iters, best, improv, plat, nfib, skipped, nonempty ? (double)sumC / nonempty : 0.0);
    int vs = verify_state();
    if (vs) fprintf(stderr, "WARNING: state verification failed (%d)\n", vs);
    write_set(argv[3], bestR, best, "best");
    printf("best %d\n", best);
    return 0;
}
