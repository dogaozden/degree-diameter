/* red.c: squad round 3, card c5: tabu search in a reduced structured family of pairwise opposite sets of H(11).

   Structure (found by c5, see cone_reduce.py): the points at infinity x0 = 0 with x5 = 2*x1 (mod 11) form a cone with
   vertex e4 over an elliptic quadric Q^-(3,11): 1343 points = e4 + 122 classes of 11 points (the points z + mu*e4 of one
   class are pairwise orthogonal).  Points of a class are pairwise orthogonal, so at most one per class; points of
   different classes are opposite.  Affine lines t + F*u, u = (1,0,0,9,0), t = (0,b,c,e,f) (1331 of 11^4 cosets are
   indexed as l = b*1331 + c*121 + e*11 + f), are pairwise opposite iff their cosets are compatible (table gok), and each
   line is opposite to every cone point except the one of its class it blocks (exactly one lift per class is blocked).
   Set for a clique K of lines: 11|K| points of the lines plus one unblocked lift for each class with a free lift.
   Objective f(K) = 11|K| + m(K), m(K) = number of classes with a free lift.  (397 = 11*25 + 122 for the 397 set.)

   Tabu search over K: moves ADD (free line), SWAP (line with exactly one conflict leaves, free line enters), DROP.
   usage: red HEXFILE INIT|- OUT_IDX CPU_SECONDS SEED [TT STAG PREST]
     INIT: offsets "a b c e f" per line (any a; normalised to a = 0) or '-' for an empty start.
     OUT_IDX: point indices of the best set (lines, cone lifts), verified later with oppcheck. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>

#define P 11
#define NLN 14641
#define NCL 122
static int N, NL;
static int32_t *lp, *pl;
static uint8_t *co;
static int32_t cone_idx[NCL][11];
static uint8_t blk[NLN][NCL];      /* blk[l][p] = lift j (0..10) of class p blocked by line l */
static uint8_t gok[NLN];           /* gok[d] = 1 iff cosets with difference d are compatible */
static uint8_t inK[NLN];
static int Kl[NLN], nK = 0, posK[NLN];
static int lc[NLN];
static int cnt[NCL][P], zeros[NCL];
static int mopen = 0;
static long tabuIn[NLN], tabuOut[NLN];
static int bestm_fix = -1;
static uint64_t rs = 0x9E3779B97F4A7C15ULL;
static inline uint64_t rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static double cpu(void) { return (double)clock() / CLOCKS_PER_SEC; }

static inline int dec_b(int l) { return l / 1331; }
static inline int dec_c(int l) { return (l / 121) % 11; }
static inline int dec_e(int l) { return (l / 11) % 11; }
static inline int dec_f(int l) { return l % 11; }
static inline int line_code(int b, int c, int e, int f) { return b * 1331 + c * 121 + e * 11 + f; }
static inline int conflict(int l, int s) {   /* l != s */
    int db = (dec_b(l) - dec_b(s) + P) % P, dc = (dec_c(l) - dec_c(s) + P) % P;
    int de = (dec_e(l) - dec_e(s) + P) % P, df = (dec_f(l) - dec_f(s) + P) % P;
    return !gok[line_code(db, dc, de, df)];
}

static inline int Bpt(const int *x, const uint8_t *z) {
    int s = x[0]*z[4] + x[4]*z[0] + x[1]*z[5] + x[5]*z[1] + x[2]*z[6] + x[6]*z[2] - 2*x[3]*z[3];
    s %= P; return s < 0 ? s + P : s;
}

static int cmp_codes_dummy;
static int32_t *codes_sorted_idx = NULL;   /* point index sorted by code */
static int32_t *codes = NULL;               /* code of point i */
static int point_of_coords(const int *x) {  /* x normalised (first nonzero 1), returns index or -1 */
    int code = 0, pw = 1;
    for (int i = 0; i < 7; i++) { code += x[i] * pw; pw *= P; }
    int lo = 0, hi = N - 1;
    while (lo <= hi) { int mid = (lo + hi) / 2; int c = codes[mid];
        if (c == code) return mid; if (c < code) lo = mid + 1; else hi = mid - 1; }
    return -1;
}

static void addK(int s) {
    inK[s] = 1; posK[s] = nK; Kl[nK++] = s;
    for (int t = 0; t < NLN; t++) if (t != s) lc[t] += conflict(t, s);
    for (int p = 0; p < NCL; p++) { int j = blk[s][p]; if (cnt[p][j]++ == 0) zeros[p]--; }
    mopen = 0; for (int p = 0; p < NCL; p++) mopen += zeros[p] > 0;
}
static void remK(int s) {
    int p0 = posK[s]; int y = Kl[--nK]; Kl[p0] = y; posK[y] = p0; inK[s] = 0;
    for (int t = 0; t < NLN; t++) if (t != s) lc[t] -= conflict(t, s);
    for (int p = 0; p < NCL; p++) { int j = blk[s][p]; if (--cnt[p][j] == 0) zeros[p]++; }
    mopen = 0; for (int p = 0; p < NCL; p++) mopen += zeros[p] > 0;
}
static int deltaAdd(int t) {
    int d = 0;
    for (int p = 0; p < NCL; p++) { int j = blk[t][p]; int z = zeros[p] - (cnt[p][j] == 0); d += (z > 0) - (zeros[p] > 0); }
    return d;
}
static int deltaRem(int s) {
    int d = 0;
    for (int p = 0; p < NCL; p++) { int j = blk[s][p]; int z = zeros[p] + (cnt[p][j] == 1); d += (z > 0) - (zeros[p] > 0); }
    return d;
}
static int deltaSwap(int s, int t) {
    int d = 0;
    for (int p = 0; p < NCL; p++) {
        int js = blk[s][p], jt = blk[t][p], z = zeros[p];
        if (js != jt) { z += (cnt[p][js] == 1); z -= (cnt[p][jt] == 0); }
        d += (z > 0) - (zeros[p] > 0);
    }
    return d;
}

/* point indices of the current solution: 11 points per line + one free lift per open class */
static int build_points(int32_t *out, int *nout) {
    int n = 0;
    for (int i = 0; i < nK; i++) {
        int l = Kl[i], b = dec_b(l), c = dec_c(l), e = dec_e(l), f = dec_f(l);
        for (int lam = 0; lam < P; lam++) {
            int a = lam, ee = (e + 9 * lam) % P;
            int x[7] = { 1, a, b, c, ((c * c - a * ee - b * f) % P + P * P) % P, ee, f };
            int idx = point_of_coords(x);
            if (idx < 0) return -1;
            out[n++] = idx;
        }
    }
    for (int p = 0; p < NCL; p++) {
        if (zeros[p] == 0) continue;
        int j = -1; for (int t = 0; t < P; t++) if (cnt[p][t] == 0) { j = t; break; }
        out[n++] = cone_idx[p][j];
    }
    *nout = n;
    return 0;
}
static void write_idx(const char *fn, const int32_t *S, int k, const char *tag) {
    FILE *f = fopen(fn, "w"); if (!f) return;
    fprintf(f, "# %s: %d points (lines + cone lifts, squad r3 c5 red)\n", tag, k);
    for (int i = 0; i < k; i++) fprintf(f, "%d\n", S[i]);
    fclose(f);
}

int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: red HEXFILE INIT|- OUT_IDX CPU_SECONDS SEED [TT STAG PREST]\n"); return 1; }
    FILE *f = fopen(argv[1], "rb"); if (!f) return 1;
    int32_t hdr[3]; if (fread(hdr, 4, 3, f) != 3) return 1;
    int q = hdr[0]; N = hdr[1]; NL = hdr[2];
    if (q != P) return 1;
    lp = malloc(4L * NL * 12); if (fread(lp, 4, (size_t)NL * 12, f) != (size_t)NL * 12) return 1;
    co = malloc(7L * N); if (fread(co, 1, 7L * N, f) != 7L * N) return 1; fclose(f);
    codes = malloc(4L * N);
    for (int i = 0; i < N; i++) { int c = 0, pw = 1; for (int k = 0; k < 7; k++) { c += co[7L * i + k] * pw; pw *= P; } codes[i] = c; }
    for (int i = 1; i < N; i++) if (codes[i] <= codes[i - 1]) { fprintf(stderr, "points not sorted by code\n"); return 1; }

    /* cone classes: points with x0 = 0, x5 = 2 x1 (mod 11), not e4; class key = (x1,x2,x3,x5,x6) normalised */
    int *classOfKey = malloc(sizeof(int) * 161051); for (int i = 0; i < 161051; i++) classOfKey[i] = -1;
    int ncl = 0; int ccount[NCL]; memset(ccount, 0, sizeof ccount);
    for (int i = 0; i < N; i++) {
        const uint8_t *z = co + 7L * i;
        if (z[0] != 0 || ((z[5] + 2 * (P - z[1])) % P) != 0) continue;   /* x5 = 2 x1 */
        int v[5] = { z[1], z[2], z[3], z[5], z[6] }, nz = -1;
        for (int k = 0; k < 5; k++) if (v[k]) { nz = v[k]; break; }
        if (nz < 0) continue;                                              /* e4 */
        int inv = 1; for (int k = 0; k < P - 2; k++) inv = inv * nz % P;   /* nz^(P-2) = nz^{-1} */
        int key = 0; for (int k = 0; k < 5; k++) key = key * P + (v[k] * inv) % P;
        if (classOfKey[key] < 0) { if (ncl >= NCL) { fprintf(stderr, "too many classes\n"); return 1; } classOfKey[key] = ncl++; }
        int c = classOfKey[key];
        if (ccount[c] >= 11) { fprintf(stderr, "class overfull\n"); return 1; }
        cone_idx[c][ccount[c]++] = i;
    }
    if (ncl != NCL) { fprintf(stderr, "found %d classes\n", ncl); return 1; }
    for (int c = 0; c < NCL; c++) if (ccount[c] != 11) { fprintf(stderr, "class %d has %d lifts\n", c, ccount[c]); return 1; }

    /* the lift blocked by each line: B(x_l, z) = 0 for x_l = (1,0,b,c,c^2-bf,e,f) (lambda = 0 point) */
    for (int l = 0; l < NLN; l++) {
        int b = dec_b(l), c = dec_c(l), e = dec_e(l), f = dec_f(l);
        int x[7] = { 1, 0, b, c, ((c * c - b * f) % P + P) % P, e, f };
        for (int p = 0; p < NCL; p++) {
            int hits = 0, jj = -1;
            for (int j = 0; j < P; j++) if (Bpt(x, co + 7L * cone_idx[p][j]) == 0) { hits++; jj = j; }
            if (hits != 1) { fprintf(stderr, "line %d class %d: %d blocked lifts\n", l, p, hits); return 1; }
            blk[l][p] = (uint8_t)jj;
        }
    }
    /* coset compatibility: d = (0,db,dc,de,df) compatible iff Q'(mu*u + d) != 0 for all mu, Q'(a,b,c,e,f)=c^2-ae-bf */
    for (int db = 0; db < P; db++) for (int dc = 0; dc < P; dc++) for (int de = 0; de < P; de++) for (int df = 0; df < P; df++) {
        int ok = 1;
        for (int mu = 0; mu < P && ok; mu++) {
            int a = mu, e = (de + 9 * mu) % P;
            int qv = ((dc * dc - a * e - db * df) % P + P * P) % P;
            if (qv == 0) ok = 0;
        }
        gok[line_code(db, dc, de, df)] = (uint8_t)ok;
    }
    /* d = 0 is never compatible (self); a line is not in conflict with itself */
    gok[0] = 0;

    double secs = atof(argv[4]);
    rs ^= (uint64_t)atoll(argv[5]) * 0x2545F4914F6CDD1DULL; for (int i = 0; i < 20; i++) rnd64();
    int TT = argc > 6 ? atoi(argv[6]) : 7;
    long STAG = argc > 7 ? atol(argv[7]) : 20000;
    double PREST = argc > 8 ? atof(argv[8]) : 0.5;
    int fixk = argc > 9 ? atoi(argv[9]) : 0;   /* >0: fixed-size mode, maximise m(K) over cliques with |K| = fixk */

    for (int l = 0; l < NLN; l++) { lc[l] = 0; }
    for (int p = 0; p < NCL; p++) { zeros[p] = P; for (int j = 0; j < P; j++) cnt[p][j] = 0; }
    mopen = NCL;   /* all classes open with K empty */

    if (strcmp(argv[2], "-") != 0) {
        FILE *g = fopen(argv[2], "r"); if (!g) return 1; char buf[256];
        while (fgets(buf, sizeof buf, g)) {
            if (buf[0] == '#') continue;
            int a, b, c, e, ff; if (sscanf(buf, "%d %d %d %d %d", &a, &b, &c, &e, &ff) != 5) continue;
            int lam = ((a % P) + P) % P;
            int bb = ((b % P) + P) % P, cc = ((c % P) + P) % P, ee = ((e - 9 * lam) % P + P * P) % P, fff = ((ff % P) + P) % P;
            int l = line_code(bb, cc, ee, fff);
            if (inK[l]) continue;
            if (lc[l] != 0) { fprintf(stderr, "init lines conflict (line %d)\n", l); return 1; }
            addK(l);
        }
        fclose(g);
    }
    fprintf(stderr, "initial |K| = %d, m = %d, f = %d\n", nK, mopen, 11 * nK + mopen);
    { int32_t p0[16000]; int n0 = 0; if (build_points(p0, &n0) == 0) write_idx(argv[3], p0, n0, "initial"); }

    int bestf = 11 * nK + mopen, bestK_n = nK; static int bestK[NLN]; memcpy(bestK, Kl, sizeof(int) * nK);
    int32_t pts[16000]; int np = 0;
    long iter = 0, lastImp = 0, nadd = 0, nswap = 0, ndrop = 0, npert = 0;
    double lastrep = 0;
    static int candS[NLN], candT[NLN]; static int candType[NLN]; static int cand_d[NLN];
    while (1) {
        if ((iter & 63) == 0) {
            double now = cpu();
            if (now > secs) break;
            if (now - lastrep > 30) { lastrep = now;
                fprintf(stderr, "[%.0fs] it %ld |K|=%d m=%d f=%d best=%d add=%ld swap=%ld drop=%ld pert=%ld\n",
                        now, iter, nK, mopen, 11 * nK + mopen, bestf, nadd, nswap, ndrop, npert); }
        }
        iter++;
        if (fixk > 0 && nK >= fixk) {         /* fixed-size mode (|K| = fixk): SWAP moves only */
            static int bestm_init = 0; if (!bestm_init) { bestm_init = 1; bestm_fix = -1; }
            while (nK > fixk) { int r = Kl[rndint(nK)]; remK(r); tabuIn[r] = iter + TT; }
            int bd = -1000000, nbb = 0, bt = -1, bsw = -1;
            for (int t = 0; t < NLN; t++) {
                if (inK[t] || lc[t] > 1) continue;
                for (int i = 0; i < nK; i++) {
                    int sv = Kl[i];
                    if (lc[t] == 1 && !conflict(t, sv)) continue;   /* t's only conflict must leave */
                    int d = deltaSwap(sv, t);
                    int adm = (tabuIn[t] <= iter && tabuOut[sv] <= iter) || (mopen + d > bestm_fix);
                    if (!adm) continue;
                    if (d > bd) { bd = d; nbb = 1; bt = t; bsw = sv; }
                    else if (d == bd && rndint(++nbb) == 0) { bt = t; bsw = sv; }
                }
            }
            if (bt < 0) {                     /* no admissible swap: random swap ignoring tabu, else restore the best */
                npert++;
                int cand[NLN], nc = 0;
                for (int t = 0; t < NLN; t++) if (!inK[t] && lc[t] <= 1) cand[nc++] = t;
                if (nc > 0) {
                    int t = cand[rndint(nc)], sv = -1;
                    if (lc[t] == 1) { for (int i = 0; i < nK; i++) if (conflict(t, Kl[i])) { sv = Kl[i]; break; } }
                    else sv = Kl[rndint(nK)];
                    remK(sv); addK(t); tabuIn[sv] = iter + TT; tabuOut[t] = iter + 2 * TT;
                } else {
                    while (nK > 0) remK(Kl[nK - 1]);
                    for (int i = 0; i < bestK_n; i++) addK(bestK[i]);
                }
            } else {
                remK(bsw); addK(bt); nswap++;
                tabuIn[bsw] = iter + TT + rndint(TT); tabuOut[bt] = iter + 2 * TT;
            }
            if (nK == fixk) {
                int mm = mopen;
                if (mm > bestm_fix) {
                    bestm_fix = mm; bestf = 11 * nK + mm; bestK_n = nK; memcpy(bestK, Kl, sizeof(int) * nK); lastImp = iter;
                    int32_t pp[16000]; int nn = 0;
                    if (build_points(pp, &nn) == 0) write_idx(argv[3], pp, nn, "best so far (fixed k)");
                    fprintf(stderr, "[%.1fs] it %ld: fixed-k %d: new best m=%d (f=%d)\n", cpu(), iter, fixk, mm, bestf);
                }
            }
            if ((iter & 65535) == 0) fprintf(stderr, "[%.0fs] fixed-k %d it %ld m=%d best=%d swaps=%ld kicks=%ld\n", cpu(), fixk, iter, mopen, bestf, nswap, npert);
            continue;
        }
        /* enumerate moves, keep the best admissible (ties random) */
        int bestd = -1000000, nb = 0, bestType = -1, bestS = -1, bestT = -1;
        int curf = 11 * nK + mopen;
        for (int t = 0; t < NLN; t++) {
            if (inK[t] || lc[t] > 1) continue;
            if (lc[t] == 0) {
                int d = 11 + deltaAdd(t);
                int adm = (tabuIn[t] <= iter) || (curf + d > bestf);
                if (!adm) continue;
                if (d > bestd) { bestd = d; nb = 1; bestType = 0; bestS = -1; bestT = t; }
                else if (d == bestd && rndint(++nb) == 0) { bestType = 0; bestS = -1; bestT = t; }
            } else {
                /* SWAP candidates: t's single conflict s */
                int s = -1;
                for (int i = 0; i < nK; i++) if (conflict(t, Kl[i])) { s = Kl[i]; break; }
                if (s < 0) continue;
                int d = deltaSwap(s, t);
                int adm = (tabuIn[t] <= iter && tabuOut[s] <= iter) || (curf + d > bestf);
                if (!adm) continue;
                if (d > bestd) { bestd = d; nb = 1; bestType = 1; bestS = s; bestT = t; }
                else if (d == bestd && rndint(++nb) == 0) { bestType = 1; bestS = s; bestT = t; }
            }
        }
        for (int i = 0; i < nK; i++) {
            int s = Kl[i];
            if (tabuOut[s] > iter && curf - 11 + deltaRem(s) <= bestf) continue;
            int d = -11 + deltaRem(s);
            if (d > bestd) { bestd = d; nb = 1; bestType = 2; bestS = s; bestT = -1; }
            else if (d == bestd && rndint(++nb) == 0) { bestType = 2; bestS = s; bestT = -1; }
        }
        if (bestType < 0) {   /* no admissible move: random drop */
            if (nK == 0) break;
            bestType = 2; bestS = Kl[rndint(nK)]; bestT = -1;
        }
        if (bestType == 0) { addK(bestT); nadd++; tabuOut[bestT] = iter + 2 * TT; }
        else if (bestType == 1) { remK(bestS); addK(bestT); nswap++; tabuIn[bestS] = iter + TT + rndint(TT); tabuOut[bestT] = iter + 2 * TT; }
        else { remK(bestS); ndrop++; tabuIn[bestS] = iter + TT + rndint(TT); }
        int f_now = 11 * nK + mopen;
        if (f_now > bestf) {
            bestf = f_now; bestK_n = nK; memcpy(bestK, Kl, sizeof(int) * nK); lastImp = iter;
            np = 0; int ok = 1;
            int saveNK = nK; (void)saveNK;
            if (build_points(pts, &np) == 0) {
                write_idx(argv[3], pts, np, "best so far");
                fprintf(stderr, "[%.1fs] it %ld: new best f=%d (|K|=%d, m=%d, points %d)\n", cpu(), iter, bestf, nK, mopen, np);
            } else { fprintf(stderr, "point mapping failed\n"); ok = 0; }
            (void)ok;
        }
        if (iter - lastImp > STAG) {   /* perturbation: restart from best (prob PREST) and kick */
            npert++;
            if ((double)(rnd64() % 1000000) < PREST * 1000000) {
                while (nK > 0) remK(Kl[nK - 1]);
                for (int i = 0; i < bestK_n; i++) addK(bestK[i]);
            }
            int r = 2 + rndint(3);
            for (int k = 0; k < r && nK > 0; k++) remK(Kl[rndint(nK)]);
            /* refill with random free lines */
            for (int tries = 0; tries < NLN * 4; tries++) {
                int t = rndint(NLN);
                if (!inK[t] && lc[t] == 0) addK(t);
            }
            lastImp = iter;
        }
    }
    /* final: verify state from scratch and report */
    int ok = 1;
    for (int i = 0; i < bestK_n && ok; i++) for (int j = i + 1; j < bestK_n; j++) if (conflict(bestK[i], bestK[j])) { ok = 0; break; }
    fprintf(stderr, "done: %ld iterations, best f=%d (|K|=%d) add=%ld swap=%ld drop=%ld pert=%ld; best clique check %d\n",
            iter, bestf, bestK_n, nadd, nswap, ndrop, npert, ok);
    printf("best %d\n", bestf);
    return 0;
}
