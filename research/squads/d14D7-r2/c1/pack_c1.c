/* pack.c: dense packings of type-2 unit zones in GH(q) (one matching). Session cell-14-7 (second), 2026-10-24.
   A unit is an incident flag (p,l). Its point zone is p plus the q^2 points collinear with p off l; its line zone is
   l plus the q^2 lines meeting l off p. Units of one matching need pairwise disjoint point zones and pairwise
   disjoint line zones (t2design.c). This program maximizes the number of such flags by simulated annealing on
   flag sets with an overlap penalty (energy = -#flags + lambda * #overlaps), then removes overlaps greedily.
   Usage: pack GHFILE SECONDS SEED OUTFLAGS [INFLAGS]
   Output: lines "p l" (a flag set with disjoint zones). Compile: gcc -O3 -march=native -lm -o pack pack.c */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>

static int P, q, Q1, ZN;          /* ZN = q^2 + 1 */
static int32_t *LP, *PL;
static uint64_t rs = 0x9E3779B97F4A7C15ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline int rndi(int n) { return (int)(rnd() % (uint64_t)n); }
static inline double rndu(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static uint16_t *occP, *occL;     /* zone occupancy */
static long over = 0;             /* sum over elements of max(0, occ - 1) */
static int *fl_p, *fl_l, nf = 0;  /* flags in the set */
static int *flagAt;               /* flagAt[p] = index of the flag with freed point p, or -1 */

static int zoneP(int p, int l, int *out) { int c = 0; out[c++] = p;
    for (int a = 0; a < Q1; a++) { int L = PL[p * Q1 + a]; if (L == l) continue; for (int b = 0; b < Q1; b++) { int w = LP[L * Q1 + b]; if (w != p) out[c++] = w; } }
    return c; }
static int zoneL(int p, int l, int *out) { int c = 0; out[c++] = l;
    for (int a = 0; a < Q1; a++) { int x = LP[l * Q1 + a]; if (x == p) continue; for (int b = 0; b < Q1; b++) { int K = PL[x * Q1 + b]; if (K != l) out[c++] = K; } }
    return c; }
static int zp[512], zl[512];
/* overlap change if the flag were added */
static int dAdd(int p, int l) { int d = 0; zoneP(p, l, zp); zoneL(p, l, zl);
    for (int i = 0; i < ZN; i++) { d += occP[zp[i]] > 0; d += occL[zl[i]] > 0; } return d; }
static void addF(int p, int l) { zoneP(p, l, zp); zoneL(p, l, zl);
    for (int i = 0; i < ZN; i++) { if (occP[zp[i]]++ > 0) over++; if (occL[zl[i]]++ > 0) over++; }
    fl_p[nf] = p; fl_l[nf] = l; flagAt[p] = nf; nf++; }
static int dRem(int idx) { int p = fl_p[idx], l = fl_l[idx], d = 0; zoneP(p, l, zp); zoneL(p, l, zl);
    for (int i = 0; i < ZN; i++) { d -= occP[zp[i]] > 1; d -= occL[zl[i]] > 1; } return d; }
static void remF(int idx) { int p = fl_p[idx], l = fl_l[idx]; zoneP(p, l, zp); zoneL(p, l, zl);
    for (int i = 0; i < ZN; i++) { if (--occP[zp[i]] > 0) over--; if (--occL[zl[i]] > 0) over--; }
    flagAt[p] = -1; nf--; if (idx != nf) { fl_p[idx] = fl_p[nf]; fl_l[idx] = fl_l[nf]; flagAt[fl_p[idx]] = idx; } }

/* ---- kick (destroy-and-repair) helpers, used when env KICK=seconds is set ---- */
static int lgT[4096], lgP[4096], lgL[4096], nlog = 0;   /* undo log: lgT=1 added (p,l), lgT=0 removed (p,l) */
static void logAdd(int p, int l) { addF(p, l); if (nlog < 4096) { lgT[nlog] = 1; lgP[nlog] = p; lgL[nlog] = l; nlog++; } }
static void logRem(int idx) { int p = fl_p[idx], l = fl_l[idx]; remF(idx); if (nlog < 4096) { lgT[nlog] = 0; lgP[nlog] = p; lgL[nlog] = l; nlog++; } }
/* points at collinearity distance <= R from x (R = 2: incidence distance <= 4), marked with gen */
static int ballPts(int x, int R, int *out, int32_t *mark, int32_t gen) {
    int c = 0, s = 0; mark[x] = gen; out[c++] = x;
    for (int r = 0; r < R; r++) { int e = c;
        for (int i = s; i < e; i++) { int y = out[i];
            for (int a = 0; a < Q1; a++) { int L = PL[y * Q1 + a];
                for (int b = 0; b < Q1; b++) { int z = LP[L * Q1 + b]; if (mark[z] != gen) { mark[z] = gen; out[c++] = z; } } } }
        s = e; }
    return c; }

int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage: pack GHFILE SECONDS SEED OUTFLAGS [INFLAGS]\n"); return 2; }
    FILE *f = fopen(argv[1], "r"); if (!f || fscanf(f, "%d %d", &P, &q) != 2) return 2; Q1 = q + 1; ZN = q * q + 1;
    LP = malloc(sizeof(int32_t) * (size_t)P * Q1); PL = malloc(sizeof(int32_t) * (size_t)P * Q1);
    for (size_t i = 0; i < (size_t)P * Q1; i++) if (fscanf(f, "%d", &LP[i]) != 1) return 2;
    fclose(f);
    { int *c = calloc(P, sizeof(int)); for (int l = 0; l < P; l++) for (int k = 0; k < Q1; k++) { int p = LP[l * Q1 + k]; PL[p * Q1 + c[p]++] = l; } free(c); }
    double secs = atof(argv[2]); if (secs <= 0) secs = 1e-9; rs ^= strtoull(argv[3], 0, 10) * 0x2545F4914F6CDD1DULL;
    occP = calloc(P, 2); occL = calloc(P, 2); fl_p = malloc(sizeof(int) * P); fl_l = malloc(sizeof(int) * P);
    flagAt = malloc(sizeof(int) * P); for (int i = 0; i < P; i++) flagAt[i] = -1;
    if (argc > 5) { f = fopen(argv[5], "r"); int a, b; while (f && fscanf(f, "%d %d", &a, &b) == 2) if (flagAt[a] < 0) addF(a, b); if (f) fclose(f);
        if (!getenv("CHECKONLY")) fprintf(stderr, "start: %d flags, overlaps %ld\n", nf, over); }
    if (getenv("GROW")) {   /* compact growth: from a seed, add chained flags in BFS order */
        int *qq = malloc(sizeof(int) * P), qh = 0, qt = 0; int seeds = atoi(getenv("GROW"));
        int *cand = malloc(sizeof(int) * 4 * Q1 * Q1 * Q1 * Q1), *cl = malloc(sizeof(int) * 4 * Q1 * Q1 * Q1 * Q1);
        for (int sd = 0; sd < seeds; sd++) {
            int p = rndi(P), l = PL[p * Q1 + rndi(Q1)];
            if (flagAt[p] >= 0 || dAdd(p, l)) continue;
            addF(p, l); qq[qt++] = p;
            while (qh < qt) {
                int pi = qq[qh++]; int idx = flagAt[pi]; if (idx < 0) continue; int li = fl_l[idx];
                int nc = 0;
                /* forward chains: pj at distance 2 from x in li (x != pi) via a line M != li; any flag line through pj except M */
                for (int a = 0; a < Q1; a++) { int x = LP[li * Q1 + a]; if (x == pi) continue;
                    for (int b = 0; b < Q1; b++) { int M = PL[x * Q1 + b]; if (M == li) continue;
                        for (int c = 0; c < Q1; c++) { int pj = LP[M * Q1 + c]; if (pj == x) continue;
                            for (int d = 0; d < Q1; d++) { int lj = PL[pj * Q1 + d]; if (lj == M) continue; cand[nc] = pj; cl[nc] = lj; nc++; } } } }
                /* backward chains: pj with flag line lj through y, y collinear with pi via N != li */
                for (int a = 0; a < Q1; a++) { int N = PL[pi * Q1 + a]; if (N == li) continue;
                    for (int b = 0; b < Q1; b++) { int y = LP[N * Q1 + b]; if (y == pi) continue;
                        for (int c = 0; c < Q1; c++) { int lj = PL[y * Q1 + c]; if (lj == N) continue;
                            for (int d = 0; d < Q1; d++) { int pj = LP[lj * Q1 + d]; if (pj == y) continue; cand[nc] = pj; cl[nc] = lj; nc++; } } } }
                for (int i = nc - 1; i > 0; i--) { int r = rndi(i + 1); int t1 = cand[i], t2 = cl[i]; cand[i] = cand[r]; cl[i] = cl[r]; cand[r] = t1; cl[r] = t2; }
                for (int i = 0; i < nc; i++) { int pj = cand[i], lj = cl[i]; if (flagAt[pj] >= 0 || occP[pj] || occL[lj]) continue; if (dAdd(pj, lj) == 0) { addF(pj, lj); qq[qt++] = pj; } }
            }
        }
        fprintf(stderr, "grow: %d flags, overlaps %ld\n", nf, over);
        for (int p = 0; p < P; p++) if (flagAt[p] < 0 && occP[p] == 0) for (int a = 0; a < Q1; a++) { int l = PL[p * Q1 + a]; if (dAdd(p, l) == 0) { addF(p, l); break; } }
        fprintf(stderr, "grow + fill: %d flags\n", nf);
    }
    if (getenv("CHECKONLY")) {   /* validate INFLAGS: incident flags, distinct points, disjoint zones */
        long bad = 0; for (int i = 0; i < nf; i++) { int ok = 0; for (int a = 0; a < Q1; a++) if (PL[fl_p[i] * Q1 + a] == fl_l[i]) ok = 1; if (!ok) bad++; }
        printf("%s %d flags, overlaps %ld, non-incident %ld\n", (over == 0 && bad == 0) ? "VALID" : "INVALID", nf, over, bad);
        return over == 0 && bad == 0 ? 0 : 1;
    }
    double lam0 = getenv("LAM0") ? atof(getenv("LAM0")) : 0.3, lam1 = getenv("LAM1") ? atof(getenv("LAM1")) : 3.0;
    double T0 = getenv("T0") ? atof(getenv("T0")) : 0.5, T1 = getenv("T1") ? atof(getenv("T1")) : 0.05;
    clock_t c0 = clock(); long it = 0; int best = 0;
    int *bp = malloc(sizeof(int) * P), *bl = malloc(sizeof(int) * P);
    for (;;) {
        it++;
        double fr = (double)(clock() - c0) / CLOCKS_PER_SEC / secs; if (fr >= 1.0) break;
        double lam = lam0 * pow(lam1 / lam0, fr), T = T0 * pow(T1 / T0, fr);
        int mv = rndi(3);
        if (mv == 0 || nf == 0) {           /* add a flag at a point not yet freed */
            int p = rndi(P); if (flagAt[p] >= 0) continue; if (occP[p]) { if (rndi(4)) continue; }
            int l = PL[p * Q1 + rndi(Q1)]; double dE = -1.0 + lam * dAdd(p, l);
            if (dE <= 0 || rndu() < exp(-dE / T)) addF(p, l);
        } else if (mv == 1) {                /* remove */
            int idx = rndi(nf); double dE = 1.0 + lam * dRem(idx);
            if (dE <= 0 || rndu() < exp(-dE / T)) remF(idx);
        } else {                             /* change the line of a flag, or move it to a collinear point */
            int idx = rndi(nf), p = fl_p[idx], l = fl_l[idx]; double d1 = dRem(idx); remF(idx);
            int p2 = p, l2;
            if (rndi(2)) { l2 = PL[p * Q1 + rndi(Q1)]; }
            else { int L = PL[p * Q1 + rndi(Q1)]; p2 = LP[L * Q1 + rndi(Q1)]; if (flagAt[p2] >= 0) p2 = p; l2 = PL[p2 * Q1 + rndi(Q1)]; }
            double dE = lam * (d1 + dAdd(p2, l2));
            if (dE <= 0 || rndu() < exp(-dE / T)) addF(p2, l2); else addF(p, l);
        }
        if ((it & 0xFFFFF) == 0) {
            if (over == 0 && nf > best) { best = nf; memcpy(bp, fl_p, sizeof(int) * nf); memcpy(bl, fl_l, sizeof(int) * nf); }
            if ((it & 0x7FFFFF) == 0) fprintf(stderr, "it %ldM flags %d overlaps %ld lam %.2f T %.3f best %d\n", it >> 20, nf, over, lam, T, best);
        }
    }
    /* remove overlaps greedily: repeatedly drop the flag with the most overlapped zone elements */
    while (over > 0) {
        int worst = -1, wc = -1;
        for (int i = 0; i < nf; i++) { int c = -dRem(i); if (c > wc) { wc = c; worst = i; } }
        remF(worst);
    }
    /* then fill greedily */
    for (int pass = 0; pass < 2; pass++) for (int p = 0; p < P; p++) if (flagAt[p] < 0 && occP[p] == 0) for (int a = 0; a < Q1; a++) { int l = PL[p * Q1 + a]; if (dAdd(p, l) == 0) { addF(p, l); break; } }
    if (nf < best) { while (nf) remF(nf - 1); for (int i = 0; i < best; i++) addF(bp[i], bl[i]); }
    if (getenv("KICK")) {   /* kick phase: destroy all flags with freed point in a ball of radius RAD around a random point,
                               repair by zero-overlap random samples inside the ball; keep if not worse (or with
                               probability exp(d/KT) when d < 0), else undo via the log */
        double ks = atof(getenv("KICK")); int R = getenv("RAD") ? atoi(getenv("RAD")) : 2;
        double KT = getenv("KT") ? atof(getenv("KT")) : 0.3; int KM = getenv("KM") ? atoi(getenv("KM")) : 4000;
        int32_t *mark = calloc(P, sizeof(int32_t)); int32_t gen = 0; int *ball = malloc(sizeof(int) * P);
        if (nf > best) { best = nf; memcpy(bp, fl_p, sizeof(int) * nf); memcpy(bl, fl_l, sizeof(int) * nf); }
        clock_t k0 = clock(); long kit = 0, kacc = 0;
        for (;;) {
            double kf = (double)(clock() - k0) / CLOCKS_PER_SEC / ks; if (kf >= 1.0) break;
            kit++; int x = rndi(P); gen++;
            int nb = ballPts(x, R, ball, mark, gen);
            int old = nf; nlog = 0;
            for (int i = nf - 1; i >= 0; i--) if (mark[fl_p[i]] == gen) logRem(i);
            int nrem = nlog;   /* first put back the destroyed flags (always feasible), then random zero-overlap samples */
            for (int t = 0; t < nrem; t++) if (lgT[t] == 0 && flagAt[lgP[t]] < 0 && dAdd(lgP[t], lgL[t]) == 0) logAdd(lgP[t], lgL[t]);
            for (int s2 = 0; s2 < KM; s2++) { int p = ball[rndi(nb)]; if (flagAt[p] >= 0) continue; int l = PL[p * Q1 + rndi(Q1)]; if (dAdd(p, l) == 0) logAdd(p, l); }
            int d = nf - old;
            if (d >= 0 || nlog >= 4096 || rndu() < exp(d / KT)) { kacc++;
                if (nf > best) { best = nf; memcpy(bp, fl_p, sizeof(int) * nf); memcpy(bl, fl_l, sizeof(int) * nf);
                    FILE *g = fopen(argv[4], "w"); if (g) { for (int i = 0; i < best; i++) fprintf(g, "%d %d\n", bp[i], bl[i]); fclose(g); } }
            } else {
                for (int t = nlog - 1; t >= 0; t--) { if (lgT[t]) remF(flagAt[lgP[t]]); else addF(lgP[t], lgL[t]); }
            }
        }
        fprintf(stderr, "kick: %ld kicks, %ld accepted, nf %d, best %d, overlaps %ld\n", kit, kacc, nf, best, over);
        free(mark); free(ball);
        if (nf < best) { while (nf) remF(nf - 1); for (int i = 0; i < best; i++) addF(bp[i], bl[i]); }
    }
    fprintf(stderr, "final:%d flags, overlaps %ld (%ld iterations)\n", nf, over, it);
    f = fopen(argv[4], "w"); for (int i = 0; i < nf; i++) fprintf(f, "%d %d\n", fl_p[i], fl_l[i]); fclose(f);
    return 0;
}
