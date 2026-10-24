/* ils.c: squad round 3, card c5: fine-grained tabu swap search (ILS with plateau moves, in the spirit of
   Andrade-Resende-Werneck and of multi-neighbourhood tabu search for maximum independent sets) for a large set of
   pairwise opposite points of H(11), i.e. an independent set of the orthogonality graph of Q(6,11) (degree 16104).

   State: S (pairwise opposite, i.e. independent), tcnt[x] = #{s in S : B(x,s) = 0} for x not in S (tightness),
   sumS[x] = sum of those s (equal to the unique S-neighbour when tcnt[x] = 1).
   Lists: FR = {x not in S : tcnt 0} (free points), OT = {x not in S : tcnt 1} (1-tight points; ~66 for the 397 set).
   Step (one move per iteration):
     (a) ADD: insert a free point.
     (b) (1,2)-swap: owner x with two opposite 1-tight points u, v: remove x, insert u, v (aspiration: tabu ignored).
     (c) SWAP (plateau move): a non-tabu 1-tight point v enters, its owner x leaves; x is tabu for TTB+rand(TTR) steps
         (tabu applies to re-entry).  No (1,2)-swap exists in (c), so a swap never frees a point by itself.
     (d) DROP: remove a random point (only if no 1-tight point is admissible).
   Stagnation: STAG steps without beating the epoch best -> perturbation: with probability PREST restore the global best,
   then force-insert KPERT random points of tightness in [KLO,KHI] (removing their neighbours, tabu for them).
   Writes the best set (point indices) to OUT_IDX whenever it improves.

   usage: ils HEXFILE INIT_IDX|- OUT_IDX CPU_SECONDS SEED [TTB TTR STAG KPERT PREST KLO KHI]
   defaults: TTB 7, TTR 10, STAG 50000, KPERT 2, PREST 0.5, KLO 2, KHI 4 (kick points have tightness in [KLO,KHI]).  Single thread; CPU-time limit via clock(). */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>

#define QQ 11
#define KK 12           /* q+1 */
#define PMAX 16200      /* |perp(x)| = 16104 */

static int N, NL;
static int32_t *lp, *pl;        /* NL x KK point indices of lines; N x KK line indices of points */
static uint8_t *co;             /* N x 7 coordinates */
static int8_t *wd;              /* N x 7: B(x,y) = sum_k wd[x][k] * co[y][k] mod 11 */
static int32_t *tcnt, *sumS, *posS, *posFR, *posOT, *Sl, *FRl, *OTl;
static uint8_t *inS;
static long *tabu;
static int ns = 0, nfr = 0, not = 0;
static int32_t tb[PMAX];
static uint64_t rs = 0x9E3779B97F4A7C15ULL;

static inline uint64_t rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static double cpu(void) { return (double)clock() / CLOCKS_PER_SEC; }

static inline int Bxy(int x, int y) {
    const int8_t *w = wd + 7L * x; const uint8_t *v = co + 7L * y;
    int s = w[0]*v[0] + w[1]*v[1] + w[2]*v[2] + w[3]*v[3] + w[4]*v[4] + w[5]*v[5] + w[6]*v[6];
    s %= QQ; return s < 0 ? s + QQ : s;
}

/* all y != x with B(x,y) = 0 (16104 of them), by the paths x-L1-p1-L2-p2 in the incidence graph */
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

static inline void fr_add(int x) { posFR[x] = nfr; FRl[nfr++] = x; }
static inline void fr_del(int x) { int p = posFR[x]; int32_t y = FRl[--nfr]; FRl[p] = y; posFR[y] = p; posFR[x] = -1; }
static inline void ot_add(int x) { posOT[x] = not; OTl[not++] = x; }
static inline void ot_del(int x) { int p = posOT[x]; int32_t y = OTl[--not]; OTl[p] = y; posOT[y] = p; posOT[x] = -1; }

/* insert r (must be free: not in S, tcnt 0) */
static void add_v(int r) {
    fr_del(r);
    inS[r] = 1; posS[r] = ns; Sl[ns++] = r;
    int n = perp(r, tb);
    for (int i = 0; i < n; i++) {
        int x = tb[i]; int a = tcnt[x];
        if (a == 0) { fr_del(x); ot_add(x); }
        else if (a == 1) ot_del(x);
        tcnt[x] = a + 1; sumS[x] += r;
    }
}

/* remove r from S */
static void del_v(int r) {
    int p = posS[r]; int32_t y = Sl[--ns]; Sl[p] = y; posS[y] = p; posS[r] = -1;
    inS[r] = 0;
    int n = perp(r, tb);
    for (int i = 0; i < n; i++) {
        int x = tb[i]; int a = tcnt[x];
        tcnt[x] = a - 1; sumS[x] -= r;
        if (a == 1) { ot_del(x); fr_add(x); }
        else if (a == 2) ot_add(x);
    }
    fr_add(r);   /* tcnt[r] is 0: S is independent */
}

/* a (1,2)-swap: two opposite 1-tight points with the same owner */
static int find12(int *ox, int *ua, int *ub) {
    for (int i = 0; i < not; i++) {
        int u = OTl[i], o = sumS[u];
        for (int j = i + 1; j < not; j++) {
            int v = OTl[j];
            if (sumS[v] == o && Bxy(u, v) != 0) { *ox = o; *ua = u; *ub = v; return 1; }
        }
    }
    return 0;
}

static void write_set(const char *fn, const int32_t *S, int k, const char *tag) {
    FILE *f = fopen(fn, "w"); if (!f) return;
    fprintf(f, "# %s: %d points, pairwise opposite (squad r3 c5 ils, H(11) point indices)\n", tag, k);
    for (int i = 0; i < k; i++) fprintf(f, "%d\n", S[i]);
    fclose(f);
}

/* recompute everything from scratch: returns 0 if consistent */
static int verify_state(void) {
    int32_t *t2 = calloc(N, sizeof(int32_t)), *s2 = calloc(N, sizeof(int32_t)); int bad = 0;
    for (int i = 0; i < ns && !bad; i++) for (int j = i + 1; j < ns; j++) if (Bxy(Sl[i], Sl[j]) == 0) { bad = 1; break; }
    for (int i = 0; i < ns && !bad; i++) { int n = perp(Sl[i], tb); for (int j = 0; j < n; j++) { t2[tb[j]]++; s2[tb[j]] += Sl[i]; } }
    long c0 = 0, c1 = 0;
    for (int x = 0; x < N && !bad; x++) {
        if (inS[x]) { if (t2[x] != 0) bad = 2; continue; }
        if (t2[x] != tcnt[x] || (t2[x] == 1 && s2[x] != sumS[x])) bad = 3;
        if (t2[x] == 0) c0++;
        if (t2[x] == 1) c1++;
    }
    if (c0 != nfr || c1 != not) bad = 4;
    free(t2); free(s2);
    return bad;
}

int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: ils HEXFILE INIT_IDX|- OUT_IDX CPU_SECONDS SEED [TTB TTR STAG KPERT PREST]\n"); return 1; }
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
    tcnt = calloc(N, 4); sumS = calloc(N, 4); posS = malloc(4L * N); posFR = malloc(4L * N); posOT = malloc(4L * N);
    Sl = malloc(4L * N); FRl = malloc(4L * N); OTl = malloc(4L * N); inS = calloc(N, 1); tabu = calloc(N, sizeof(long));
    for (int x = 0; x < N; x++) { posS[x] = -1; posOT[x] = -1; posFR[x] = x; FRl[x] = x; }
    nfr = N; not = 0; ns = 0;

    double secs = atof(argv[4]);
    rs ^= (uint64_t)atoll(argv[5]) * 0x2545F4914F6CDD1DULL; for (int i = 0; i < 20; i++) rnd64();
    int ttb = argc > 6 ? atoi(argv[6]) : 7, ttr = argc > 7 ? atoi(argv[7]) : 10;
    long stagmax = argc > 8 ? atol(argv[8]) : 50000;
    int kpert = argc > 9 ? atoi(argv[9]) : 2;
    double prest = argc > 10 ? atof(argv[10]) : 0.5;
    int klo = argc > 11 ? atoi(argv[11]) : 2, khi = argc > 12 ? atoi(argv[12]) : 4;

    /* initial set */
    if (strcmp(argv[2], "-") != 0) {
        FILE *g = fopen(argv[2], "r"); if (!g) return 1; char buf[256];
        while (fgets(buf, sizeof buf, g)) {
            int v; if (buf[0] == '#' || sscanf(buf, "%d", &v) != 1) continue;
            if (v < 0 || v >= N || inS[v] || tcnt[v] != 0) { fprintf(stderr, "bad or conflicting initial point %d\n", v); return 1; }
            add_v(v);
        }
        fclose(g);
    }
    fprintf(stderr, "initial |S| = %d, 1-tight %d, free %d\n", ns, not, nfr);

    int32_t *bestS = malloc(4L * N); int bestn = ns; memcpy(bestS, Sl, 4L * ns);
    int epochBest = ns; long stag = 0;
    long iter = 0, nadd = 0, n12 = 0, nswap = 0, ndrop = 0, npert = 0, nrest = 0;
    double lastrep = 0;
    int ox, ua, ub;
    if (bestn > 0) write_set(argv[3], bestS, bestn, "best so far");
    while (1) {
        if ((iter & 511) == 0) {
            double now = cpu();
            if (now > secs) break;
            if (now - lastrep > 30) {
                lastrep = now;
                long h2 = 0, h3 = 0, h4 = 0;
                for (int x = 0; x < N; x++) if (!inS[x]) { if (tcnt[x] == 2) h2++; else if (tcnt[x] == 3) h3++; else if (tcnt[x] == 4) h4++; }
                fprintf(stderr, "[%.0fs] it %ld |S|=%d best=%d tight1=%d tight2=%ld tight3=%ld tight4=%ld add=%ld 12=%ld swap=%ld drop=%ld pert=%ld rest=%ld\n",
                        now, iter, ns, bestn, not, h2, h3, h4, nadd, n12, nswap, ndrop, npert, nrest);
            }
        }
        iter++;
        if (nfr > 0) {                                  /* (a) ADD */
            add_v(FRl[rndint(nfr)]); nadd++;
        } else if (find12(&ox, &ua, &ub)) {             /* (b) (1,2)-swap */
            del_v(ox); add_v(ua); add_v(ub); n12++;
        } else {
            int v = -1;                                 /* (c) SWAP: non-tabu 1-tight point enters */
            if (not > 0) {
                for (int t = 0; t < 64 && v < 0; t++) { int c = OTl[rndint(not)]; if (tabu[c] <= iter) v = c; }
                if (v < 0) for (int i = 0; i < not; i++) if (tabu[OTl[i]] <= iter) { v = OTl[i]; break; }
            }
            if (v >= 0) {
                int x = sumS[v];
                del_v(x); tabu[x] = iter + ttb + rndint(ttr); add_v(v); nswap++;
            } else {                                    /* (d) DROP */
                int x = Sl[rndint(ns)];
                del_v(x); tabu[x] = iter + ttb + rndint(ttr); ndrop++;
            }
        }
        if (ns > epochBest) { epochBest = ns; stag = 0; } else stag++;
        if (ns > bestn) {
            bestn = ns; memcpy(bestS, Sl, 4L * ns);
            write_set(argv[3], bestS, bestn, "best so far");
            fprintf(stderr, "[%.1fs] it %ld: new best %d\n", cpu(), iter, bestn);
        }
        if (stag > stagmax) {                           /* perturbation */
            npert++;
            if ((rnd64() % 1000000) < (uint64_t)(prest * 1000000)) {
                nrest++;
                while (ns > 0) del_v(Sl[ns - 1]);
                for (int i = 0; i < bestn; i++) add_v(bestS[i]);
            }
            for (int t = 0; t < kpert; t++) {
                int v = -1; long tr = 0;
                do { int c = rndint(N); tr++; if (!inS[c] && tcnt[c] >= klo && tcnt[c] <= khi) v = c; } while (v < 0 && tr < 2000000);
                if (v < 0 && not > 0) v = OTl[rndint(not)];
                if (v < 0) continue;
                for (int i = ns - 1; i >= 0; i--) { int s = Sl[i]; if (Bxy(v, s) == 0) { del_v(s); tabu[s] = iter + ttb + rndint(ttr); } }
                add_v(v);
            }
            while (nfr > 0) add_v(FRl[rndint(nfr)]);
            epochBest = ns; stag = 0;
        }
    }
    int vs = verify_state();
    fprintf(stderr, "done: %ld iterations, best %d, add %ld, 12-swap %ld, swap %ld, drop %ld, pert %ld, restores %ld; state check %d\n",
            iter, bestn, nadd, n12, nswap, ndrop, npert, nrest, vs);
    if (vs) fprintf(stderr, "WARNING: state verification failed (%d)\n", vs);
    write_set(argv[3], bestS, bestn, "best");
    printf("best %d\n", bestn);
    return 0;
}
