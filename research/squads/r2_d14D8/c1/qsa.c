/* qsa.c (c1, squad r2_d14D8): anneal the level family D7 x Z_k on the Sigma-symmetric quotient, exact cost.
   Adapted from round-1 symsa.c. Lift group Z_m, m = 5k; slot voltage = (LEV + 5C) mod 5k.
   Hexagon slots have LEV 0; the two phi slots of each point orbit have LEV 1 and 2 and the same target (K, T).
   Moves: change one sub-voltage C (85%); swap the phi targets (K, T) of two point orbits (15%, both phi slots).
   COST = sum over sample representatives of uncovered (line, level) pairs after walks of length 7 (exact for the
   lift, because Sigma x Z_m acts; a full check over all NP representatives runs whenever the sample is clean).
   usage: qsa design_in k_start k_max seconds seed nsample outprefix
   Writes outprefix_k{k}.txt on each exact zero, outprefix_last.txt at the end. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;
static int NP, S, D, NE, KS, M;
static int *EK, *ET, *ELV, *EC, *EW;
static u64 *Pa, *La;
static u64 FULL;
static u64 rs = 88172645463325252ULL;
static u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static double urand(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

/* voltage of a slot: w = (LEV + 5 C) mod 5k, so w mod 5 = LEV (the D7 level) and C in Z_k runs over the coset
   {w : w = LEV mod 5} bijectively (valid for every k, including k divisible by 5, where Z_5 x Z_k is not cyclic). */
static inline int slot_w(int lev, int c) { return (lev + 5 * c) % M; }
static void set_k(int k) {
    KS = k; M = 5 * k; FULL = (M == 64) ? ~0ULL : ((1ULL << M) - 1);
    for (int e = 0; e < NE; e++) EW[e] = slot_w(ELV[e], EC[e]);
}

static inline u64 rot(u64 x, int w) { if (!w) return x; return ((x << w) | (x >> (M - w))) & FULL; }

static long long cost_src(int i0) {
    memset(Pa, 0, sizeof(u64) * NP * S);
    Pa[(size_t)i0 * S] = 1ULL;
    u64 *cur = Pa, *nxt = La;
    for (int step = 1; step <= 7; step++) {
        memset(nxt, 0, sizeof(u64) * NP * S);
        if (step % 2 == 1) {                       /* point -> line */
            for (int i = 0; i < NP; i++) {
                const u64 *x = cur + (size_t)i * S;
                for (int s = 0; s < D; s++) {
                    int e = D * i + s, k = EK[e], t = ET[e], w = EW[e];
                    u64 *y = nxt + (size_t)k * S;
                    for (int r = 0; r < S; r++) { u64 v = x[r]; if (!v) continue; int rr = r + t; if (rr >= S) rr -= S; y[rr] |= rot(v, w); }
                }
            }
        } else {                                   /* line -> point */
            for (int i = 0; i < NP; i++) {
                u64 *y = nxt + (size_t)i * S;
                for (int s = 0; s < D; s++) {
                    int e = D * i + s, k = EK[e], t = ET[e], w = EW[e];
                    const u64 *x = cur + (size_t)k * S;
                    int wn = (M - w) % M;
                    for (int r = 0; r < S; r++) { u64 v = x[r]; if (!v) continue; int rr = r - t; if (rr < 0) rr += S; y[rr] |= rot(v, wn); }
                }
            }
        }
        u64 *tmp = cur; cur = nxt; nxt = tmp;
    }
    long long unc = 0;
    for (size_t j = 0; j < (size_t)NP * S; j++) unc += M - __builtin_popcountll(cur[j]);
    return unc;
}

static long long cost_sum(const int *src, int ns, long long lim) {
    long long tot = 0;
    for (int j = 0; j < ns; j++) { tot += cost_src(src[j]); if (tot > lim) return tot; }
    return tot;
}

static void swap_phi(int i1, int i2) {          /* exchange the phi targets of two point orbits */
    for (int s = D - 2; s < D; s++) {
        int e1 = D * i1 + s, e2 = D * i2 + s, tk = EK[e1], tt = ET[e1];
        EK[e1] = EK[e2]; ET[e1] = ET[e2]; EK[e2] = tk; ET[e2] = tt;
    }
}

static void write_design(const char *fn) {
    FILE *f = fopen(fn, "w");
    fprintf(f, "%d %d %d\n", NP, S, D);
    for (int e = 0; e < NE; e++) fprintf(f, "%d %d %d %d\n", EK[e], ET[e], ELV[e], EC[e]);
    fclose(f);
}

int main(int argc, char **argv) {
    if (argc < 8) { fprintf(stderr, "usage: qsa design_in k_start k_max seconds seed nsample outprefix\n"); return 2; }
    FILE *f = fopen(argv[1], "r"); if (!f) { perror("design"); return 2; }
    int k0 = atoi(argv[2]), kmax = atoi(argv[3]); double secs = atof(argv[4]);
    rs ^= (u64)atoll(argv[5]) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 10; i++) rnd();
    int nsample = atoi(argv[6]); const char *outp = argv[7];
    double T = getenv("QT") ? atof(getenv("QT")) : 0.6;
    if (fscanf(f, "%d %d %d", &NP, &S, &D) != 3) { fprintf(stderr, "bad header\n"); return 2; }
    NE = NP * D;
    EK = malloc(sizeof(int) * NE); ET = malloc(sizeof(int) * NE); ELV = malloc(sizeof(int) * NE);
    EC = malloc(sizeof(int) * NE); EW = malloc(sizeof(int) * NE);
    for (int e = 0; e < NE; e++)
        if (fscanf(f, "%d %d %d %d", &EK[e], &ET[e], &ELV[e], &EC[e]) != 4) { fprintf(stderr, "short design\n"); return 2; }
    fclose(f);
    for (int e = 0; e < NE; e++) EC[e] %= k0;
    set_k(k0);
    Pa = malloc(sizeof(u64) * NP * S); La = malloc(sizeof(u64) * NP * S);
    int cap = 3 * nsample + 16; int *src = malloc(sizeof(int) * cap); int ns = 0;
    int *bad = malloc(sizeof(int) * NP);
    for (int j = 0; j < nsample; j++) src[ns++] = (int)(rnd() % (u64)NP);
    if (getenv("QFULL")) {                      /* cross-check: sum over all reps (total over lift sources = S * sum) */
        long long full = 0; for (int i = 0; i < NP; i++) full += cost_src(i);
        printf("FULLREPS %lld TOTAL_OVER_ALL_SOURCES %lld\n", full, full * S); return 0;
    }
    long long cur = cost_sum(src, ns, 1LL << 60);
    time_t t0 = time(NULL);
    long long it = 0, acc = 0;
    fprintf(stderr, "start k=%d m=%d sample=%d cost=%lld T=%.2f\n", KS, M, ns, cur, T);
    while (difftime(time(NULL), t0) < secs) {
        it++;
        int kind, e = 0, old = 0, i1 = 0, i2 = 0;
        if (urand() < 0.85) {                       /* change one sub-voltage */
            kind = 0; e = (int)(rnd() % (u64)NE); old = EC[e];
            int nv = (int)(rnd() % (u64)(KS - 1)); if (nv >= old) nv++;
            EC[e] = nv; EW[e] = slot_w(ELV[e], nv);
        } else {                                    /* swap phi targets of two point orbits */
            kind = 1; i1 = (int)(rnd() % (u64)NP); i2 = (int)(rnd() % (u64)NP);
            if (i1 == i2) continue;
            swap_phi(i1, i2);
        }
        double thr = (double)cur - T * log(urand() + 1e-300);
        long long nc = cost_sum(src, ns, (long long)floor(thr));
        if ((double)nc <= thr) { cur = nc; acc++; }
        else {                                      /* undo */
            if (kind == 0) { EC[e] = old; EW[e] = slot_w(ELV[e], old); }
            else swap_phi(i1, i2);
        }
        if (cur == 0) {                             /* clean sample: full check over all representatives */
            long long full = 0; int nbad = 0;
            for (int i = 0; i < NP; i++) { long long c = cost_src(i); full += c; if (c) bad[nbad++] = i; }
            fprintf(stderr, "  clean sample at k=%d (it %lld, %.0fs): full COST over reps = %lld (bad reps %d)\n",
                    KS, it, difftime(time(NULL), t0), full, nbad);
            if (full == 0) {
                char fn[512]; snprintf(fn, sizeof fn, "%s_k%d.txt", outp, KS); write_design(fn);
                printf("FULL_OK k=%d m=%d iters=%lld secs=%.0f file=%s\n", KS, M, it, difftime(time(NULL), t0), fn);
                fflush(stdout);
                if (KS >= kmax) break;
                int nk = KS + 1; while (nk % 5 == 0) nk++;
                if (nk > kmax) break;
                set_k(nk);
            } else {
                if (ns + nbad > cap) {              /* rebuild sample: bad reps first, then random ones */
                    ns = 0;
                    for (int j = 0; j < nbad && ns < nsample; j++) src[ns++] = bad[j];
                    while (ns < nsample) src[ns++] = (int)(rnd() % (u64)NP);
                } else {
                    for (int j = 0; j < nbad && j < 8; j++) src[ns++] = bad[j];
                }
            }
            cur = cost_sum(src, ns, 1LL << 60);
        }
        if (it % 500 == 0)
            fprintf(stderr, "it %lld k=%d cost=%lld acc=%.3f sample=%d t=%.0fs\n", it, KS, cur, (double)acc / it, ns,
                    difftime(time(NULL), t0));
    }
    char fn[512]; snprintf(fn, sizeof fn, "%s_last.txt", outp); write_design(fn);
    printf("END k=%d m=%d iters=%lld cost=%lld last=%s\n", KS, M, it, cur, fn);
    return 0;
}
