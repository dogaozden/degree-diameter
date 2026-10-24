/* symsa.c (c4, squad r1_d14D8): annealing over Singer-invariant voltage lifts of H(11) + 2 matchings.

   Quotient graph: point orbits i (NP = 1332, each of size S = 133 under Sigma = <g>, g = C^10), line orbits k.
   Point orbit i has 14 slots e = 14 i + s: slots 0..11 hexagon (target line orbit k, shift t), slots 12,13 the
   matchings. Lift voltage of slot e: w_e in Z_m. The lift (degree 14) is the Z_133 x Z_m cover of the quotient:
   point (a, i, h) ~ line (a + t, k, h + w).  Walks of length exactly 7 from (point rep i, 0, 0) reach every line
   (b, k, h') iff the bitset DP below marks all (k, b, h'). COST(i) = number of unreached (line, level) pairs from
   the representative of point orbit i; the total over all 177156 points is S * sum over reps (Sigma-invariance).

   Usage: symsa qstruct.txt m_start m_max seconds seed nsample outprefix [init.txt]
   init.txt: NP*14 lines "k t w" (same format as the output). Writes outprefix_m{m}.txt on every full success. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>
#include <ctype.h>

typedef uint64_t u64;
static int NP, S = 133, M, NE;
static int *EK, *ET, *EW;
static u64 *Pa, *La;
static u64 FULL;
static u64 rs = 88172645463325252ULL;
static u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static double urand(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

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
                for (int s = 0; s < 14; s++) {
                    int e = 14 * i + s, k = EK[e], t = ET[e], w = EW[e];
                    u64 *y = nxt + (size_t)k * S;
                    for (int r = 0; r < S; r++) { u64 v = x[r]; if (!v) continue; int rr = r + t; if (rr >= S) rr -= S; y[rr] |= rot(v, w); }
                }
            }
        } else {                                   /* line -> point (reverse the same edges) */
            for (int i = 0; i < NP; i++) {
                u64 *y = nxt + (size_t)i * S;
                for (int s = 0; s < 14; s++) {
                    int e = 14 * i + s, k = EK[e], t = ET[e], w = EW[e];
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

/* sum of costs over sources, abandoned as soon as the running sum exceeds lim (returns > lim then) */
static long long cost_sum(const int *src, int ns, long long lim) {
    long long tot = 0;
    for (int j = 0; j < ns; j++) { tot += cost_src(src[j]); if (tot > lim) return tot; }
    return tot;
}

static int valid_orbit(int i) {                    /* 14 slots must give distinct (k,t): no multi-edges */
    for (int s = 0; s < 14; s++) for (int u = 0; u < s; u++) {
        int e = 14 * i + s, f = 14 * i + u;
        if (EK[e] == EK[f] && ET[e] == ET[f]) return 0;
    }
    return 1;
}

static void write_params(const char *fn) {
    FILE *f = fopen(fn, "w");
    for (int e = 0; e < NE; e++) fprintf(f, "%d %d %d\n", EK[e], ET[e], EW[e]);
    fclose(f);
}

int main(int argc, char **argv) {
    if (argc < 8) { fprintf(stderr, "usage: symsa qstruct m_start m_max seconds seed nsample outprefix [init]\n"); return 2; }
    FILE *f = fopen(argv[1], "r"); if (!f) return 2;
    int m0 = atoi(argv[2]), mmax = atoi(argv[3]); double secs = atof(argv[4]);
    rs ^= (u64)atoll(argv[5]) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 10; i++) rnd();
    int nsample = atoi(argv[6]); const char *outp = argv[7];
    int Sread; if (fscanf(f, "%d %d", &NP, &Sread) != 2 || Sread != S) { fprintf(stderr, "bad qstruct\n"); return 2; }
    NE = 14 * NP;
    EK = malloc(sizeof(int) * NE); ET = malloc(sizeof(int) * NE); EW = malloc(sizeof(int) * NE);
    for (int e = 0; e < NE; e++) if (fscanf(f, "%d %d", &EK[e], &ET[e]) != 2) { fprintf(stderr, "short qstruct\n"); return 2; }
    fclose(f);
    M = m0; FULL = (M == 64) ? ~0ULL : ((1ULL << M) - 1);
    for (int e = 0; e < NE; e++) EW[e] = (int)(rnd() % (u64)M);
    if (argc > 8) {
        FILE *g = fopen(argv[8], "r"); if (!g) { perror("init"); return 2; }
        for (int e = 0; e < NE; e++) { int k, t, w; if (fscanf(g, "%d %d %d", &k, &t, &w) != 3) { fprintf(stderr, "short init\n"); return 2; }
            EK[e] = k; ET[e] = t; EW[e] = w; }
        fclose(g);
        for (int e = 0; e < NE; e++) if (EW[e] >= M) { fprintf(stderr, "init voltage >= m_start\n"); return 2; }
    }
    Pa = malloc(sizeof(u64) * NP * S); La = malloc(sizeof(u64) * NP * S);
    if (getenv("SYMCHECK")) {            /* cross-check mode: per-source costs for the listed orbits, then exit */
        char *lst = getenv("SYMCHECK"); long long tot = 0;
        for (char *p = lst; *p; ) { int i = (int)strtol(p, &p, 10); long long c = cost_src(i); tot += c;
            printf("SRC %d COST %lld\n", i, c); if (*p == ',') p++; else break; }
        printf("SUM %lld\n", tot); return 0;
    }
    int cap = NP; int *src = malloc(sizeof(int) * cap); int ns = 0;
    for (int j = 0; j < nsample; j++) src[ns++] = (int)(rnd() % (u64)NP);
    long long cur = cost_sum(src, ns, (long long)1 << 60);
    time_t t0 = time(NULL);
    double T = 0.6; long long it = 0, acc = 0;
    fprintf(stderr, "start m=%d sample=%d cost=%lld\n", M, ns, cur);
    while (difftime(time(NULL), t0) < secs) {
        it++;
        int kind; int e = 0, old = 0, e2 = -1, ok_k = 0, ok_t = 0, ok_w = 0;
        int i1 = 0, i2 = 0, sv = 0; int ek1, et1, ew1, ek2, et2, ew2;
        double u = urand();
        if (u < 0.9 || M < 2) {                     /* change one voltage */
            kind = 0; e = (int)(rnd() % (u64)NE); old = EW[e];
            int nv = (int)(rnd() % (u64)(M - 1)); if (nv >= old) nv++;
            EW[e] = nv;
        } else {                                    /* swap the matching targets of two point orbits */
            kind = 1; sv = 12 + (int)(rnd() % 2); i1 = (int)(rnd() % (u64)NP); i2 = (int)(rnd() % (u64)NP);
            if (i1 == i2) continue;
            int e1 = 14 * i1 + sv, e2b = 14 * i2 + sv;
            ek1 = EK[e1]; et1 = ET[e1]; ew1 = EW[e1]; ek2 = EK[e2b]; et2 = ET[e2b]; ew2 = EW[e2b];
            EK[e1] = ek2; ET[e1] = et2; EW[e1] = ew2; EK[e2b] = ek1; ET[e2b] = et1; EW[e2b] = ew1;
            if (!valid_orbit(i1) || !valid_orbit(i2)) {          /* undo */
                EK[e1] = ek1; ET[e1] = et1; EW[e1] = ew1; EK[e2b] = ek2; ET[e2b] = et2; EW[e2b] = ew2;
                continue;
            }
        }
        double thr = (double)cur - T * log(urand() + 1e-300);  /* accept iff new cost <= thr */
        long long nc = cost_sum(src, ns, (long long)floor(thr));
        if ((double)nc <= thr && nc <= (long long)1 << 40) {
            cur = nc; acc++;
        } else {                                    /* undo */
            if (kind == 0) EW[e] = old;
            else {
                int e1 = 14 * i1 + sv, e2b = 14 * i2 + sv;
                EK[e1] = ek1; ET[e1] = et1; EW[e1] = ew1; EK[e2b] = ek2; ET[e2b] = et2; EW[e2b] = ew2;
            }
        }
        (void)e2; (void)ok_k; (void)ok_t; (void)ok_w; (void)ew2;
        if (cur == 0) {                             /* sample clean: full check over all representatives */
            long long full = 0; int nbad = 0; int bad_list[64];
            for (int i = 0; i < NP; i++) { long long c = cost_src(i); full += c; if (c && nbad < 64) bad_list[nbad++] = i; }
            fprintf(stderr, "  sample clean at m=%d (it %lld): full COST over reps = %lld (bad reps %d)\n", M, it, full, nbad);
            if (full == 0) {
                char fn[512]; snprintf(fn, sizeof fn, "%s_m%d.txt", outp, M); write_params(fn);
                printf("FULL_OK m=%d iters=%lld secs=%.0f file=%s\n", M, it, difftime(time(NULL), t0), fn); fflush(stdout);
                if (M >= mmax) break;
                M++; FULL = (M == 64) ? ~0ULL : ((1ULL << M) - 1);
                /* voltages stay below the old m, so they remain valid at the larger m */
            } else {
                for (int j = 0; j < nbad && ns < cap; j++) src[ns++] = bad_list[j];
                if (ns >= cap) ns = nsample;
                fprintf(stderr, "  added %d bad reps to the sample (now %d)\n", nbad < 8 ? nbad : 8, ns);
            }
            cur = cost_sum(src, ns, (long long)1 << 60);
        }
        if (it % 200 == 0) { fprintf(stderr, "it %lld m=%d cost=%lld acc=%.3f t=%.0fs\n", it, M, cur, (double)acc / it, difftime(time(NULL), t0)); }
    }
    printf("END m_reached_full=%d iters=%lld\n", M, it);
    return 0;
}
