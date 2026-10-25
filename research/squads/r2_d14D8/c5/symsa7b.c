/* symsa7.c (c5, squad r2_d14D8): annealing over Singer-type (Sigma = <g>, |Sigma| = 19) invariant voltage lifts of
   H(7) + 2 matchings, degree 10. Port of r1 c4 symsa.c (written for q = 11, degree 14) to q = 7.

   Quotient: point orbits i in [0, NP) (NP = 1032), each of size S = 19. Slot e = D*i + s, D = 10: slots s < 8 are
   hexagon lines (target line orbit k, shift t), slots 8, 9 the Sigma-equivariant matchings. Lift: point (a, i, h) ~
   line (a + t, k, h + w) with w = voltage of slot e. Walks of length 7 from (point rep i0, shift 0, level 0) reach every
   line state (b, k, h') iff bit h' of LY[7][k*S + b] is set; COST(i0) = number of unreached states. The exact total
   over all points is S * sum over representatives, so COST 0 over all representatives is the exact check.

   Moves: (a) targeted repair (prob PT): pick a sampled source i0, an unreached (line state, level h') at layer 7,
   a reached level h'' of the same line state, reconstruct one walk of length 7 from i0 to that line state, and
   re-voltage one edge of the walk by sigma*(h' - h'') so that the walk's endpoint moves to h'.
   (b) random voltage change; (c) swap of the matching targets of two point orbits.
   Accept with the annealing rule (T = 0.6) on the sum of COSTs over a sample of representatives; a clean sample
   triggers the full check over all representatives; on success the modulus is raised (voltages stay valid).

   Usage: symsa7 qstruct m_start m_max seconds seed nsample outprefix [init.txt] [pt]
   qstruct: "NP S D" then NP*D lines "k t". init.txt: NP*D lines "k t w" (optional starting voltages).
   Writes outprefix_m{m}.txt ("k t w" per slot) on every full success. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;
static int NP, S, D, M, NE;
static int *EK, *ET, *EW;
static int *REVN, **REV;
static u64 *LY[8];
static u64 FULL;
static u64 rs = 88172645463325252ULL;
static u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static double urand(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
static inline u64 rot(u64 x, int w) { if (!w) return x; return ((x << w) | (x >> (M - w))) & FULL; }

/* layers LY[0..7] of the walk DP from (i0, 0, 0): LY[s][x*S + b] = set of levels reached after exactly s steps */
static void dp_layers(int i0) {
    size_t NS = (size_t)NP * S;
    memset(LY[0], 0, sizeof(u64) * NS);
    LY[0][(size_t)i0 * S] = 1ULL;
    for (int step = 1; step <= 7; step++) {
        u64 *cur = LY[step - 1], *nxt = LY[step];
        memset(nxt, 0, sizeof(u64) * NS);
        if (step & 1) {                             /* point -> line */
            for (int i = 0; i < NP; i++) {
                const u64 *x = cur + (size_t)i * S;
                for (int s = 0; s < D; s++) {
                    int e = D * i + s, k = EK[e], t = ET[e], w = EW[e];
                    u64 *y = nxt + (size_t)k * S;
                    for (int r = 0; r < S; r++) { u64 v = x[r]; if (!v) continue; int rr = r + t; if (rr >= S) rr -= S; y[rr] |= rot(v, w); }
                }
            }
        } else {                                    /* line -> point (reverse the same edges) */
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
    }
}

static long long cost_src(int i0) {
    dp_layers(i0);
    long long unc = 0;
    size_t NS = (size_t)NP * S;
    for (size_t j = 0; j < NS; j++) unc += M - __builtin_popcountll(LY[7][j]);
    return unc;
}

static long long cost_sum(const int *src, int ns, long long lim) {
    long long tot = 0;
    for (int j = 0; j < ns; j++) { tot += cost_src(src[j]); if (tot > lim) return tot; }
    return tot;
}

static void build_rev(void) {
    for (int k = 0; k < NP; k++) REVN[k] = 0;
    for (int e = 0; e < NE; e++) { int k = EK[e]; REV[k][REVN[k]++] = e; }
}

static int valid_orbit(int i) {                    /* the D slots must give distinct (k,t): no multi-edges */
    for (int s = 0; s < D; s++) for (int u = 0; u < s; u++) {
        int e = D * i + s, f = D * i + u;
        if (EK[e] == EK[f] && ET[e] == ET[f]) return 0;
    }
    return 1;
}

/* backward reconstruction of one walk of length 7 from (i0, 0, 0) to line state (k7, b7) at level h7.
   Uses the layers of the current dp_layers call. ecs[s], sgs[s]: edge and direction (+1 forward, -1 reverse) of step s. */
static int reconstruct(int k7, int b7, int h7, int *ecs, int *sgs) {
    int x = k7, b = b7, h = h7;                    /* layer s: odd -> line (x = orbit, b = shift); even -> point */
    for (int s = 7; s >= 1; s--) {
        if (s & 1) {
            int cand[64], nc = 0;
            for (int u = 0; u < REVN[x] && nc < 64; u++) {
                int e = REV[x][u]; int i = e / D;
                int ap = ((b - ET[e]) % S + S) % S;
                int hp = ((h - EW[e]) % M + M) % M;
                if ((LY[s - 1][(size_t)i * S + ap] >> hp) & 1ULL) cand[nc++] = e;
            }
            if (!nc) return 0;
            int e = cand[rnd() % (u64)nc]; int i = e / D;
            ecs[s] = e; sgs[s] = +1;
            b = ((b - ET[e]) % S + S) % S; h = ((h - EW[e]) % M + M) % M; x = i;
        } else {
            int cand[16], nc = 0;
            for (int s2 = 0; s2 < D; s2++) {
                int e = D * x + s2, kk = EK[e];
                int bb = (b + ET[e]) % S, hp = (h + EW[e]) % M;
                if ((LY[s - 1][(size_t)kk * S + bb] >> hp) & 1ULL) cand[nc++] = e;
            }
            if (!nc) return 0;
            int e = cand[rnd() % (u64)nc];
            ecs[s] = e; sgs[s] = -1;
            b = (b + ET[e]) % S; h = (h + EW[e]) % M; x = EK[e];
        }
    }
    return b == 0 && h == 0;
}

static void write_params(const char *fn) {
    FILE *f = fopen(fn, "w");
    for (int e = 0; e < NE; e++) fprintf(f, "%d %d %d\n", EK[e], ET[e], EW[e]);
    fclose(f);
}

/* targeted repair move on source i0; returns the changed edge in *ec and its old voltage in *eo, or 0 if not applicable */
static int targeted(int i0, int *ec, int *eo) {
    dp_layers(i0);
    size_t NS = (size_t)NP * S;
    static size_t cand[1 << 16]; size_t nc = 0;
    for (size_t j = 0; j < NS; j++) { u64 v = LY[7][j]; if (v && v != FULL && nc < (1 << 16)) cand[nc++] = j; }
    if (!nc) return 0;
    for (int tries = 0; tries < 8; tries++) {
        size_t j = cand[rnd() % (u64)nc];
        u64 unc = ~LY[7][j] & FULL, reached = LY[7][j];
        int nu = __builtin_popcountll(unc), nr = __builtin_popcountll(reached);
        int hp = -1, hpp = -1;
        int pick = (int)(rnd() % (u64)nu);
        for (int h = 0; h < M; h++) if ((unc >> h) & 1ULL) { if (pick-- == 0) { hp = h; break; } }
        pick = (int)(rnd() % (u64)nr);
        for (int h = 0; h < M; h++) if ((reached >> h) & 1ULL) { if (pick-- == 0) { hpp = h; break; } }
        int k7 = (int)(j / S), b7 = (int)(j % S);
        int ecs[8], sgs[8];
        build_rev();
        if (!reconstruct(k7, b7, hpp, ecs, sgs)) continue;
        int st = 1 + (int)(rnd() % 7u);
        int e = ecs[st], sg = sgs[st];
        int delta = ((sg * (hp - hpp)) % M + M) % M;
        *ec = e; *eo = EW[e];
        EW[e] = (EW[e] + delta) % M;
        return 1;
    }
    return 0;
}

static int *bad_list_buf;
static int *badkeep, nbk = 0;                   /* representatives that were bad at the last full check (targets of repair moves) */

int main(int argc, char **argv) {
    if (argc < 8) { fprintf(stderr, "usage: symsa7 qstruct m_start m_max seconds seed nsample outprefix [init] [pt]\n"); return 2; }
    FILE *f = fopen(argv[1], "r"); if (!f) return 2;
    int m0 = atoi(argv[2]), mmax = atoi(argv[3]); double secs = atof(argv[4]);
    rs ^= (u64)atoll(argv[5]) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 10; i++) rnd();
    int nsample = atoi(argv[6]); const char *outp = argv[7];
    double PT = argc > 9 ? atof(argv[9]) : 0.5;
    if (fscanf(f, "%d %d %d", &NP, &S, &D) != 3) { fprintf(stderr, "bad qstruct header\n"); return 2; }
    NE = D * NP;
    EK = malloc(sizeof(int) * NE); ET = malloc(sizeof(int) * NE); EW = malloc(sizeof(int) * NE);
    for (int e = 0; e < NE; e++) if (fscanf(f, "%d %d", &EK[e], &ET[e]) != 2) { fprintf(stderr, "short qstruct\n"); return 2; }
    fclose(f);
    REVN = calloc(NP, sizeof(int)); REV = malloc(sizeof(int *) * NP);
    for (int k = 0; k < NP; k++) REV[k] = malloc(sizeof(int) * (D * 4));   /* reverse lists: capacity 4D per line orbit */
    M = m0; FULL = (M == 64) ? ~0ULL : ((1ULL << M) - 1);
    for (int e = 0; e < NE; e++) EW[e] = (int)(rnd() % (u64)M);
    if (argc > 8 && strcmp(argv[8], "-")) {
        FILE *g = fopen(argv[8], "r"); if (!g) { perror("init"); return 2; }
        for (int e = 0; e < NE; e++) { int k, t, w; if (fscanf(g, "%d %d %d", &k, &t, &w) != 3) { fprintf(stderr, "short init\n"); return 2; }
            EK[e] = k; ET[e] = t; EW[e] = w; }
        fclose(g);
        for (int e = 0; e < NE; e++) if (EW[e] >= M) { fprintf(stderr, "init voltage >= m_start\n"); return 2; }
    }
    for (int i = 0; i < NP; i++) if (!valid_orbit(i)) { fprintf(stderr, "initial multi-edge in orbit %d\n", i); return 2; }
    for (int t = 0; t < 8; t++) LY[t] = malloc(sizeof(u64) * (size_t)NP * S);
    if (getenv("SYMFULL")) {                        /* check mode: exact total over all representatives, then exit */
        long long full = 0; for (int i = 0; i < NP; i++) full += cost_src(i);
        printf("FULLSUM %lld\n", full); return 0;
    }
    int cap = NP; int *src = malloc(sizeof(int) * cap); int ns = 0;
    bad_list_buf = malloc(sizeof(int) * NP); badkeep = malloc(sizeof(int) * NP);
    for (int j = 0; j < nsample; j++) src[ns++] = (int)(rnd() % (u64)NP);
    long long cur = cost_sum(src, ns, (long long)1 << 60);
    time_t t0 = time(NULL);
    double T = 0.6; long long it = 0, acc = 0, nt = 0, nta = 0;
    fprintf(stderr, "start m=%d D=%d sample=%d cost=%lld PT=%.2f\n", M, D, ns, cur, PT);
    while (difftime(time(NULL), t0) < secs) {
        it++;
        int kind; int e = 0, old = 0, sv = 0, i1 = 0, i2 = 0;
        int ek1 = 0, et1 = 0, ew1 = 0, ek2 = 0, et2 = 0, ew2 = 0;
        double u = urand();
        if (u < PT) {                               /* targeted repair: a walk to an unreached state, one edge re-voltaged */
            kind = 0; nt++;
            int i0 = (nbk > 0) ? badkeep[rnd() % (u64)nbk] : src[rnd() % (u64)ns];
            if (!targeted(i0, &e, &old)) continue;
            nta++;
        } else if (u < 0.97 || M < 2) {             /* random voltage change */
            kind = 0; e = (int)(rnd() % (u64)NE); old = EW[e];
            int nv = (int)(rnd() % (u64)(M - 1)); if (nv >= old) nv++;
            EW[e] = nv;
        } else {                                    /* swap the matching targets of two point orbits */
            kind = 1; sv = D - 2 + (int)(rnd() % 2); i1 = (int)(rnd() % (u64)NP); i2 = (int)(rnd() % (u64)NP);
            if (i1 == i2) continue;
            int e1 = D * i1 + sv, e2b = D * i2 + sv;
            ek1 = EK[e1]; et1 = ET[e1]; ew1 = EW[e1]; ek2 = EK[e2b]; et2 = ET[e2b]; ew2 = EW[e2b];
            EK[e1] = ek2; ET[e1] = et2; EW[e1] = ew2; EK[e2b] = ek1; ET[e2b] = et1; EW[e2b] = ew1;
            if (!valid_orbit(i1) || !valid_orbit(i2)) {
                EK[e1] = ek1; ET[e1] = et1; EW[e1] = ew1; EK[e2b] = ek2; ET[e2b] = et2; EW[e2b] = ew2;
                continue;
            }
        }
        double thr = (double)cur - T * log(urand() + 1e-300);
        long long nc = cost_sum(src, ns, (long long)floor(thr));
        if ((double)nc <= thr && nc <= (long long)1 << 40) {
            cur = nc; acc++;
        } else {
            if (kind == 0) EW[e] = old;
            else {
                int e1 = D * i1 + sv, e2b = D * i2 + sv;
                EK[e1] = ek1; ET[e1] = et1; EW[e1] = ew1; EK[e2b] = ek2; ET[e2b] = et2; EW[e2b] = ew2;
            }
        }
        if (cur == 0) {                             /* sample clean: full check over all representatives */
            long long full = 0; int nbad = 0;
            for (int i = 0; i < NP; i++) { long long c = cost_src(i); full += c; if (c) bad_list_buf[nbad++] = i; }
            fprintf(stderr, "  sample clean at m=%d (it %lld): full COST over reps = %lld (bad reps %d) t=%.0fs\n", M, it, full, nbad, difftime(time(NULL), t0));
            if (full == 0) {
                char fn[512]; snprintf(fn, sizeof fn, "%s_m%d.txt", outp, M); write_params(fn);
                printf("FULL_OK m=%d iters=%lld secs=%.0f file=%s\n", M, it, difftime(time(NULL), t0), fn); fflush(stdout);
                if (M >= mmax) break;
                M++; FULL = (M == 64) ? ~0ULL : ((1ULL << M) - 1);
            } else {
                nbk = nbad; for (int j = 0; j < nbad; j++) badkeep[j] = bad_list_buf[j];
                int add = nbad < 8 ? nbad : 8;
                if (ns + add > nsample + 200) ns = nsample;   /* keep the sample small (the random part is kept) */
                for (int j = 0; j < add && ns < cap; j++) src[ns++] = bad_list_buf[(int)(rnd() % (u64)nbad)];
                fprintf(stderr, "  added %d bad reps (now %d)\n", add, ns);
            }
            cur = cost_sum(src, ns, (long long)1 << 60);
        }
        if (it % 100 == 0) fprintf(stderr, "it %lld m=%d cost=%lld acc=%.3f targeted %lld/%lld t=%.0fs\n", it, M, cur, (double)acc / it, nta, nt, difftime(time(NULL), t0));
    }
    printf("END m_reached_full=%d iters=%lld\n", M, it);
    return 0;
}
