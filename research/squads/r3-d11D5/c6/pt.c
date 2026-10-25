/* pt.c (card c6): parallel tempering with crossover for the DM-base structural cost.
   Derived from research/d11D5/plus/plusopt7.c: same total() (exact structural cost, copied verbatim apart from
   the removed MU/demand terms, which are 0 in the scorer). K replicas, each a full state (ln, pt, sig, sinv, hot
   lists). total() reads global pointers; bind(R) points them at replica R, so no copying is needed.
   Temperatures are geometric from TMIN to TMAX over the K slots; slots hold replicas, and a swap exchanges the
   replicas of two adjacent slots (accept min(1, exp((c_i-c_j)(1/T_i-1/T_j)))).
   Moves per replica: sigma swap (prob 1-PF), degree-preserving flag swap (prob PF), Metropolis at the slot's T.
   Every SW global moves: one round of adjacent swap attempts (even/odd pairs alternate), then the crossover round:
   two replicas with identical line lists (same base) exchange sigma on the hot points of one of them (repair by
   swaps), accepted by Metropolis at the receiving slot's T.
   usage: SECS=840 SEED=1 PF=0.3 PH=0.7 SW=200 XP=0.5 TMIN=0.3 TMAX=6 OUT=best.in OUT0=zero.in ./pt s1.in ... s6.in
          SCORE=1 ./pt s1.in ...  (prints the structural cost of each start and exits) */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>
#include <limits.h>

#define MAXR 8
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline double urand(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

int n, dg, V;
int *ln, *pt, *sig, *sinv;                 /* currently bound replica */
uint64_t *R0, *F0, *N0;
uint64_t *C1[6], *C2[6];
int *hot, nhot, collect = 0; uint8_t *ishot; int *hv, nhv; uint8_t *ishv;
long lastfail;

static void addhot(int v) { if (!ishv[v]) { ishv[v] = 1; hv[nhv++] = v; } int p = v < n ? v : sinv[v - n]; if (!ishot[p]) { ishot[p] = 1; hot[nhot++] = p; } }

/* exact structural cost (same algorithm as plusopt7.c total() with MU = 0) */
static long total(void) {
    long c = 0;
    for (int s0 = 0; s0 < V; s0 += 64) {
        int ns = V - s0 < 64 ? V - s0 : 64; uint64_t full = ns == 64 ? ~0ULL : ((1ULL << ns) - 1);
        memset(C1[0], 0, 8L * V); memset(C2[0], 0, 8L * V);
        for (int k = 0; k < ns; k++) C1[0][s0 + k] |= 1ULL << k;
        for (int d = 1; d <= 5; d++) {
            uint64_t *a1 = C1[d], *a2 = C2[d], *b1 = C1[d - 1], *b2 = C2[d - 1];
            for (int x = 0; x < V; x++) {
                const int *nb = x < n ? pt + x * dg : ln + (x - n) * dg; int off = x < n ? n : 0;
                uint64_t s1 = 0, s2 = 0;
                for (int j = 0; j < dg; j++) { int y = nb[j] + off; s2 |= b2[y] | (s1 & b1[y]); s1 |= b1[y]; }
                a1[x] = s1; a2[x] = s2;
            }
        }
        memset(R0, 0, 24L * V); memset(F0, 0, 24L * V);
        for (int d = 1; d <= 5; d++) {
            memset(N0, 0, 24L * V);
            for (int x = 0; x < V; x++) {
                uint64_t a0 = F0[x * 3], a1 = F0[x * 3 + 1], a2 = F0[x * 3 + 2], pu = C1[d - 1][x];
                if (a0 | a1 | a2) { const int *nb = x < n ? pt + x * dg : ln + (x - n) * dg; int off = x < n ? n : 0;
                    for (int j = 0; j < dg; j++) { uint64_t *y = N0 + (nb[j] + off) * 3; y[0] |= a0; y[1] |= a1; y[2] |= a2; } }
                a0 |= pu;
                if (x < n) { uint64_t *y = N0 + (n + sig[x]) * 3; y[1] |= a0; y[2] |= a1; y[0] |= a2; }
                else { uint64_t *y = N0 + sinv[x - n] * 3; y[2] |= a0; y[0] |= a1; y[1] |= a2; }
            }
            for (int i = 0; i < 3 * V; i++) R0[i] |= N0[i];
            uint64_t *t = F0; F0 = N0; N0 = t;
        }
        for (int t = 0; t < V; t++) {
            uint64_t ok0 = R0[t * 3];
            ok0 |= C1[0][t] | C1[2][t] | C2[4][t] | C2[5][t];
            c += ns - __builtin_popcountll(ok0 & full);
            c += ns - __builtin_popcountll(R0[t * 3 + 1] & full);
            c += ns - __builtin_popcountll(R0[t * 3 + 2] & full);
            if (collect) { uint64_t bad = (~ok0 | ~R0[t * 3 + 1] | ~R0[t * 3 + 2]) & full;
                while (bad) { int k = __builtin_ctzll(bad); bad &= bad - 1; addhot(s0 + k); addhot(t); } }
        }
    }
    lastfail = c;
    return c;
}

static int has(const int *a, int v) { for (int j = 0; j < dg; j++) if (a[j] == v) return 1; return 0; }
static void repl(int *a, int from, int to) { for (int j = 0; j < dg; j++) if (a[j] == from) { a[j] = to; return; } }

typedef struct { int *ln, *pt, *sig, *sinv, *hot, *hv; uint8_t *ishot, *ishv; int nhot, nhv; long c; int since; long acc, tries; } Rep;
static Rep rep[MAXR];
static Rep *slot[MAXR]; static double Tk[MAXR];
static int K = 6, REFRESH = 256;
static double PF = 0.3, PH = 0.7, XP = 0.5;
static long SW = 200, G_total = 0, nextswap = 200; static int swapround = 0;
static long swtry[MAXR], swacc[MAXR], xelig = 0, xtry = 0, xacc = 0;
static double secs = 840, t0;
static long gbest = LONG_MAX; static int *gbl, *gbs;
static const char *OUTF = NULL, *OUT0F = NULL;

static double now(void) { struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts); return ts.tv_sec + 1e-9 * ts.tv_nsec; }

static void bind(Rep *R) { ln = R->ln; pt = R->pt; sig = R->sig; sinv = R->sinv; hot = R->hot; hv = R->hv;
    ishot = R->ishot; ishv = R->ishv; nhot = R->nhot; nhv = R->nhv; }
static void unbind(Rep *R) { R->nhot = nhot; R->nhv = nhv; }

static void save(const char *fn, const int *L2, const int *S2) {
    FILE *g = fopen(fn, "w"); if (!g) return; fprintf(g, "%d %d\n", n, dg);
    for (int l = 0; l < n; l++) for (int k = 0; k < dg; k++) fprintf(g, "%d%c", L2[l * dg + k], k == dg - 1 ? '\n' : ' ');
    for (int i = 0; i < n; i++) fprintf(g, "%d\n", S2[i]); fclose(g);
}

static int slot_of(Rep *R) { for (int k = 0; k < K; k++) if (slot[k] == R) return k; return -1; }

static void finish0(Rep *R, const char *why) {
    printf("FAIL0 reached (%s) by replica %d at G=%ld t=%.1f\n", why, (int)(R - rep), G_total, now() - t0); fflush(stdout);
    save(OUT0F ? OUT0F : "c6_zero.in", R->ln, R->sig);
    exit(0);
}

static void note(Rep *R, const char *why) {
    if (R->c < gbest) {
        gbest = R->c; memcpy(gbl, R->ln, 4L * n * dg); memcpy(gbs, R->sig, 4L * n);
        int k = slot_of(R);
        printf("t=%.1f G=%ld best=%ld (%s) slot=%d T=%.2f\n", now() - t0, G_total, gbest, why, k, k >= 0 ? Tk[k] : -1.0);
        fflush(stdout);
        if (OUTF) save(OUTF, gbl, gbs);
    }
    if (R->c == 0) finish0(R, why);
}

static void refresh(Rep *R) {
    bind(R);
    for (int i = 0; i < nhot; i++) ishot[hot[i]] = 0; nhot = 0;
    for (int i = 0; i < nhv; i++) ishv[hv[i]] = 0; nhv = 0;
    collect = 1; R->c = total(); collect = 0;
    unbind(R); R->since = 0;
}

/* one Metropolis move of replica R at temperature T; keeps the new state if accepted */
static void step(Rep *R, double T) {
    bind(R);
    long c = R->c, c2;
    R->tries++;
    if (urand() >= PF) {
        int a = (nhot && urand() < PH) ? hot[rnd() % nhot] : (int)(rnd() % n);
        int b = (int)(rnd() % n);
        if (a != b) {
            int la = sig[a], lb = sig[b]; sig[a] = lb; sig[b] = la; sinv[lb] = a; sinv[la] = b;
            c2 = total();
            if (c2 <= c || urand() < exp((double)(c - c2) / T)) { R->c = c2; R->acc++; }
            else { sig[a] = la; sig[b] = lb; sinv[la] = a; sinv[lb] = b; }
        }
    } else {
        int l1, p1;
        if (nhv && urand() < PH) { int h = hv[rnd() % nhv];
            if (h < n) { p1 = h; l1 = pt[p1 * dg + rnd() % dg]; if (rnd() & 1) p1 = ln[l1 * dg + rnd() % dg]; }
            else { l1 = h - n; p1 = ln[l1 * dg + rnd() % dg]; if (rnd() & 1) l1 = pt[p1 * dg + rnd() % dg]; } }
        else { l1 = (int)(rnd() % n); p1 = ln[l1 * dg + rnd() % dg]; }
        int l2 = (int)(rnd() % n);
        if (l1 != l2) {
            int p2 = ln[l2 * dg + rnd() % dg];
            if (!(p1 == p2 || has(ln + l2 * dg, p1) || has(ln + l1 * dg, p2))) {
                repl(ln + l1 * dg, p1, p2); repl(ln + l2 * dg, p2, p1); repl(pt + p1 * dg, l1, l2); repl(pt + p2 * dg, l2, l1);
                c2 = total();
                if (c2 <= c || urand() < exp((double)(c - c2) / T)) { R->c = c2; R->acc++; }
                else { repl(ln + l1 * dg, p2, p1); repl(ln + l2 * dg, p1, p2); repl(pt + p1 * dg, l2, l1); repl(pt + p2 * dg, l1, l2); }
            }
        }
    }
    unbind(R);
}

/* crossover: copy A's sigma on A's hot points into B (repairing the bijection by swaps), Metropolis at B's slot */
static void cross(Rep *A, Rep *B) {
    xtry++;
    refresh(A);
    int nH = A->nhot; int *H = malloc(4L * (nH > 0 ? nH : 1)); memcpy(H, A->hot, 4L * nH);
    int *sg = malloc(4L * n), *si = malloc(4L * n); memcpy(sg, B->sig, 4L * n); memcpy(si, B->sinv, 4L * n);
    long cB = B->c;
    for (int i = 0; i < nH; i++) { int p = H[i]; int L = A->sig[p]; if (B->sig[p] == L) continue;
        int q = B->sinv[L], Lold = B->sig[p];
        B->sig[p] = L; B->sinv[L] = p; B->sig[q] = Lold; B->sinv[Lold] = q; }
    bind(B); long c2 = total(); unbind(B);
    int k = slot_of(B); double TB = k >= 0 ? Tk[k] : 1.0;
    if (c2 <= cB || urand() < exp((double)(cB - c2) / TB)) { B->c = c2; xacc++; refresh(B); note(B, "cross"); }
    else { memcpy(B->sig, sg, 4L * n); memcpy(B->sinv, si, 4L * n); }
    free(H); free(sg); free(si);
}

/* at most one crossover per round: a random ordered pair with identical base, taken with probability XP */
static void crossover_round(void) {
    int pi[MAXR * MAXR], pj[MAXR * MAXR], ne = 0;
    for (int i = 0; i < K; i++) for (int j = 0; j < K; j++) {
        if (i == j) continue;
        if (memcmp(rep[i].ln, rep[j].ln, 4L * n * dg)) continue;
        pi[ne] = i; pj[ne] = j; ne++;
    }
    if (!ne) return;
    xelig += ne;
    if (urand() < XP) { int q = (int)(rnd() % ne); cross(&rep[pi[q]], &rep[pj[q]]); }
}

static void swap_round(void) {
    int par = swapround++ & 1;
    for (int k = par; k + 1 < K; k += 2) {
        Rep *A = slot[k], *B = slot[k + 1];
        double a = (double)(A->c - B->c) * (1.0 / Tk[k] - 1.0 / Tk[k + 1]);
        swtry[k]++;
        if (a >= 0 || urand() < exp(a)) { slot[k] = B; slot[k + 1] = A; swacc[k]++; }
    }
}

static void status(void) {
    printf("status t=%.0f G=%ld slots:", now() - t0, G_total);
    for (int k = 0; k < K; k++) printf(" [T=%.2f c=%ld acc=%.3f]", Tk[k], slot[k]->c, slot[k]->tries ? (double)slot[k]->acc / slot[k]->tries : 0.0);
    printf(" swaps:"); for (int k = 0; k + 1 < K; k++) printf(" %.2f", swtry[k] ? (double)swacc[k] / swtry[k] : 0.0);
    printf(" cross elig=%ld tried=%ld acc=%ld best=%ld\n", xelig, xtry, xacc, gbest); fflush(stdout);
}

static void load(const char *fn, Rep *R) {
    FILE *f = fopen(fn, "r"); if (!f) { fprintf(stderr, "cannot open %s\n", fn); exit(1); }
    int nn, dd; if (fscanf(f, "%d %d", &nn, &dd) != 2 || nn != n || dd != dg) { fprintf(stderr, "bad header in %s\n", fn); exit(1); }
    for (int i = 0; i < n * dg; i++) if (fscanf(f, "%d", &R->ln[i]) != 1) { fprintf(stderr, "short file %s\n", fn); exit(1); }
    for (int i = 0; i < n; i++) if (fscanf(f, "%d", &R->sig[i]) != 1) { fprintf(stderr, "short file %s\n", fn); exit(1); }
    fclose(f);
    for (int i = 0; i < n; i++) R->sinv[R->sig[i]] = i;
    int *fill = calloc(n, 4);
    for (int l = 0; l < n; l++) for (int k = 0; k < dg; k++) { int p = R->ln[l * dg + k]; if (fill[p] >= dg) { fprintf(stderr, "point degree > dg in %s\n", fn); exit(1); } R->pt[p * dg + fill[p]++] = l; }
    for (int p = 0; p < n; p++) if (fill[p] != dg) { fprintf(stderr, "point %d degree %d in %s\n", p, fill[p], fn); exit(1); }
    free(fill);
}

int main(int argc, char **argv) {
    if (argc < 2) { fprintf(stderr, "usage: pt start1.in [start2.in ...]\n"); return 1; }
    if (getenv("SEED")) { rs ^= (uint64_t)atoll(getenv("SEED")) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 20; i++) rnd(); }
    if (getenv("SECS")) secs = atof(getenv("SECS"));
    if (getenv("PF")) PF = atof(getenv("PF"));
    if (getenv("PH")) PH = atof(getenv("PH"));
    if (getenv("XP")) XP = atof(getenv("XP"));
    if (getenv("SW")) SW = atol(getenv("SW"));
    if (getenv("K")) K = atoi(getenv("K"));
    if (K > MAXR) K = MAXR;
    double TMIN = getenv("TMIN") ? atof(getenv("TMIN")) : 0.3, TMAX = getenv("TMAX") ? atof(getenv("TMAX")) : 6.0;
    OUTF = getenv("OUT"); OUT0F = getenv("OUT0");
    int nf = argc - 1;
    FILE *f = fopen(argv[1], "r"); if (!f || fscanf(f, "%d %d", &n, &dg) != 2) { fprintf(stderr, "bad start %s\n", argv[1]); return 1; }
    fclose(f); V = 2 * n;
    R0 = malloc(24L * V); F0 = malloc(24L * V); N0 = malloc(24L * V);
    for (int d = 0; d < 6; d++) { C1[d] = malloc(8L * V); C2[d] = malloc(8L * V); }
    gbl = malloc(4L * n * dg); gbs = malloc(4L * n);
    for (int r = 0; r < K; r++) {
        Rep *R = &rep[r];
        R->ln = malloc(4L * n * dg); R->pt = malloc(4L * n * dg); R->sig = malloc(4L * n); R->sinv = malloc(4L * n);
        R->hot = malloc(4L * n); R->ishot = calloc(n, 1); R->hv = malloc(8L * n); R->ishv = calloc(2 * n, 1);
        R->nhot = R->nhv = 0; R->acc = R->tries = 0; R->since = 0;
        load(argv[1 + (r < nf ? r : nf - 1)], R);
        refresh(R);
    }
    int shared = 1;
    for (int r = 1; r < K; r++) if (memcmp(rep[r].ln, rep[0].ln, 4L * n * dg)) shared = 0;
    printf("n=%d dg=%d K=%d files=%d shared_base=%d\n", n, dg, K, nf, shared);
    for (int r = 0; r < K; r++) printf("  replica %d start %s cost=%ld\n", r, argv[1 + (r < nf ? r : nf - 1)], rep[r].c);
    fflush(stdout);
    if (getenv("SCORE")) return 0;
    /* slots: coldest slot gets the lowest-cost replica */
    for (int r = 0; r < K; r++) slot[r] = &rep[r];
    for (int i = 1; i < K; i++) for (int j = i; j > 0 && slot[j]->c < slot[j - 1]->c; j--) { Rep *t = slot[j]; slot[j] = slot[j - 1]; slot[j - 1] = t; }
    for (int k = 0; k < K; k++) Tk[k] = K > 1 ? TMIN * pow(TMAX / TMIN, (double)k / (K - 1)) : TMIN;
    for (int r = 0; r < K; r++) note(&rep[r], "start");
    t0 = now(); double lastst = 0;
    nextswap = SW;
    while (1) {
        double el = now() - t0; if (el > secs) break;
        for (int k = 0; k < K; k++) {
            Rep *R = slot[k];
            step(R, Tk[k]); G_total++;
            if (++R->since >= REFRESH) refresh(R);
            note(R, "move");
        }
        if (G_total >= nextswap) {
            nextswap += SW;
            swap_round();
            crossover_round();
        }
        if (el - lastst > 60) { lastst = el; status(); }
    }
    status();
    printf("RESULT best=%ld G=%ld t=%.1f\n", gbest, G_total, now() - t0);
    if (OUTF) save(OUTF, gbl, gbs);
    return 0;
}
