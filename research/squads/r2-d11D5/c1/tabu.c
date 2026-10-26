/* tabu.c (card c1, squad round r2-d11D5): tabu search on the BASE of a doubled-matching Z6 lift.
   total() is the cost function of research/d11D5/plus/plusopt2.c, copied; the only addition is the `collect`
   branch, which records the failing sources/targets (it does not change the returned cost).
   Each step: sample up to K candidate moves (sigma swap of two points' lines, or a degree-preserving flag swap),
   biased to the failing vertices; apply the best NON-TABU one even if it is worse (aspiration: a move that beats
   the best cost so far is always allowed).  Tabu memory: after point p leaves line la (sig[p]: la -> lb), the
   assignment sig[p] = la is forbidden for TT steps; after a flag move, the two removed incidences may not be
   re-added for TT steps.  After STALL steps without a new best, restart from the best state with KICK random moves.
   usage: ./tabu in.in
   env: SECS (wall seconds, 60), SEED, K (200), TMIN (40), TMAX (120), PH (0.7), PF (0.4), STALL (150), KICK (6),
        OUT (best state file), OUT0 (file written when cost 0 is reached, default cost0.in), SCORE=1 (print cost, exit) */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <limits.h>
#include <time.h>
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline double urand(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
int n, dg, V; int *ln, *pt; int *sig, *sinv;
uint64_t *R0, *F0, *N0;          /* jumped states: V*3 words (coset 0,1,2) */
uint64_t *C1[6], *C2[6];         /* pure walk counts per length, saturating: >=1, >=2 */
int *hot, nhot, collect = 0; uint8_t *ishot; int *hv, nhv; uint8_t *ishv;
static void addhot(int v) { if (!ishv[v]) { ishv[v] = 1; hv[nhv++] = v; } int p = v < n ? v : sinv[v - n]; if (!ishot[p]) { ishot[p] = 1; hot[nhot++] = p; } }
static void clearhot(void) { for (int i = 0; i < nhot; i++) ishot[hot[i]] = 0; nhot = 0; for (int i = 0; i < nhv; i++) ishv[hv[i]] = 0; nhv = 0; }
/* cost: copied from plusopt2.c total() (no-op lines removed; the collect branch only records failing vertices) */
static long total(void) {
    long c = 0;
    for (int s0 = 0; s0 < V; s0 += 64) {
        int ns = V - s0 < 64 ? V - s0 : 64; uint64_t full = ns == 64 ? ~0ULL : ((1ULL << ns) - 1);
        /* pure walk counts */
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
        /* jumped reachability: jumped states J[x][c]; pure states feed the first jump */
        memset(R0, 0, 24L * V); memset(F0, 0, 24L * V);
        for (int d = 1; d <= 5; d++) {
            memset(N0, 0, 24L * V);
            for (int x = 0; x < V; x++) {
                uint64_t a0 = F0[x * 3], a1 = F0[x * 3 + 1], a2 = F0[x * 3 + 2], pu = C1[d - 1][x];
                if (a0 | a1 | a2) { const int *nb = x < n ? pt + x * dg : ln + (x - n) * dg; int off = x < n ? n : 0;
                    for (int j = 0; j < dg; j++) { uint64_t *y = N0 + (nb[j] + off) * 3; y[0] |= a0; y[1] |= a1; y[2] |= a2; } }
                a0 |= pu;   /* a pure walk of length d-1 at x (coset 0) may jump now */
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
    return c;
}
static int has(const int *a, int v) { for (int j = 0; j < dg; j++) if (a[j] == v) return 1; return 0; }
static void repl(int *a, int from, int to) { for (int j = 0; j < dg; j++) if (a[j] == from) { a[j] = to; return; } }
static void sig_swap(int a, int b) { int la = sig[a], lb = sig[b]; sig[a] = lb; sig[b] = la; sinv[lb] = a; sinv[la] = b; }
/* flag move: (p1,l1),(p2,l2) -> (p1,l2),(p2,l1); undo is flag_move(l1,p2,l2,p1) */
static void flag_move(int l1, int p1, int l2, int p2) {
    repl(ln + l1 * dg, p1, p2); repl(ln + l2 * dg, p2, p1); repl(pt + p1 * dg, l1, l2); repl(pt + p2 * dg, l2, l1);
}
static int flag_ok(int l1, int p1, int l2, int p2) { return l1 != l2 && p1 != p2 && !has(ln + l2 * dg, p1) && !has(ln + l1 * dg, p2); }
static void save(const char *fn, int *L2, int *S2) { FILE *g = fopen(fn, "w"); fprintf(g, "%d %d\n", n, dg);
    for (int l = 0; l < n; l++) { for (int k = 0; k < dg; k++) fprintf(g, "%d%c", L2[l * dg + k], k == dg - 1 ? '\n' : ' '); }
    for (int i = 0; i < n; i++) fprintf(g, "%d\n", S2[i]); fclose(g); }
/* rebuild pt (point -> lines) from ln and check that every point has degree dg */
static int rebuild(void) {
    int *fill = calloc(n, 4), ok = 1;
    for (int l = 0; l < n && ok; l++) for (int k = 0; k < dg; k++) { int p = ln[l * dg + k];
        if (fill[p] >= dg) { ok = 0; break; } pt[p * dg + fill[p]++] = l; }
    for (int p = 0; p < n && ok; p++) if (fill[p] != dg) ok = 0;
    free(fill); return ok;
}
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }
static int *tS, *tI; static long best, cur, since, evals; static long it; static int ncand, nrest;
static long sC, sNt; static int sType, sA, sB, sL1, sP1, sL2, sP2;   /* best non-tabu candidate of this step */
/* sigma swap (A,B): tabu if it re-creates an assignment removed within the last tt steps (aspiration: beats best) */
static void try_sigma(int A, int B) {
    int la = sig[A], lb = sig[B];
    int tabu = tS[A * n + lb] > it || tS[B * n + la] > it;
    sig_swap(A, B); collect = 0; long c2 = total(); evals++; ncand++; sig_swap(A, B);
    if (tabu && !(c2 < best)) return;
    if (c2 < sC) { sC = c2; sNt = 1; sType = 0; sA = A; sB = B; }
    else if (c2 == sC && rnd() % (unsigned)(++sNt) == 0) { sType = 0; sA = A; sB = B; }
}
/* flag swap (p1,l1),(p2,l2) -> (p1,l2),(p2,l1): tabu if it re-adds an incidence removed within the last tt steps */
static void try_flag(int L1, int P1, int L2, int P2) {
    int tabu = tI[P1 * n + L2] > it || tI[P2 * n + L1] > it;
    flag_move(L1, P1, L2, P2); collect = 0; long c2 = total(); evals++; ncand++; flag_move(L1, P2, L2, P1);
    if (tabu && !(c2 < best)) return;
    if (c2 < sC) { sC = c2; sNt = 1; sType = 1; sL1 = L1; sP1 = P1; sL2 = L2; sP2 = P2; }
    else if (c2 == sC && rnd() % (unsigned)(++sNt) == 0) { sType = 1; sL1 = L1; sP1 = P1; sL2 = L2; sP2 = P2; }
}
/* one random flag swap with (p1,l1) incident to, or next to, a hot vertex (prob PH), else uniform */
static void sample_flag(double PH) {
    int L1, P1, L2, P2;
    if (nhv && urand() < PH) { int h = hv[rnd() % nhv];
        if (h < n) { P1 = h; L1 = pt[P1 * dg + rnd() % dg]; if (rnd() & 1) P1 = ln[L1 * dg + rnd() % dg]; }
        else { L1 = h - n; P1 = ln[L1 * dg + rnd() % dg]; if (rnd() & 1) L1 = pt[P1 * dg + rnd() % dg]; } }
    else { L1 = rnd() % n; P1 = ln[L1 * dg + rnd() % dg]; }
    L2 = rnd() % n; if (L1 == L2) return;
    P2 = ln[L2 * dg + rnd() % dg];
    if (flag_ok(L1, P1, L2, P2)) try_flag(L1, P1, L2, P2);
}
int main(int argc, char **argv) {
    if (argc < 2) return 1;
    if (getenv("SEED")) { rs ^= (uint64_t)atoll(getenv("SEED")) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 20; i++) rnd(); }
    FILE *f = fopen(argv[1], "r"); if (!f) return 1;
    if (fscanf(f, "%d %d", &n, &dg) != 2) return 1;
    V = 2 * n;
    ln = malloc(4L * n * dg); for (int i = 0; i < n * dg; i++) if (fscanf(f, "%d", &ln[i]) != 1) return 1;
    sig = malloc(4L * n); sinv = malloc(4L * n); for (int i = 0; i < n; i++) if (fscanf(f, "%d", &sig[i]) != 1) return 1;
    fclose(f);
    for (int i = 0; i < n; i++) sinv[sig[i]] = i;
    pt = malloc(4L * n * dg); if (!rebuild()) { fprintf(stderr, "input is not a dg-regular incidence\n"); return 1; }
    R0 = malloc(24L * V); F0 = malloc(24L * V); N0 = malloc(24L * V);
    for (int d = 0; d < 6; d++) { C1[d] = malloc(8L * V); C2[d] = malloc(8L * V); }
    hot = malloc(4L * n); ishot = calloc(n, 1); hv = malloc(4L * V); ishv = calloc(V, 1); nhot = nhv = 0;
    collect = 1; long c = total(); collect = 0;
    printf("n=%d dg=%d cost=%ld hot points=%d hot vertices=%d\n", n, dg, c, nhot, nhv); fflush(stdout);
    if (getenv("SCORE")) return 0;
    double SECS = getenv("SECS") ? atof(getenv("SECS")) : 60;
    int EXH = getenv("EXH") ? atoi(getenv("EXH")) : 1;      /* 1: all sigma swaps (a in hot points, b any point) */
    int HMAX = getenv("HMAX") ? atoi(getenv("HMAX")) : 4;   /* at most HMAX hot points (random subset) per step */
    int K = getenv("K") ? atoi(getenv("K")) : 200;          /* EXH=0: sampled candidates per step */
    int KF = getenv("KF") ? atoi(getenv("KF")) : 0;         /* extra sampled flag swaps per step */
    int TMIN = getenv("TMIN") ? atoi(getenv("TMIN")) : 8, TMAX = getenv("TMAX") ? atoi(getenv("TMAX")) : 24;
    double PH = getenv("PH") ? atof(getenv("PH")) : 0.9, PF = getenv("PF") ? atof(getenv("PF")) : 0.0;
    long STALL = getenv("STALL") ? atol(getenv("STALL")) : 60; int KICK = getenv("KICK") ? atoi(getenv("KICK")) : 3;
    const char *OUT = getenv("OUT"), *OUT0 = getenv("OUT0") ? getenv("OUT0") : "cost0.in";
    tS = calloc((size_t)n * n, 4); tI = calloc((size_t)n * n, 4);   /* tabu expiry step per (point, line) */
    int *bl = malloc(4L * n * dg), *bs = malloc(4L * n), *cp = malloc(4L * n);
    memcpy(bl, ln, 4L * n * dg); memcpy(bs, sig, 4L * n);
    best = c; cur = c; since = 0; it = 0; evals = 0; nrest = 0;
    double t0 = now();
    if (best == 0) { save(OUT0, bl, bs); printf("COST0 at start\n"); return 0; }
    while (cur > 0) {
        double el = now() - t0; if (el > SECS) break;
        it++;
        int tt = TMIN + (int)(rnd() % (unsigned)(TMAX - TMIN + 1));
        sC = LONG_MAX; sNt = 0; sType = -1; ncand = 0;
        if (EXH) {   /* every sigma swap with a in a (random subset of the) hot points */
            int nh = nhot < HMAX ? nhot : HMAX; memcpy(cp, hot, 4L * nhot);
            for (int i = 0; i < nh; i++) { int j = i + (int)(rnd() % (unsigned)(nhot - i)); int tmp = cp[i]; cp[i] = cp[j]; cp[j] = tmp; }
            for (int i = 0; i < nh; i++) for (int B = 0; B < n; B++) if (B != cp[i]) try_sigma(cp[i], B);
        } else {
            for (int tries = 0; ncand < K && tries < 4 * K; tries++) {
                if (urand() < PF) sample_flag(PH);
                else { int A = (nhot && urand() < PH) ? hot[rnd() % nhot] : (int)(rnd() % n); int B = (int)(rnd() % n); if (A != B) try_sigma(A, B); }
            }
        }
        for (int k = 0; k < KF; k++) sample_flag(PH);
        if (sType < 0) {   /* nothing admissible: random sigma swap */
            int A = rnd() % n, B = rnd() % n; if (A == B) B = (A + 1) % n; sType = 0; sA = A; sB = B; }
        if (sType == 0) { int la = sig[sA], lb = sig[sB]; sig_swap(sA, sB); tS[sA * n + la] = it + tt; tS[sB * n + lb] = it + tt; }
        else { flag_move(sL1, sP1, sL2, sP2); tI[sP1 * n + sL1] = it + tt; tI[sP2 * n + sL2] = it + tt; }
        clearhot(); collect = 1; cur = total(); collect = 0;
        if (sC != LONG_MAX && cur != sC) fprintf(stderr, "mismatch at it=%ld: %ld vs %ld\n", it, cur, sC);
        if (cur < best) {
            best = cur; memcpy(bl, ln, 4L * n * dg); memcpy(bs, sig, 4L * n); since = 0;
            printf("t=%.1f it=%ld NEW BEST cost=%ld (cands=%d hot=%d/%d)\n", now() - t0, it, best, ncand, nhot, nhv);
            fflush(stdout);
            if (OUT) save(OUT, bl, bs);
            if (best == 0) { save(OUT0, bl, bs); printf("COST0 reached at it=%ld\n", it); fflush(stdout); break; }
        } else since++;
        if (it % 10 == 0) { printf("t=%.0f it=%ld cur=%ld best=%ld evals=%ld restarts=%d hot=%d/%d\n", now() - t0, it, cur, best, evals, nrest, nhot, nhv);
            fflush(stdout); }
        if (since > STALL) {   /* restart from the best state with random kicks; tabu memory cleared */
            memcpy(ln, bl, 4L * n * dg); memcpy(sig, bs, 4L * n); for (int i = 0; i < n; i++) sinv[sig[i]] = i;
            rebuild(); memset(tS, 0, (size_t)n * n * 4); memset(tI, 0, (size_t)n * n * 4);
            for (int k = 0; k < KICK; k++) { int A = rnd() % n, B = rnd() % n; if (A != B) sig_swap(A, B); }
            clearhot(); collect = 1; cur = total(); collect = 0; since = 0; nrest++;
        }
    }
    printf("RESULT best=%ld it=%ld evals=%ld restarts=%d time=%.0f\n", best, it, evals, nrest, now() - t0);
    if (OUT) save(OUT, bl, bs);
    return 0;
}
