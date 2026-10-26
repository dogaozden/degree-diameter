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
int main(int argc, char **argv) {
    if (argc < 2) return 1;
    if (getenv("SEED")) { rs ^= (uint64_t)atoll(getenv("SEED")) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 20; i++) rnd(); }
    FILE *f = fopen(argv[1], "r"); if (!f) return 1;
    if (fscanf(f, "%d %d", &n, &dg) != 2) return 1; V = 2 * n;
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
    if (getenv("DIAG")) {   /* distribution of candidate costs (flag moves near hot vertices vs sigma swaps) */
        int N = atoi(getenv("DIAG")); long *fc = malloc(8L * N), *sc = malloc(8L * N); int nf = 0, ns2 = 0;
        for (int i = 0; i < N * 20 && (nf < N || ns2 < N); i++) {
            if (nf < N && (i & 1)) { int h = hv[rnd() % nhv]; int L1, P1, L2, P2;
                if (h < n) { P1 = h; L1 = pt[P1 * dg + rnd() % dg]; if (rnd() & 1) P1 = ln[L1 * dg + rnd() % dg]; }
                else { L1 = h - n; P1 = ln[L1 * dg + rnd() % dg]; if (rnd() & 1) L1 = pt[P1 * dg + rnd() % dg]; }
                L2 = rnd() % n; P2 = ln[L2 * dg + rnd() % dg];
                if (L1 == L2 || !flag_ok(L1, P1, L2, P2)) continue;
                flag_move(L1, P1, L2, P2); collect = 0; fc[nf++] = total(); flag_move(L1, P2, L2, P1); }
            else if (ns2 < N) { int A = hot[rnd() % nhot], B = rnd() % n; if (A == B) continue;
                sig_swap(A, B); collect = 0; sc[ns2++] = total(); sig_swap(A, B); }
        }
        int cmp(const void *a, const void *b) { long x = *(const long *)a, y = *(const long *)b; return x < y ? -1 : x > y; }
        qsort(fc, nf, 8, cmp); qsort(sc, ns2, 8, cmp);
        printf("flag moves (%d): min %ld q10 %ld median %ld\n", nf, fc[0], fc[nf / 10], fc[nf / 2]);
        printf("sigma swaps (%d): min %ld q10 %ld median %ld\n", ns2, sc[0], sc[ns2 / 10], sc[ns2 / 2]);
        return 0;
    }
    double SECS = getenv("SECS") ? atof(getenv("SECS")) : 60;
    int K = getenv("K") ? atoi(getenv("K")) : 200;
    int TMIN = getenv("TMIN") ? atoi(getenv("TMIN")) : 40, TMAX = getenv("TMAX") ? atoi(getenv("TMAX")) : 120;
    double PH = getenv("PH") ? atof(getenv("PH")) : 0.7, PF = getenv("PF") ? atof(getenv("PF")) : 0.4;
    long STALL = getenv("STALL") ? atol(getenv("STALL")) : 150; int KICK = getenv("KICK") ? atoi(getenv("KICK")) : 6;
    const char *OUT = getenv("OUT"), *OUT0 = getenv("OUT0") ? getenv("OUT0") : "cost0.in";
    int *tS = calloc((size_t)n * n, 4), *tI = calloc((size_t)n * n, 4);   /* tabu expiry per (point,line) */
    int *bl = malloc(4L * n * dg), *bs = malloc(4L * n);
    memcpy(bl, ln, 4L * n * dg); memcpy(bs, sig, 4L * n);
    long best = c, cur = c, since = 0, it = 0, evals = 0; int restarts = 0;
    double t0 = now();
    if (best == 0) { save(OUT0, bl, bs); printf("COST0 at start\n"); return 0; }
    while (cur > 0) {
        double el = now() - t0; if (el > SECS) break;
        it++;
        int tt = TMIN + (int)(rnd() % (unsigned)(TMAX - TMIN + 1));
        long bestC = LONG_MAX, nt = 0; int bType = -1, bA = 0, bB = 0, bL1 = 0, bP1 = 0, bL2 = 0, bP2 = 0;
        int ncand = 0;
        for (int tries = 0; ncand < K && tries < 4 * K; tries++) {
            if (urand() >= PF) {   /* sigma swap: a biased to hot points */
                int A = (nhot && urand() < PH) ? hot[rnd() % nhot] : (int)(rnd() % n);
                int B = (int)(rnd() % n); if (A == B) continue;
                int la = sig[A], lb = sig[B];
                int tabu = tS[A * n + lb] > it || tS[B * n + la] > it;
                sig_swap(A, B); collect = 0; long c2 = total(); evals++; ncand++; sig_swap(A, B);
                if (tabu && !(c2 < best)) continue;
                if (c2 < bestC) { bestC = c2; nt = 1; bType = 0; bA = A; bB = B; }
                else if (c2 == bestC && rnd() % (unsigned)(++nt) == 0) { bType = 0; bA = A; bB = B; }
            } else {               /* flag swap, with (p1,l1) incident to or next to a hot vertex */
                int L1, P1, L2, P2;
                if (nhv && urand() < PH) { int h = hv[rnd() % nhv];
                    if (h < n) { P1 = h; L1 = pt[P1 * dg + rnd() % dg]; if (rnd() & 1) P1 = ln[L1 * dg + rnd() % dg]; }
                    else { L1 = h - n; P1 = ln[L1 * dg + rnd() % dg]; if (rnd() & 1) L1 = pt[P1 * dg + rnd() % dg]; } }
                else { L1 = rnd() % n; P1 = ln[L1 * dg + rnd() % dg]; }
                L2 = rnd() % n; if (L1 == L2) continue;
                P2 = ln[L2 * dg + rnd() % dg];
                if (!flag_ok(L1, P1, L2, P2)) continue;
                int tabu = tI[P1 * n + L2] > it || tI[P2 * n + L1] > it;
                flag_move(L1, P1, L2, P2); collect = 0; long c2 = total(); evals++; ncand++; flag_move(L1, P2, L2, P1);
                if (tabu && !(c2 < best)) continue;
                if (c2 < bestC) { bestC = c2; nt = 1; bType = 1; bL1 = L1; bP1 = P1; bL2 = L2; bP2 = P2; }
                else if (c2 == bestC && rnd() % (unsigned)(++nt) == 0) { bType = 1; bL1 = L1; bP1 = P1; bL2 = L2; bP2 = P2; }
            }
        }
        if (bType < 0) {   /* every sampled move was tabu: random sigma swap */
            int A = rnd() % n, B = rnd() % n; if (A == B) B = (A + 1) % n; bType = 0; bA = A; bB = B;
        }
        if (bType == 0) { int la = sig[bA], lb = sig[bB]; sig_swap(bA, bB);
            tS[bA * n + la] = it + tt; tS[bB * n + lb] = it + tt; }
        else { flag_move(bL1, bP1, bL2, bP2); tI[bP1 * n + bL1] = it + tt; tI[bP2 * n + bL2] = it + tt; }
        clearhot(); collect = 1; long nc = total(); collect = 0; cur = nc;
        if (bestC != LONG_MAX && nc != bestC) fprintf(stderr, "mismatch at it=%ld: %ld vs %ld\n", it, nc, bestC);
        if (cur < best) {
            best = cur; memcpy(bl, ln, 4L * n * dg); memcpy(bs, sig, 4L * n); since = 0;
            printf("t=%.1f it=%ld NEW BEST cost=%ld (ncand=%d hot=%d/%d)\n", now() - t0, it, best, ncand, nhot, nhv);
            fflush(stdout);
            if (OUT) save(OUT, bl, bs);
            if (best == 0) { save(OUT0, bl, bs); printf("COST0 reached at it=%ld\n", it); fflush(stdout); break; }
        } else since++;
        if (it % 25 == 0) { printf("t=%.0f it=%ld cur=%ld best=%ld evals=%ld restarts=%d\n", now() - t0, it, cur, best, evals, restarts);
            fflush(stdout); }
        if (since > STALL) {   /* restart from the best state with random kicks */
            memcpy(ln, bl, 4L * n * dg); memcpy(sig, bs, 4L * n); for (int i = 0; i < n; i++) sinv[sig[i]] = i;
            rebuild(); memset(tS, 0, (size_t)n * n * 4); memset(tI, 0, (size_t)n * n * 4);
            for (int k = 0; k < KICK; k++) {
                if (rnd() & 1) { int A = rnd() % n, B = rnd() % n; if (A != B) sig_swap(A, B); }
                else { int L1 = rnd() % n, P1 = ln[L1 * dg + rnd() % dg], L2 = rnd() % n, P2 = ln[L2 * dg + rnd() % dg];
                    if (L1 != L2 && flag_ok(L1, P1, L2, P2)) flag_move(L1, P1, L2, P2); }
            }
            clearhot(); collect = 1; cur = total(); collect = 0; since = 0; restarts++;
        }
    }
    printf("RESULT best=%ld it=%ld evals=%ld restarts=%d time=%.0f\n", best, it, evals, restarts, now() - t0);
    if (OUT) save(OUT, bl, bs);
    return 0;
}
