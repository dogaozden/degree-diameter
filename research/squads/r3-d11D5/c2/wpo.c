/* wpo.c: clause-weighting (breakout / PAWS-style) local search on the base of a DM Z6 lift, card c2 of round r3-d11D5.
   Built from research/d11D5/plus/plusopt7.c.  total() is kept unchanged (used as a check at start).  evalw() is the same
   bit-parallel evaluation, but for each failing triple (source s, target t, coset k) it lists the index ((s*V)+t)*3+k and
   sums the weights W of the failing triples.  Weighted cost = sum of W over failing triples; true cost = their number.
   Moves (as in plusopt7's annealer): sigma swap (a, b), a a hot point (prob PH) or random, b random; flag swap
   (p1,l1),(p2,l2) -> (p1,l2),(p2,l1) with a flag at distance <= 1 from a hot vertex (prob PH).  Strict first improvement
   of the weighted cost over a random stream of candidates.  A local minimum is declared after LMAX consecutive
   non-improving candidates (sampled stand-in for "no move improves"); then W += 1 on every failing triple; every DECAY
   bumps all W > 1 drop by 1.  The true cost is tracked; the state is saved at each new low; stops at 0 (saved to OUT0).
   usage: wpo start.in   env: SECS (CPU s), SEED, PF (flag-move prob, 0.3), PH (hot prob, 0.7), LMAX (500),
          DECAY (50), WCAP (60000), OUT, OUT0 (default fail0.in), SCORE=1 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline double urand(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
int n, dg, V; int *ln, *pt; int *sig, *sinv;
uint64_t *R0, *F0, *N0;
uint64_t *C1[6], *C2[6];
int *hot, nhot; uint8_t *ishot; int *hv, nhv; uint8_t *ishv;
uint16_t *W; size_t NT; uint16_t WCAP = 60000;
int *fA, *fB; long nfA;          /* failing-triple lists: current state (fA) and candidate (fB) */
long cur_tc, cur_wc, nbump = 0; int DECAY = 50;
static void addhot(int v) { if (!ishv[v]) { ishv[v] = 1; hv[nhv++] = v; } int p = v < n ? v : sinv[v - n]; if (!ishot[p]) { ishot[p] = 1; hot[nhot++] = p; } }
static void build_hot(const int *fl, long nf) {
    for (int i = 0; i < nhot; i++) ishot[hot[i]] = 0; nhot = 0;
    for (int i = 0; i < nhv; i++) ishv[hv[i]] = 0; nhv = 0;
    for (long i = 0; i < nf; i++) { long st = fl[i] / 3; addhot((int)(st / V)); addhot((int)(st % V)); }
}
/* unchanged bit-parallel count, as in plusopt7.c */
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
            uint64_t ok0 = R0[t * 3] | C1[0][t] | C1[2][t] | C2[4][t] | C2[5][t];
            c += ns - __builtin_popcountll(ok0 & full);
            c += ns - __builtin_popcountll(R0[t * 3 + 1] & full);
            c += ns - __builtin_popcountll(R0[t * 3 + 2] & full);
        }
    }
    return c;
}
/* same evaluation; lists failing triples if rec, returns their number and the sum of their weights */
static long evalw(int rec, int *fl, long *nf, long *ws) {
    long cnt = 0, wsum = 0;
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
            uint64_t ok0 = R0[t * 3] | C1[0][t] | C1[2][t] | C2[4][t] | C2[5][t];
            uint64_t bad[3] = { ~ok0 & full, ~R0[t * 3 + 1] & full, ~R0[t * 3 + 2] & full };
            for (int k = 0; k < 3; k++) {
                uint64_t b = bad[k];
                while (b) { int j = __builtin_ctzll(b); b &= b - 1; int idx = ((s0 + j) * V + t) * 3 + k;
                    if (rec) fl[cnt] = idx; cnt++; wsum += W[idx]; }
            }
        }
    }
    *nf = cnt; *ws = wsum; return cnt;
}
static void save(const char *fn, int *L2, int *S2) { FILE *g = fopen(fn, "w"); fprintf(g, "%d %d\n", n, dg);
    for (int l = 0; l < n; l++) { for (int k = 0; k < dg; k++) fprintf(g, "%d%c", L2[l * dg + k], k == dg - 1 ? '\n' : ' '); }
    for (int i = 0; i < n; i++) fprintf(g, "%d\n", S2[i]); fclose(g); }
static int has(const int *a, int v) { for (int j = 0; j < dg; j++) if (a[j] == v) return 1; return 0; }
static void repl(int *a, int from, int to) { for (int j = 0; j < dg; j++) if (a[j] == from) { a[j] = to; return; } }
static void bump_weights(void) {
    for (long i = 0; i < nfA; i++) { int idx = fA[i]; if (W[idx] < WCAP) W[idx]++; }
    nbump++;
    if (nbump % DECAY == 0) for (size_t i = 0; i < NT; i++) if (W[i] > 1) W[i]--;
    cur_wc = 0; for (long i = 0; i < nfA; i++) cur_wc += W[fA[i]];
}
static uint16_t maxw(void) { uint16_t m = 0; for (size_t i = 0; i < NT; i++) if (W[i] > m) m = W[i]; return m; }
int main(int argc, char **argv) {
    if (getenv("SEED")) { rs ^= (uint64_t)atoll(getenv("SEED")) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 20; i++) rnd(); }
    if (argc < 2) return 1;
    FILE *f = fopen(argv[1], "r"); if (!f || fscanf(f, "%d %d", &n, &dg) != 2) return 1; V = 2 * n;
    ln = malloc(4L * n * dg); for (int i = 0; i < n * dg; i++) if (fscanf(f, "%d", &ln[i]) != 1) return 1;
    sig = malloc(4L * n); sinv = malloc(4L * n); for (int i = 0; i < n; i++) if (fscanf(f, "%d", &sig[i]) != 1) return 1; fclose(f);
    for (int i = 0; i < n; i++) sinv[sig[i]] = i;
    pt = malloc(4L * n * dg); int *fill = calloc(n, 4);
    for (int l = 0; l < n; l++) for (int k = 0; k < dg; k++) { int p = ln[l * dg + k]; if (fill[p] >= dg) { fprintf(stderr, "point degree > dg\n"); return 1; } pt[p * dg + fill[p]++] = l; }
    for (int p = 0; p < n; p++) if (fill[p] != dg) { fprintf(stderr, "point %d degree %d\n", p, fill[p]); return 1; }
    R0 = malloc(24L * V); F0 = malloc(24L * V); N0 = malloc(24L * V); for (int d = 0; d < 6; d++) { C1[d] = malloc(8L * V); C2[d] = malloc(8L * V); }
    hot = malloc(4L * n); ishot = calloc(n, 1); nhot = 0; hv = malloc(8L * n); ishv = calloc(2 * n, 1); nhv = 0;
    NT = (size_t)V * V * 3; W = malloc(2 * NT); for (size_t i = 0; i < NT; i++) W[i] = 1;
    fA = malloc(4 * NT); fB = malloc(4 * NT);
    long nf, ws; long c = total(); long c1 = evalw(1, fA, &nf, &ws); nfA = nf; cur_tc = c1; cur_wc = ws;
    build_hot(fA, nfA);
    printf("n=%d dg=%d cost=%ld (check %ld) hot points=%d hot vertices=%d\n", n, dg, c, c1, nhot, nhv); fflush(stdout);
    if (getenv("SCORE")) return 0;
    double secs = getenv("SECS") ? atof(getenv("SECS")) : 60, PF = getenv("PF") ? atof(getenv("PF")) : 0.3, PH = getenv("PH") ? atof(getenv("PH")) : 0.7;
    int LMAX = getenv("LMAX") ? atoi(getenv("LMAX")) : 500; DECAY = getenv("DECAY") ? atoi(getenv("DECAY")) : 50;
    WCAP = getenv("WCAP") ? (uint16_t)atoi(getenv("WCAP")) : 60000;
    const char *OUTF = getenv("OUT"), *OUT0 = getenv("OUT0") ? getenv("OUT0") : "fail0.in";
    long best = cur_tc, nev = 0, nacc = 0, nofail = 0; double lastp = -100;
    if (OUTF) save(OUTF, ln, sig);
    clock_t t0 = clock();
    while (1) {
        double el = (double)(clock() - t0) / CLOCKS_PER_SEC;
        if (cur_tc == 0) { printf("FAIL0 reached t=%.0f ev=%ld bumps=%ld\n", el, nev, nbump); fflush(stdout); save(OUT0, ln, sig); break; }
        if (el > secs) break;
        if (el - lastp >= 30) { lastp = el; printf("t=%.0f ev=%ld acc=%ld bumps=%ld cur_true=%ld cur_w=%ld best=%ld nfail=%ld hotp=%d maxW=%u\n",
                                                 el, nev, nacc, nbump, cur_tc, cur_wc, best, nfA, nhot, maxw()); fflush(stdout); }
        int kind, a = 0, b = 0, l1 = 0, p1 = 0, l2 = 0, p2 = 0;
        if (urand() >= PF) {   /* sigma swap */
            kind = 0; a = (nhot && urand() < PH) ? hot[rnd() % nhot] : (int)(rnd() % n); b = (int)(rnd() % n);
            if (a == b) continue;
            int la = sig[a], lb = sig[b]; sig[a] = lb; sig[b] = la; sinv[lb] = a; sinv[la] = b;
        } else {               /* flag swap, one flag within distance 1 of a hot vertex */
            kind = 1;
            if (nhv && urand() < PH) { int h = hv[rnd() % nhv];
                if (h < n) { p1 = h; l1 = pt[p1 * dg + rnd() % dg]; if (rnd() & 1) p1 = ln[l1 * dg + rnd() % dg]; }
                else { l1 = h - n; p1 = ln[l1 * dg + rnd() % dg]; if (rnd() & 1) l1 = pt[p1 * dg + rnd() % dg]; } }
            else { l1 = rnd() % n; p1 = ln[l1 * dg + rnd() % dg]; }
            l2 = rnd() % n; if (l1 == l2) continue;
            p2 = ln[l2 * dg + rnd() % dg];
            if (p1 == p2 || has(ln + l2 * dg, p1) || has(ln + l1 * dg, p2)) continue;
            repl(ln + l1 * dg, p1, p2); repl(ln + l2 * dg, p2, p1); repl(pt + p1 * dg, l1, l2); repl(pt + p2 * dg, l2, l1);
        }
        long nf2, ws2; long tc2 = evalw(1, fB, &nf2, &ws2); nev++;
        if (ws2 < cur_wc) {    /* strict improvement of the weighted cost: accept */
            int *tmp = fA; fA = fB; fB = tmp; nfA = nf2; cur_wc = ws2; cur_tc = tc2; nacc++; nofail = 0;
            build_hot(fA, nfA);
            if (cur_tc < best) { best = cur_tc; printf("NEW BEST true=%ld t=%.0f ev=%ld bumps=%ld w=%ld\n", best, el, nev, nbump, cur_wc); fflush(stdout);
                if (OUTF) save(OUTF, ln, sig); }
        } else {               /* undo */
            if (kind == 0) { int la = sig[a], lb = sig[b]; sig[a] = lb; sig[b] = la; sinv[lb] = a; sinv[la] = b; }
            else { repl(ln + l1 * dg, p2, p1); repl(ln + l2 * dg, p1, p2); repl(pt + p1 * dg, l2, l1); repl(pt + p2 * dg, l1, l2); }
            nofail++;
            if (nofail >= LMAX) { bump_weights(); nofail = 0; }   /* local minimum: breakout */
        }
    }
    printf("RESULT best=%ld cur_true=%ld ev=%ld acc=%ld bumps=%ld maxW=%u\n", best, cur_tc, nev, nacc, nbump, maxw());
    if (OUTF) printf("best state saved to %s (true cost %ld)\n", OUTF, best);
    return 0;
}
