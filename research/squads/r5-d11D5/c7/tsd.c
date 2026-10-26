/* c7 tsd.c (squad round r5-d11D5, card c7): targeted steepest descent with a tabu list for the doubled-matching base.
   Built from a copy of research/d11D5/plus/plusopt7.c: the RNG, the globals and total() are copied verbatim
   (cost = number of failing (source, target, coset) triples, 0 is the target; MU stays 0).
   One step:
    1. hot points / hot vertices of the current state (total() with collect=1);
    2. candidates: sigma swaps (a,b), a a hot point (the sigma-preimage of a hot line is a hot point already), b any
       point (a pair with both ends hot is listed once); flag swaps (p1,l1)-(p2,l2) with (p1,l1) at distance <= 1
       from a hot vertex (probability PH, as in plusopt7), l2 random.  A uniform random subset of at most CAPS sigma and
       CAPF flag candidates, in random order;
    3. every candidate is evaluated exactly with total();
    4. move: best improving move (min cost; ties: fewest sigma values differing from the start file); if none
       improves, the best non-tabu plateau move (cost unchanged, same tie-break); if none, the least-worsening non-tabu
       move; only if every candidate is tabu, the least-worsening tabu move.  Improving moves ignore the tabu list.
    5. tabu: an accepted move forbids re-creating the attributes it removed for TEN steps: the sigma value (p -> l)
       or the flag (p,l).
   Stops at cost 0 (OUT0 written) or after SECS of wall time.  OUT is rewritten whenever the best cost improves.
   usage: tsd in.txt     env: SECS (wall s, 600), SEED, CAPS (2000), CAPF (1000), TEN (50), PH (0.7), OUT, OUT0, SCORE=1
   build: gcc -O3 -march=native -o tsd tsd.c -lm */
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
uint64_t *R0, *F0, *N0;          /* jumped states: V*3 words (coset 0,1,2) */
uint64_t *C1[6], *C2[6];         /* pure walk counts per length, saturating: >=1, >=2 */
int *hot, nhot, collect = 0; uint8_t *ishot; int *hv, nhv; uint8_t *ishv;
static void addhot(int v) { if (!ishv[v]) { ishv[v] = 1; hv[nhv++] = v; } int p = v < n ? v : sinv[v - n]; if (!ishot[p]) { ishot[p] = 1; hot[nhot++] = p; } }
double MU = 0; long demands, lastfail;
static long total(void) {
    long c = 0; demands = 0;
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
            int same = (t < n) == (s0 < n);   /* batches never straddle sides only if n % 64 == 0; handle per bit below */
            (void)same;
            /* same-side bits: walks of even length; opposite-side: odd.  Pure ok: length<=2 reach, or >=2 walks of length 4 (same)
               or >=2 walks of length 5 (opposite); counts of the wrong parity are 0 automatically (bipartite). */
            if (MU > 0) { uint64_t mpts = s0 >= n ? 0 : (s0 + 64 <= n ? ~0ULL : ((1ULL << (n - s0)) - 1)); uint64_t same = (t < n ? mpts : ~mpts) & full;
                demands += __builtin_popcountll(~(C1[0][t] | C1[2][t] | C2[4][t]) & same); }
            ok0 |= C1[0][t] | C1[2][t] | C2[4][t] | C2[5][t];
            c += ns - __builtin_popcountll(ok0 & full);
            c += ns - __builtin_popcountll(R0[t * 3 + 1] & full);
            c += ns - __builtin_popcountll(R0[t * 3 + 2] & full);
            if (collect) { uint64_t bad = (~ok0 | ~R0[t * 3 + 1] | ~R0[t * 3 + 2]) & full;
                while (bad) { int k = __builtin_ctzll(bad); bad &= bad - 1; addhot(s0 + k); addhot(t); } }
        }
    }
    lastfail = c;
    if (MU > 0) return 10 * c + (long)(MU * 10 * demands);
    return c;
}
static int has(const int *a, int v) { for (int j = 0; j < dg; j++) if (a[j] == v) return 1; return 0; }
static void repl(int *a, int from, int to) { for (int j = 0; j < dg; j++) if (a[j] == from) { a[j] = to; return; } }
static void save(const char *fn, int *L2, int *S2) { FILE *g = fopen(fn, "w"); fprintf(g, "%d %d\n", n, dg);
    for (int l = 0; l < n; l++) { for (int k = 0; k < dg; k++) fprintf(g, "%d%c", L2[l * dg + k], k == dg - 1 ? '\n' : ' '); }
    for (int i = 0; i < n; i++) fprintf(g, "%d\n", S2[i]); fclose(g); }
static double now(void) { struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts); return ts.tv_sec + 1e-9 * ts.tv_nsec; }

typedef struct { int type, a, b, c, d; } cand;   /* type 0: sigma swap a<->b; type 1: flag (p1,l1)=(a,b), (p2,l2)=(c,d) */
static int *S0, *tabuS, *tabuF;                  /* start sigma; tabu expiry per (point, line) */
static int ndiff = 0;                            /* number of sigma values differing from the start file */
static void sw(int a, int b) { int la = sig[a], lb = sig[b]; sig[a] = lb; sig[b] = la; sinv[lb] = a; sinv[la] = b; }
/* (p1,l1),(p2,l2) -> (p1,l2),(p2,l1); the inverse is fl(p2,l1,p1,l2) */
static void fl(int p1, int l1, int p2, int l2) { repl(ln + l1 * dg, p1, p2); repl(ln + l2 * dg, p2, p1); repl(pt + p1 * dg, l1, l2); repl(pt + p2 * dg, l2, l1); }
static void cand_apply(cand *q) { if (q->type == 0) sw(q->a, q->b); else fl(q->a, q->b, q->c, q->d); }
static void cand_undo(cand *q) { if (q->type == 0) sw(q->a, q->b); else fl(q->c, q->b, q->a, q->d); }
static int cand_tabu(const cand *q, long step) {
    if (q->type == 0) { int la = sig[q->a], lb = sig[q->b]; return tabuS[q->a * n + lb] > step || tabuS[q->b * n + la] > step; }
    return tabuF[q->a * n + q->d] > step || tabuF[q->c * n + q->b] > step; }
static int ndiff_after(const cand *q) { int a = q->a, b = q->b, la = sig[a], lb = sig[b];
    return ndiff - (la != S0[a]) - (lb != S0[b]) + (lb != S0[a]) + (la != S0[b]); }
static long eval_hot(void) {   /* cost of the current state; also refreshes the hot points and hot vertices */
    for (int i = 0; i < nhot; i++) ishot[hot[i]] = 0; nhot = 0;
    for (int i = 0; i < nhv; i++) ishv[hv[i]] = 0; nhv = 0;
    collect = 1; long c = total(); collect = 0; return c; }

int main(int argc, char **argv) {
    if (argc < 2) { fprintf(stderr, "usage: tsd in.txt\n"); return 1; }
    if (getenv("SEED")) { rs ^= (uint64_t)atoll(getenv("SEED")) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 20; i++) rnd(); }
    FILE *f = fopen(argv[1], "r"); if (!f || fscanf(f, "%d %d", &n, &dg) != 2) return 1; V = 2 * n;
    ln = malloc(4L * n * dg); for (int i = 0; i < n * dg; i++) if (fscanf(f, "%d", &ln[i]) != 1) return 1;
    sig = malloc(4L * n); sinv = malloc(4L * n); for (int i = 0; i < n; i++) if (fscanf(f, "%d", &sig[i]) != 1) return 1; fclose(f);
    for (int i = 0; i < n; i++) sinv[sig[i]] = i;
    pt = malloc(4L * n * dg); int *fill = calloc(n, 4);
    for (int l = 0; l < n; l++) for (int k = 0; k < dg; k++) { int p = ln[l * dg + k]; if (fill[p] >= dg) { fprintf(stderr, "point degree > dg\n"); return 1; } pt[p * dg + fill[p]++] = l; }
    for (int p = 0; p < n; p++) if (fill[p] != dg) { fprintf(stderr, "point %d degree %d\n", p, fill[p]); return 1; }
    R0 = malloc(24L * V); F0 = malloc(24L * V); N0 = malloc(24L * V);
    for (int d = 0; d < 6; d++) { C1[d] = malloc(8L * V); C2[d] = malloc(8L * V); }
    hot = malloc(4L * n); ishot = calloc(n, 1); nhot = 0; hv = malloc(8L * n); ishv = calloc(2 * n, 1); nhv = 0;
    S0 = malloc(4L * n); memcpy(S0, sig, 4L * n);
    tabuS = calloc((size_t)n * n, sizeof(int)); tabuF = calloc((size_t)n * n, sizeof(int));
    double SECS = getenv("SECS") ? atof(getenv("SECS")) : 600, PH = getenv("PH") ? atof(getenv("PH")) : 0.7;
    int CAPS = getenv("CAPS") ? atoi(getenv("CAPS")) : 2000, CAPF = getenv("CAPF") ? atoi(getenv("CAPF")) : 1000;
    long TEN = getenv("TEN") ? atol(getenv("TEN")) : 50;
    const char *OUTF = getenv("OUT") ? getenv("OUT") : "tsd_best.in", *OUT0F = getenv("OUT0") ? getenv("OUT0") : "tsd_fail0.in";

    long c = eval_hot();
    printf("n=%d dg=%d cost=%ld hot points=%d hot vertices=%d\n", n, dg, c, nhot, nhv); fflush(stdout);
    if (getenv("SCORE")) return 0;
    if (c == 0) { save(OUT0F, ln, sig); printf("cost 0 at start\n"); return 0; }
    long best = c; int bestnd = 0;
    int *bl = malloc(4L * n * dg), *bs = malloc(4L * n); memcpy(bl, ln, 4L * n * dg); memcpy(bs, sig, 4L * n);
    size_t cap = (size_t)n * n + (size_t)CAPF + 16; cand *C = malloc(sizeof(cand) * cap);
    double t0 = now(); long step = 0;
    while (c > 0) {
        if (now() - t0 > SECS) break;
        step++;
        /* 2. candidates */
        int nc = 0;
        for (int i = 0; i < nhot; i++) { int a = hot[i];
            for (int b = 0; b < n; b++) { if (b == a || (ishot[b] && b < a)) continue; C[nc].type = 0; C[nc].a = a; C[nc].b = b; nc++; } }
        int ns = nc < CAPS ? nc : CAPS;
        for (int i = 0; i < ns; i++) { int j = i + (int)(rnd() % (uint64_t)(nc - i)); cand t = C[i]; C[i] = C[j]; C[j] = t; }
        int nt = ns, nf = 0;
        for (long tries = 0; nf < CAPF && tries < 20L * CAPF; tries++) {
            int l1, p1;
            if (nhv && urand() < PH) { int h = hv[rnd() % nhv];
                if (h < n) { p1 = h; l1 = pt[p1 * dg + rnd() % dg]; if (rnd() & 1) p1 = ln[l1 * dg + rnd() % dg]; }
                else { l1 = h - n; p1 = ln[l1 * dg + rnd() % dg]; if (rnd() & 1) l1 = pt[p1 * dg + rnd() % dg]; } }
            else { l1 = rnd() % n; p1 = ln[l1 * dg + rnd() % dg]; }
            int l2 = rnd() % n; if (l1 == l2) continue;
            int p2 = ln[l2 * dg + rnd() % dg];
            if (p1 == p2 || has(ln + l2 * dg, p1) || has(ln + l1 * dg, p2)) continue;
            cand *q = &C[nt++]; q->type = 1; q->a = p1; q->b = l1; q->c = p2; q->d = l2; nf++;
        }
        for (int i = nt - 1; i > 0; i--) { int j = (int)(rnd() % (uint64_t)(i + 1)); cand t = C[i]; C[i] = C[j]; C[j] = t; }
        /* 3-4. evaluate every candidate exactly, then pick */
        long bic = 0, bpc = 0, bwc = 0, bac = 0; int bin = 0, bpn = 0, bwn = 0, ban = 0;
        int bii = -1, bpi = -1, bwi = -1, bai = -1, nev = 0;
        for (int i = 0; i < nt; i++) {
            if ((i & 127) == 0 && now() - t0 > SECS) break;
            cand *q = &C[i];
            int nd2 = q->type == 0 ? ndiff_after(q) : ndiff;
            int tb = cand_tabu(q, step);
            cand_apply(q); long c2 = total(); cand_undo(q); nev++;
            if (c2 < c && (bii < 0 || c2 < bic || (c2 == bic && nd2 < bin))) { bii = i; bic = c2; bin = nd2; }
            if (!tb) {
                if (c2 == c) { if (bpi < 0 || nd2 < bpn) { bpi = i; bpc = c2; bpn = nd2; } }
                else if (bwi < 0 || c2 < bwc || (c2 == bwc && nd2 < bwn)) { bwi = i; bwc = c2; bwn = nd2; }
            }
            if (bai < 0 || c2 < bac || (c2 == bac && nd2 < ban)) { bai = i; bac = c2; ban = nd2; }
            if (c2 == 0) break;
        }
        int pick; long pcost; const char *kind;
        if (bii >= 0) { pick = bii; pcost = bic; kind = "improve"; }
        else if (bpi >= 0) { pick = bpi; pcost = bpc; kind = "plateau"; }
        else if (bwi >= 0) { pick = bwi; pcost = bwc; kind = "worse"; }
        else if (bai >= 0) { pick = bai; pcost = bac; kind = "tabu-all"; }
        else break;
        /* 5. apply, forbid the removed attributes for TEN steps */
        cand *q = &C[pick];
        if (q->type == 0) { int la = sig[q->a], lb = sig[q->b];
            tabuS[q->a * n + la] = (int)(step + TEN); tabuS[q->b * n + lb] = (int)(step + TEN);
            ndiff = ndiff_after(q); }
        else { tabuF[q->a * n + q->b] = (int)(step + TEN); tabuF[q->c * n + q->d] = (int)(step + TEN); }
        cand_apply(q);
        c = eval_hot();
        if (c != pcost) printf("WARNING: applied cost %ld != evaluated %ld\n", c, pcost);
        if (c < best) { best = c; bestnd = ndiff; memcpy(bl, ln, 4L * n * dg); memcpy(bs, sig, 4L * n); save(OUTF, bl, bs); }
        printf("step %ld t=%.1f %s cost=%ld best=%ld ndiff=%d (cands %d, evals %d, hot %d pts %d vtx)\n",
               step, now() - t0, kind, c, best, ndiff, nt, nev, nhot, nhv);
        fflush(stdout);
        if (c == 0) { save(OUT0F, ln, sig); printf("COST 0 at step %ld\n", step); break; }
    }
    printf("RESULT best=%ld bestndiff=%d steps=%ld time=%.0f s\n", best, bestnd, step, now() - t0);
    return 0;
}
