/* plusopt2.c: anneal the BASE of a doubled-matching (DM) Z6 lift.  The base is any dg-regular bipartite graph
   (n points, n lines) with a point -> line bijection sigma; its edges are doubled.  Structural cost = number of
   (source, target, coset) triples unreachable by walks of length <= 5 in the Z3 quotient (jump point->line = +1).
   Moves: swap the sigma-images of two points (prob 1 - PF), or a degree-preserving flag swap
   (p1,l1),(p2,l2) -> (p1,l2),(p2,l1) (prob PF).  Cost 0 leaves only the coset-0 geodesic parity conditions, which
   the flag cocycle has to satisfy afterwards (zcons / dmfast-style annealing).
   Input/output format: "n dg" then n lines of dg point ids (points of each line), then n sigma values.
   usage: plusopt2 in.txt   env: SECS, SEED, T0, T1, PF, OUT, SCORE=1 */
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
int *hot, nhot, collect = 0; uint8_t *ishot;
static void addhot(int v) { int p = v < n ? v : sinv[v - n]; if (!ishot[p]) { ishot[p] = 1; hot[nhot++] = p; } }
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
            int same = (t < n) == (s0 < n);   /* batches never straddle sides only if n % 64 == 0; handle per bit below */
            (void)same;
            /* same-side bits: walks of even length; opposite-side: odd.  Pure ok: length<=2 reach, or >=2 walks of length 4 (same)
               or >=2 walks of length 5 (opposite); counts of the wrong parity are 0 automatically (bipartite). */
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
static void save(const char *fn, int *L2, int *S2) { FILE *g = fopen(fn, "w"); fprintf(g, "%d %d\n", n, dg);
    for (int l = 0; l < n; l++) { for (int k = 0; k < dg; k++) fprintf(g, "%d%c", L2[l * dg + k], k == dg - 1 ? '\n' : ' '); }
    for (int i = 0; i < n; i++) fprintf(g, "%d\n", S2[i]); fclose(g); }
int main(int argc, char **argv) {
    if (getenv("SEED")) { rs ^= (uint64_t)atoll(getenv("SEED")) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 20; i++) rnd(); }
    FILE *f = fopen(argv[1], "r"); if (fscanf(f, "%d %d", &n, &dg) != 2) return 1; V = 2 * n;
    ln = malloc(4L * n * dg); for (int i = 0; i < n * dg; i++) if (fscanf(f, "%d", &ln[i]) != 1) return 1;
    sig = malloc(4L * n); sinv = malloc(4L * n); for (int i = 0; i < n; i++) if (fscanf(f, "%d", &sig[i]) != 1) return 1; fclose(f);
    for (int i = 0; i < n; i++) sinv[sig[i]] = i;
    pt = malloc(4L * n * dg); int *fill = calloc(n, 4);
    for (int l = 0; l < n; l++) for (int k = 0; k < dg; k++) { int p = ln[l * dg + k]; if (fill[p] >= dg) { fprintf(stderr, "point degree > dg\n"); return 1; } pt[p * dg + fill[p]++] = l; }
    for (int p = 0; p < n; p++) if (fill[p] != dg) { fprintf(stderr, "point %d degree %d\n", p, fill[p]); return 1; }
    R0 = malloc(24L * V); F0 = malloc(24L * V); N0 = malloc(24L * V); for (int d = 0; d < 6; d++) { C1[d] = malloc(8L * V); C2[d] = malloc(8L * V); }
    hot = malloc(4L * n); ishot = calloc(n, 1); nhot = 0;
    collect = 1; long c = total(); collect = 0;
    printf("n=%d dg=%d cost=%ld hot points=%d\n", n, dg, c, nhot); fflush(stdout);
    double PH = getenv("PH") ? atof(getenv("PH")) : 0.7;
    if (getenv("SCORE")) return 0;
    double secs = getenv("SECS") ? atof(getenv("SECS")) : 60, T0 = getenv("T0") ? atof(getenv("T0")) : 20, T1 = getenv("T1") ? atof(getenv("T1")) : 0.5;
    double PF = getenv("PF") ? atof(getenv("PF")) : 0.3;
    long best = c; int *bl = malloc(4L * n * dg), *bs = malloc(4L * n); memcpy(bl, ln, 4L * n * dg); memcpy(bs, sig, 4L * n);
    clock_t t0 = clock(); long it = 0, acc = 0;
    while (best > 0) {
        double el = (double)(clock() - t0) / CLOCKS_PER_SEC; if (el > secs) break;
        double T = T0 * pow(T1 / T0, el / secs);
        it++;
        if (urand() >= PF) {
            int a = (nhot && urand() < PH) ? hot[rnd() % nhot] : rnd() % n, b = rnd() % n; if (a == b) continue;
            int la = sig[a], lb = sig[b]; sig[a] = lb; sig[b] = la; sinv[lb] = a; sinv[la] = b;
            long c2 = total();
            if (c2 <= c || urand() < exp((c - c2) / T)) { c = c2; acc++; }
            else { sig[a] = la; sig[b] = lb; sinv[la] = a; sinv[lb] = b; }
        } else {
            int l1 = rnd() % n, l2 = rnd() % n; if (l1 == l2) continue;
            int p1 = ln[l1 * dg + rnd() % dg], p2 = ln[l2 * dg + rnd() % dg];
            if (p1 == p2 || has(ln + l2 * dg, p1) || has(ln + l1 * dg, p2)) continue;
            repl(ln + l1 * dg, p1, p2); repl(ln + l2 * dg, p2, p1); repl(pt + p1 * dg, l1, l2); repl(pt + p2 * dg, l2, l1);
            long c2 = total();
            if (c2 <= c || urand() < exp((c - c2) / T)) { c = c2; acc++; }
            else { repl(ln + l1 * dg, p2, p1); repl(ln + l2 * dg, p1, p2); repl(pt + p1 * dg, l2, l1); repl(pt + p2 * dg, l1, l2); }
        }
        if ((it & 255) == 0) { for (int i = 0; i < nhot; i++) ishot[hot[i]] = 0; nhot = 0; collect = 1; total(); collect = 0; }
        if (c < best) { best = c; memcpy(bl, ln, 4L * n * dg); memcpy(bs, sig, 4L * n); printf("t=%.0f it=%ld cost=%ld T=%.2f\n", el, it, c, T); fflush(stdout);
            if (getenv("OUT")) save(getenv("OUT"), bl, bs); }
    }
    printf("RESULT best=%ld iters=%ld accepted=%ld\n", best, it, acc);
    if (getenv("OUT")) save(getenv("OUT"), bl, bs);
    return 0;
}
