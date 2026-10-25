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
int *hot, nhot, collect = 0; uint8_t *ishot; int *hv, nhv; uint8_t *ishv;
static void addhot(int v) { if (!ishv[v]) { ishv[v] = 1; hv[nhv++] = v; } int p = v < n ? v : sinv[v - n]; if (!ishot[p]) { ishot[p] = 1; hot[nhot++] = p; } }
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
    hot = malloc(4L * n); ishot = calloc(n, 1); nhot = 0; hv = malloc(8L * n); ishv = calloc(2 * n, 1); nhv = 0;
    collect = 1; long c = total(); collect = 0;
    printf("n=%d dg=%d cost=%ld hot points=%d\n", n, dg, c, nhot); fflush(stdout);
    double PH = getenv("PH") ? atof(getenv("PH")) : 0.7;
    if (getenv("SCORE")) return 0;
    if (getenv("TWOSTEP")) {   /* one failing same-side pair (v1, v2): force the sigma-relation, then repair */
        int v1 = hv[0], v2 = nhv > 1 ? hv[1] : hv[0]; int part = getenv("PART") ? atoi(getenv("PART")) : 0, nparts = getenv("NPARTS") ? atoi(getenv("NPARTS")) : 1;
        printf("failing vertices %d %d (hot %d)\n", v1, v2, nhv); fflush(stdout);
        int firsts[4096][2], nfirst = 0;
        for (int side = 0; side < 2; side++) { int a0 = side ? v2 : v1, b0 = side ? v1 : v2;
            if (a0 >= n) { /* lines: want sinv[a0-n] collinear with sinv[b0-n]: move line a0 to a point u collinear with w */
                int w = sinv[b0 - n];
                for (int j = 0; j < dg; j++) { int l = pt[w * dg + j]; for (int k = 0; k < dg; k++) { int u = ln[l * dg + k]; if (u == w) continue; firsts[nfirst][0] = u; firsts[nfirst][1] = sinv[a0 - n]; nfirst++; } } }
            else { /* points: want sig[a0] concurrent with sig[b0]: give a0 a line concurrent with sig[b0] */
                int lb = sig[b0];
                for (int k = 0; k < dg; k++) { int p = ln[lb * dg + k]; for (int j = 0; j < dg; j++) { int l = pt[p * dg + j]; if (l == lb) continue; firsts[nfirst][0] = a0; firsts[nfirst][1] = sinv[l]; nfirst++; } } } }
        printf("first moves %d\n", nfirst); fflush(stdout);
        long bestc = c;
        for (int fi = part; fi < nfirst; fi += nparts) { int a = firsts[fi][0], b = firsts[fi][1]; if (a == b) continue;
            int la = sig[a], lb = sig[b]; sig[a] = lb; sig[b] = la; sinv[lb] = a; sinv[la] = b;
            for (int i = 0; i < nhot; i++) ishot[hot[i]] = 0; nhot = 0; for (int i = 0; i < nhv; i++) ishv[hv[i]] = 0; nhv = 0;
            collect = 1; long c1 = total(); collect = 0;
            if (c1 == 0) { printf("first move %d %d -> 0\n", a, b); if (getenv("OUT")) save(getenv("OUT"), ln, sig); return 0; }
            int nh = nhot < 64 ? nhot : 64; int hl[64]; memcpy(hl, hot, 4 * nh);
            for (int i = 0; i < nh; i++) { int a2 = hl[i];
                for (int b2 = 0; b2 < n; b2++) { if (a2 == b2) continue;
                    int la2 = sig[a2], lb2 = sig[b2]; sig[a2] = lb2; sig[b2] = la2; sinv[lb2] = a2; sinv[la2] = b2;
                    long c2 = total();
                    if (c2 < bestc) { bestc = c2; printf("moves (%d %d) (%d %d) -> %ld\n", a, b, a2, b2, c2); fflush(stdout); }
                    if (c2 == 0) { if (getenv("OUT")) save(getenv("OUT"), ln, sig); return 0; }
                    sig[a2] = la2; sig[b2] = lb2; sinv[la2] = a2; sinv[lb2] = b2; } }
            sig[a] = la; sig[b] = lb; sinv[la] = a; sinv[lb] = b;
            if (fi % 16 == part) { printf("first %d/%d (c1=%ld) best %ld\n", fi, nfirst, c1, bestc); fflush(stdout); } }
        printf("TWOSTEP done best %ld\n", bestc); return 0;
    }
    if (getenv("EXHAUST")) {   /* all sigma swaps with a hot point; all flag swaps with a flag near a hot vertex */
        long bestc = c; int nh = nhot; int *hl = malloc(4L * nh); memcpy(hl, hot, 4L * nh);
        int nv2 = nhv; int *hvl = malloc(4L * nv2); memcpy(hvl, hv, 4L * nv2);
        printf("hot points %d, hot vertices %d\n", nh, nv2); fflush(stdout);
        for (int i = 0; i < nh; i++) { int a = hl[i];
            for (int b = 0; b < n; b++) { if (a == b) continue;
                int la = sig[a], lb = sig[b]; sig[a] = lb; sig[b] = la; sinv[lb] = a; sinv[la] = b;
                long c2 = total();
                if (c2 < bestc) { bestc = c2; printf("sigma swap %d %d -> %ld\n", a, b, c2); fflush(stdout); if (c2 == 0) { if (getenv("OUT")) save(getenv("OUT"), ln, sig); return 0; } }
                sig[a] = la; sig[b] = lb; sinv[la] = a; sinv[lb] = b; } }
        printf("sigma swaps done, best %ld\n", bestc); fflush(stdout);
        /* flags near hot vertices */
        int *fl = malloc(8L * n * dg * 2), nfl = 0;
        for (int i = 0; i < nv2; i++) { int h = hvl[i];
            if (h < n) { for (int j = 0; j < dg; j++) { int l = pt[h * dg + j]; for (int k = 0; k < dg; k++) { fl[2 * nfl] = ln[l * dg + k]; fl[2 * nfl + 1] = l; nfl++; } } }
            else { int l0 = h - n; for (int k = 0; k < dg; k++) { int p = ln[l0 * dg + k]; for (int j = 0; j < dg; j++) { fl[2 * nfl] = p; fl[2 * nfl + 1] = pt[p * dg + j]; nfl++; } } } }
        printf("near flags %d\n", nfl); fflush(stdout);
        for (int i = 0; i < nfl; i++) { int p1 = fl[2 * i], l1 = fl[2 * i + 1];
            for (int l2 = 0; l2 < n; l2++) { if (l2 == l1) continue;
                for (int k = 0; k < dg; k++) { int p2 = ln[l2 * dg + k];
                    if (p1 == p2 || has(ln + l2 * dg, p1) || has(ln + l1 * dg, p2)) continue;
                    if (!has(ln + l1 * dg, p1)) break;
                    repl(ln + l1 * dg, p1, p2); repl(ln + l2 * dg, p2, p1); repl(pt + p1 * dg, l1, l2); repl(pt + p2 * dg, l2, l1);
                    long c2 = total();
                    if (c2 < bestc) { bestc = c2; printf("flag swap (%d,%d)(%d,%d) -> %ld\n", p1, l1, p2, l2, c2); fflush(stdout);
                        if (c2 == 0) { if (getenv("OUT")) save(getenv("OUT"), ln, sig); return 0; } }
                    repl(ln + l1 * dg, p2, p1); repl(ln + l2 * dg, p1, p2); repl(pt + p1 * dg, l2, l1); repl(pt + p2 * dg, l1, l2); } } }
        printf("flag swaps done, best %ld\n", bestc); return 0;
    }
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
            int l1, p1;
            if (nhv && urand() < PH) { int h = hv[rnd() % nhv];
                /* a flag at distance <= 1 from the hot vertex */
                if (h < n) { p1 = h; l1 = pt[p1 * dg + rnd() % dg]; if (rnd() & 1) p1 = ln[l1 * dg + rnd() % dg]; }
                else { l1 = h - n; p1 = ln[l1 * dg + rnd() % dg]; if (rnd() & 1) l1 = pt[p1 * dg + rnd() % dg]; } }
            else { l1 = rnd() % n; p1 = ln[l1 * dg + rnd() % dg]; }
            int l2 = rnd() % n; if (l1 == l2) continue;
            int p2 = ln[l2 * dg + rnd() % dg];
            if (p1 == p2 || has(ln + l2 * dg, p1) || has(ln + l1 * dg, p2)) continue;
            repl(ln + l1 * dg, p1, p2); repl(ln + l2 * dg, p2, p1); repl(pt + p1 * dg, l1, l2); repl(pt + p2 * dg, l2, l1);
            long c2 = total();
            if (c2 <= c || urand() < exp((c - c2) / T)) { c = c2; acc++; }
            else { repl(ln + l1 * dg, p2, p1); repl(ln + l2 * dg, p1, p2); repl(pt + p1 * dg, l2, l1); repl(pt + p2 * dg, l1, l2); }
        }
        if ((it & 255) == 0) { for (int i = 0; i < nhot; i++) ishot[hot[i]] = 0; nhot = 0; for (int i = 0; i < nhv; i++) ishv[hv[i]] = 0; nhv = 0; collect = 1; total(); collect = 0; }
        if (c < best) { best = c; memcpy(bl, ln, 4L * n * dg); memcpy(bs, sig, 4L * n); printf("t=%.0f it=%ld cost=%ld T=%.2f\n", el, it, c, T); fflush(stdout);
            if (getenv("OUT")) save(getenv("OUT"), bl, bs); }
    }
    printf("RESULT best=%ld iters=%ld accepted=%ld\n", best, it, acc);
    if (getenv("OUT")) save(getenv("OUT"), bl, bs);
    return 0;
}
