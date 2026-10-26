/* plusopt.c: structural cost of a doubled-matching (DM) Z6 lift over an arbitrary bipartite base.
   Base: points 0..n-1, lines 0..n-1, incidence lists; sigma: point -> line (bijection), doubled.
   In the Z3 quotient (jump point->line = +1, base edges 0) a lifted pair (s, t, coset) is reachable iff some walk of
   length <= 5 reaches it.  For DM-type bases every reachable class also gets both Z2 sheets except the coset-0
   geodesic classes (an OR-constraint on the flag cocycle, solved afterwards), so
       cost = number of unreachable (s, t, coset) over all base sources s.
   Anneals sigma (swaps of two points' images) to minimise the cost.
   Input file: "n deg" then n lines of deg point ids (line incidences), then n sigma values.
   usage: plusopt in.txt   env: SECS, SEED, T0, T1, OUT (sigma output), SCORE=1 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline double urand(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
int n, dg, V; int *ln;   /* ln[l*dg+k] */
int *adjo, *adjn;        /* base adjacency (without jumps): vertex v -> list */
int *sig, *sinv;
uint8_t *st;             /* state bits per vertex: 3 bits for cosets */
uint8_t *fr, *nx;
static long cost_from(int s) {
    memset(st, 0, V); memset(fr, 0, V);
    st[s] = 1; fr[s] = 1;
    for (int d = 0; d < 5; d++) {
        memset(nx, 0, V);
        for (int x = 0; x < V; x++) if (fr[x]) {
            uint8_t b = fr[x];
            for (int j = adjo[x]; j < adjo[x + 1]; j++) nx[adjn[j]] |= b;
            if (x < n) { int y = n + sig[x]; uint8_t r = ((b << 1) | (b >> 2)) & 7; nx[y] |= r; }      /* +1 */
            else { int y = sinv[x - n]; uint8_t r = ((b >> 1) | (b << 2)) & 7; nx[y] |= r; }          /* -1 */
        }
        for (int x = 0; x < V; x++) { nx[x] &= ~st[x]; st[x] |= nx[x]; }
        uint8_t *t = fr; fr = nx; nx = t;
    }
    long c = 0;
    for (int x = 0; x < V; x++) c += 3 - __builtin_popcount(st[x]);
    return c;
}
uint64_t *R0, *F0, *N0;   /* V*3 words */
static long total(void) {
    long c = 0;
    for (int s0 = 0; s0 < V; s0 += 64) {
        int ns = V - s0 < 64 ? V - s0 : 64; uint64_t full = ns == 64 ? ~0ULL : ((1ULL << ns) - 1);
        memset(R0, 0, 24L * V); memset(F0, 0, 24L * V);
        for (int k = 0; k < ns; k++) { R0[(s0 + k) * 3] |= 1ULL << k; F0[(s0 + k) * 3] |= 1ULL << k; }
        for (int d = 0; d < 5; d++) {
            memset(N0, 0, 24L * V);
            for (int x = 0; x < V; x++) { uint64_t a0 = F0[x * 3], a1 = F0[x * 3 + 1], a2 = F0[x * 3 + 2]; if (!(a0 | a1 | a2)) continue;
                for (int j = adjo[x]; j < adjo[x + 1]; j++) { uint64_t *y = N0 + adjn[j] * 3; y[0] |= a0; y[1] |= a1; y[2] |= a2; }
                if (x < n) { uint64_t *y = N0 + (n + sig[x]) * 3; y[1] |= a0; y[2] |= a1; y[0] |= a2; }
                else { uint64_t *y = N0 + sinv[x - n] * 3; y[2] |= a0; y[0] |= a1; y[1] |= a2; } }
            for (int i = 0; i < 3 * V; i++) { N0[i] &= ~R0[i]; R0[i] |= N0[i]; }
            uint64_t *t = F0; F0 = N0; N0 = t;
        }
        for (int i = 0; i < 3 * V; i++) c += ns - __builtin_popcountll(R0[i] & full);
    }
    return c;
}
int main(int argc, char **argv) {
    if (getenv("SEED")) { rs ^= (uint64_t)atoll(getenv("SEED")) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 20; i++) rnd(); }
    FILE *f = fopen(argv[1], "r"); if (fscanf(f, "%d %d", &n, &dg) != 2) return 1; V = 2 * n;
    ln = malloc(4L * n * dg); for (int i = 0; i < n * dg; i++) if (fscanf(f, "%d", &ln[i]) != 1) return 1;
    sig = malloc(4L * n); sinv = malloc(4L * n); for (int i = 0; i < n; i++) { if (fscanf(f, "%d", &sig[i]) != 1) return 1; } fclose(f);
    for (int i = 0; i < n; i++) sinv[sig[i]] = i;
    int *deg = calloc(V, 4); for (int l = 0; l < n; l++) for (int k = 0; k < dg; k++) { deg[ln[l * dg + k]]++; deg[n + l]++; }
    adjo = malloc(4L * (V + 1)); adjo[0] = 0; for (int i = 0; i < V; i++) adjo[i + 1] = adjo[i] + deg[i];
    adjn = malloc(4L * adjo[V]); int *fill = calloc(V, 4);
    for (int l = 0; l < n; l++) for (int k = 0; k < dg; k++) { int p = ln[l * dg + k]; adjn[adjo[p] + fill[p]++] = n + l; adjn[adjo[n + l] + fill[n + l]++] = p; }
    st = malloc(V); fr = malloc(V); nx = malloc(V); R0 = malloc(24L * V); F0 = malloc(24L * V); N0 = malloc(24L * V);
    long c = total();
    printf("n=%d deg=%d cost=%ld\n", n, dg, c); fflush(stdout);
    if (getenv("SCORE")) return 0;
    double secs = getenv("SECS") ? atof(getenv("SECS")) : 60, T0 = getenv("T0") ? atof(getenv("T0")) : 20, T1 = getenv("T1") ? atof(getenv("T1")) : 0.5;
    long best = c; int *bs = malloc(4L * n); memcpy(bs, sig, 4L * n);
    clock_t t0 = clock(); long it = 0;
    while (best > 0) {
        double el = (double)(clock() - t0) / CLOCKS_PER_SEC; if (el > secs) break;
        double T = T0 * pow(T1 / T0, el / secs);
        int a = rnd() % n, b = rnd() % n; if (a == b) continue;
        int la = sig[a], lb = sig[b]; sig[a] = lb; sig[b] = la; sinv[lb] = a; sinv[la] = b;
        long c2 = total(); it++;
        if (c2 <= c || urand() < exp((c - c2) / T)) { c = c2; if (c < best) { best = c; memcpy(bs, sig, 4L * n); printf("t=%.0f it=%ld cost=%ld\n", el, it, c); fflush(stdout); } }
        else { sig[a] = la; sig[b] = lb; sinv[la] = a; sinv[lb] = b; }
    }
    printf("RESULT best=%ld iters=%ld\n", best, it);
    if (getenv("OUT")) { FILE *g = fopen(getenv("OUT"), "w"); for (int i = 0; i < n; i++) fprintf(g, "%d\n", bs[i]); fclose(g); }
    return 0;
}
