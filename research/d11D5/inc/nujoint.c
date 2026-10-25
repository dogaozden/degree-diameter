/* nujoint.c: second stage of a doubled-matching (DM) Z6 lift over a general base: find the flag cocycle nu (Z2 voltages
   3*nu on base flags) jointly with sigma.  Base and sigma in the plusopt format (".in").
   Exact model (research/d11D5/NOTES.md, "The open lead"): a (source, target, coset) triple fails STRUCTURALLY when no walk
   of length <= 5 reaches it in the Z3 quotient (cosets 1, 2), or (coset 0) the pure distance is > 2 (same side) / > 3
   (opposite), no walk with >= 1 jump and jump sum 0 exists, and there are < 2 pure walks of length 4 / 5.  When a coset-0
   class rests on >= 2 pure walks only, it is reached iff the walks do not all have the same nu-parity ("parity pair").
   Cost = WS * structural + violated parity pairs (unordered).  Moves: nu flips on a flag of a violated pair's walk
   (focused, prob 1 - PS), sigma swaps (prob PS; structural cost and the active pair set are recomputed).
   usage: nujoint in.in   env: SEED, SECS, T0, T1, PS (default 0.002), WS (default 50), NU (initial nu file: one 0/1
   per flag, flag id = l*dg + slot), OUT (writes "sigma" .in), OUTNU (nu file), SCORE=1 (score and exit). */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline double urand(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
int n, dg, V; int *ln, *pt, *ptslot; int *sig, *sinv;
uint64_t *R0, *F0, *N0, *C1[6], *C2[6];
/* parity pairs */
long npair, ngeo; int *ps, *pt_, *poff; int *gflag; uint8_t *glen; int *flagoff, *flaggeo; int *pidx;   /* pidx[s*V+t] */
uint8_t *active, *gpar; int *ones; uint8_t *nu; long viol; long *vlist, nvl; long *vpos;
static void vadd(long p) { if (vpos[p] < 0) { vpos[p] = nvl; vlist[nvl++] = p; } }
static void vdel(long p) { long i = vpos[p]; if (i >= 0) { long q = vlist[--nvl]; vlist[i] = q; vpos[q] = i; vpos[p] = -1; } }
static inline int pbad(long p) { int k = poff[p + 1] - poff[p]; return active[p] && (ones[p] == 0 || ones[p] == k); }
/* structural cost; also sets active[] for parity pairs when setact */
static long structural(int setact) {
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
            uint64_t np = C1[0][t] | C1[2][t] | R0[t * 3];   /* coset 0 without parity */
            uint64_t ok0 = np | C2[4][t] | C2[5][t];
            c += ns - __builtin_popcountll(ok0 & full);
            c += ns - __builtin_popcountll(R0[t * 3 + 1] & full);
            c += ns - __builtin_popcountll(R0[t * 3 + 2] & full);
            if (setact) for (int k = 0; k < ns; k++) { int s = s0 + k; if (s >= t) continue; int p = pidx[(long)s * V + t];
                if (p >= 0) active[p] = !((np >> k) & 1); }
        }
    }
    return c;
}
static void recount(void) {
    viol = 0; nvl = 0; for (long p = 0; p < npair; p++) vpos[p] = -1;
    for (long g = 0; g < ngeo; g++) { int x = 0; for (int j = 0; j < glen[g]; j++) x ^= nu[gflag[g * 5 + j]]; gpar[g] = x; }
    for (long p = 0; p < npair; p++) { int o = 0; for (int g = poff[p]; g < poff[p + 1]; g++) o += gpar[g]; ones[p] = o; if (pbad(p)) { viol++; vadd(p); } }
}
int *gpair;
uint16_t *wt = NULL; long wviol = 0; int *dacc, *touch;   /* clause weights (WMODE) */
static int *stamp, stampc = 0;
static long wdelta(int f) {   /* change of the weighted violation count if nu[f] flips (not applied) */
    int nt = 0; long d = 0; stampc++;
    for (int i = flagoff[f]; i < flagoff[f + 1]; i++) { int g = flaggeo[i]; int p = gpair[g];
        if (stamp[p] != stampc) { stamp[p] = stampc; dacc[p] = 0; touch[nt++] = p; } dacc[p] += gpar[g] ? -1 : 1; }
    for (int i = 0; i < nt; i++) { int p = touch[i]; if (!active[p]) continue; int k = poff[p + 1] - poff[p];
        int was = ones[p] == 0 || ones[p] == k; int o2 = ones[p] + dacc[p]; int now = o2 == 0 || o2 == k;
        if (was != now) d += now ? wt[p] : -(long)wt[p]; }
    return d;
}
static long applyflip(int f) {
    long d = 0; nu[f] ^= 1;
    for (int i = flagoff[f]; i < flagoff[f + 1]; i++) { int g = flaggeo[i]; long p = gpair[g];
        int was = pbad(p); ones[p] += gpar[g] ? -1 : 1; gpar[g] ^= 1; int now = pbad(p);
        if (was != now) { if (now) { d++; vadd(p); if (wt) wviol += wt[p]; } else { d--; vdel(p); if (wt) wviol -= wt[p]; } } }
    viol += d; return d;
}
static void save(const char *fn) { FILE *g = fopen(fn, "w"); fprintf(g, "%d %d\n", n, dg);
    for (int l = 0; l < n; l++) for (int k = 0; k < dg; k++) fprintf(g, "%d%c", ln[l * dg + k], k == dg - 1 ? '\n' : ' ');
    for (int i = 0; i < n; i++) fprintf(g, "%d\n", sig[i]); fclose(g); }
static void savenu(const char *fn) { FILE *g = fopen(fn, "w"); for (int f = 0; f < n * dg; f++) fprintf(g, "%d\n", nu[f]); fclose(g); }
int main(int argc, char **argv) {
    if (getenv("SEED")) { rs ^= (uint64_t)atoll(getenv("SEED")) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 20; i++) rnd(); }
    FILE *f = fopen(argv[1], "r"); if (!f || fscanf(f, "%d %d", &n, &dg) != 2) return 1; V = 2 * n;
    ln = malloc(4L * n * dg); for (int i = 0; i < n * dg; i++) if (fscanf(f, "%d", &ln[i]) != 1) return 1;
    sig = malloc(4L * n); sinv = malloc(4L * n); for (int i = 0; i < n; i++) if (fscanf(f, "%d", &sig[i]) != 1) return 1; fclose(f);
    for (int i = 0; i < n; i++) sinv[sig[i]] = i;
    pt = malloc(4L * n * dg); ptslot = malloc(4L * n * dg); int *fill = calloc(n, 4);
    for (int l = 0; l < n; l++) for (int k = 0; k < dg; k++) { int p = ln[l * dg + k]; ptslot[p * dg + fill[p]] = l * dg + k; pt[p * dg + fill[p]++] = l; }
    R0 = malloc(24L * V); F0 = malloc(24L * V); N0 = malloc(24L * V); for (int d = 0; d < 6; d++) { C1[d] = malloc(8L * V); C2[d] = malloc(8L * V); }
    /* distance <= 3 bitsets (pure) to recognise geodesic endpoints */
    int W64 = (V + 63) / 64; uint64_t *near = calloc((size_t)V * W64, 8);   /* near[s] = vertices at pure distance <= 3 */
    for (int s = 0; s < V; s++) {
        uint64_t *b = near + (size_t)s * W64; int fr[4096], nf = 1, nx[4096]; fr[0] = s; b[s >> 6] |= 1ULL << (s & 63);
        for (int d = 1; d <= 3; d++) { int nn = 0;
            for (int i = 0; i < nf; i++) { int x = fr[i]; const int *nb = x < n ? pt + x * dg : ln + (x - n) * dg; int off = x < n ? n : 0;
                for (int j = 0; j < dg; j++) { int y = nb[j] + off; if (!((b[y >> 6] >> (y & 63)) & 1)) { b[y >> 6] |= 1ULL << (y & 63); nx[nn++] = y; } } }
            memcpy(fr, nx, 4 * nn); nf = nn; }
    }
    /* enumerate pure walks of length 4 (same side) and 5 (opposite) between pairs at pure distance 4 / 5 */
    pidx = malloc(4L * V * V); for (long i = 0; i < (long)V * V; i++) pidx[i] = -1;
    long cap = 1 << 22; long gcap = 1 << 23; ps = malloc(4 * cap); pt_ = malloc(4 * cap); int *pcnt = NULL;
    gflag = malloc(4L * 5 * gcap); glen = malloc(gcap); gpair = malloc(4L * gcap); ngeo = 0; npair = 0;
    /* first pass: walk lists per source, grouped by target */
    int *wf = malloc(4L * 5 * 70000), *wt = malloc(4L * 70000);
    for (int s = 0; s < V; s++) {
        int nw = 0; const uint64_t *bs = near + (size_t)s * W64;
        /* walks s=v0 - v1 - v2 - v3 - v4 (- v5); flags recorded as flag ids; no immediate backtracking */
        int sp = s < n;
        for (int a = 0; a < dg; a++) { int v1, f1; if (sp) { v1 = n + pt[s * dg + a]; f1 = ptslot[s * dg + a]; } else { v1 = ln[(s - n) * dg + a]; f1 = (s - n) * dg + a; }
          for (int b = 0; b < dg; b++) { int v2, f2; if (v1 >= n) { v2 = ln[(v1 - n) * dg + b]; f2 = (v1 - n) * dg + b; } else { v2 = n + pt[v1 * dg + b]; f2 = ptslot[v1 * dg + b]; } if (v2 == s) continue;
            for (int c = 0; c < dg; c++) { int v3, f3; if (v2 >= n) { v3 = ln[(v2 - n) * dg + c]; f3 = (v2 - n) * dg + c; } else { v3 = n + pt[v2 * dg + c]; f3 = ptslot[v2 * dg + c]; } if (v3 == v1) continue;
              for (int e = 0; e < dg; e++) { int v4, f4; if (v3 >= n) { v4 = ln[(v3 - n) * dg + e]; f4 = (v3 - n) * dg + e; } else { v4 = n + pt[v3 * dg + e]; f4 = ptslot[v3 * dg + e]; } if (v4 == v2) continue;
                if (v4 > s && !((bs[v4 >> 6] >> (v4 & 63)) & 1)) { /* same side, distance 4 */
                    int *w = wf + 5 * nw; w[0] = f1; w[1] = f2; w[2] = f3; w[3] = f4; w[4] = -1; wt[nw++] = v4; }
                if (sp) for (int h = 0; h < dg; h++) { int v5, f5; if (v4 >= n) { v5 = ln[(v4 - n) * dg + h]; f5 = (v4 - n) * dg + h; } else { v5 = n + pt[v4 * dg + h]; f5 = ptslot[v4 * dg + h]; } if (v5 == v3) continue;
                    if (!((bs[v5 >> 6] >> (v5 & 63)) & 1)) { /* point s, line v5 at distance >= 5 */
                        int *w = wf + 5 * nw; w[0] = f1; w[1] = f2; w[2] = f3; w[3] = f4; w[4] = f5; wt[nw++] = v5; } }
              } } } }
        /* group by target */
        for (int i = 0; i < nw; i++) { int t = wt[i]; long key = (long)s * V + t;
            if (pidx[key] < 0) { pidx[key] = npair; ps[npair] = s; pt_[npair] = t; npair++; } }
        /* store walks in pair order: count then place (pairs of this source are contiguous) */
        static int *cnt = NULL, *firstp = NULL; if (!cnt) { cnt = calloc(V, 4); firstp = malloc(4L * V); } (void)firstp;
        for (int i = 0; i < nw; i++) cnt[wt[i]]++;
        /* we keep walks unsorted: store and remember pair id per walk; sort globally later */
        for (int i = 0; i < nw; i++) { long g = ngeo++; if (g >= gcap) { fprintf(stderr, "gcap\n"); return 1; }
            memcpy(gflag + 5 * g, wf + 5 * i, 20); glen[g] = wf[5 * i + 4] < 0 ? 4 : 5; gpair[g] = pidx[(long)s * V + wt[i]]; }
        for (int i = 0; i < nw; i++) cnt[wt[i]] = 0;
        (void)pcnt;
    }
    /* sort walks by pair (counting sort) */
    poff = calloc(npair + 1, 4); for (long g = 0; g < ngeo; g++) poff[gpair[g] + 1]++;
    for (long p = 0; p < npair; p++) poff[p + 1] += poff[p];
    int *pos = malloc(4L * npair); for (long p = 0; p < npair; p++) pos[p] = poff[p];
    int *gf2 = malloc(4L * 5 * ngeo); uint8_t *gl2 = malloc(ngeo); int *gp2 = malloc(4L * ngeo);
    for (long g = 0; g < ngeo; g++) { int p = gpair[g]; int q = pos[p]++; memcpy(gf2 + 5L * q, gflag + 5 * g, 20); gl2[q] = glen[g]; gp2[q] = p; }
    free(gflag); free(glen); free(gpair); gflag = gf2; glen = gl2; gpair = gp2;
    flagoff = calloc(n * dg + 1, 4); for (long g = 0; g < ngeo; g++) for (int j = 0; j < glen[g]; j++) flagoff[gflag[5 * g + j] + 1]++;
    for (int i = 0; i < n * dg; i++) flagoff[i + 1] += flagoff[i];
    flaggeo = malloc(4L * flagoff[n * dg]); int *fp = malloc(4L * n * dg); memcpy(fp, flagoff, 4L * n * dg);
    for (long g = 0; g < ngeo; g++) for (int j = 0; j < glen[g]; j++) flaggeo[fp[gflag[5 * g + j]]++] = g;
    active = calloc(npair, 1); gpar = calloc(ngeo, 1); ones = calloc(npair, 4); vlist = malloc(8L * npair); vpos = malloc(8L * npair);
    nu = calloc(n * dg, 1);
    if (getenv("NU")) { FILE *g = fopen(getenv("NU"), "r"); for (int i = 0; i < n * dg; i++) { int v; if (fscanf(g, "%d", &v) != 1) break; nu[i] = v & 1; } fclose(g); }
    else for (int i = 0; i < n * dg; i++) nu[i] = rnd() & 1;
    long sc = structural(1); recount();
    long nact = 0; for (long p = 0; p < npair; p++) nact += active[p];
    printf("n=%d dg=%d parity-candidate pairs %ld (walks %ld), active %ld, structural %ld, violated %ld\n", n, dg, npair, ngeo, nact, sc, viol); fflush(stdout);
    if (getenv("SCORE")) return 0;
    double secs = getenv("SECS") ? atof(getenv("SECS")) : 60, T0 = getenv("T0") ? atof(getenv("T0")) : 1.0, T1 = getenv("T1") ? atof(getenv("T1")) : 0.05;
    double PS = getenv("PS") ? atof(getenv("PS")) : 0.002; long WS = getenv("WS") ? atol(getenv("WS")) : 50;
    long cost = WS * sc + viol, best = cost; uint8_t *bnu = malloc(n * dg); int *bsig = malloc(4L * n); memcpy(bnu, nu, n * dg); memcpy(bsig, sig, 4L * n);
    clock_t t0 = clock(); long it = 0;
    if (getenv("WMODE")) {   /* clause weighting (breakout): greedy best flip on a violated pair, bump weights at minima */
        wt = malloc(2L * npair); for (long p = 0; p < npair; p++) wt[p] = 1; dacc = calloc(npair, 4); touch = malloc(4L * npair); stamp = calloc(npair, 4);
        wviol = viol; long bumps = 0; int DEC = getenv("DECAY") ? atoi(getenv("DECAY")) : 50; double NOISE = getenv("NOISE") ? atof(getenv("NOISE")) : 0.02;
        best = viol; memcpy(bnu, nu, n * dg);
        int *cand = malloc(4 * 64);
        while (viol > 0) {
            double el = (double)(clock() - t0) / CLOCKS_PER_SEC; if (el > secs) break; it++;
            long p = vlist[rnd() % nvl]; int nc = 0;
            for (int g = poff[p]; g < poff[p + 1]; g++) for (int j = 0; j < glen[g]; j++) { int fl = gflag[5L * g + j]; int dup = 0; for (int c = 0; c < nc; c++) if (cand[c] == fl) dup = 1; if (!dup && nc < 64) cand[nc++] = fl; }
            long bd = 1L << 40; int bf = -1, ties = 0;
            for (int c = 0; c < nc; c++) { long d = wdelta(cand[c]); if (d < bd) { bd = d; bf = cand[c]; ties = 1; } else if (d == bd && rnd() % (++ties) == 0) bf = cand[c]; }
            if (bd < 0 || urand() < NOISE) applyflip(bf);
            else { for (long i = 0; i < nvl; i++) { long q = vlist[i]; if (wt[q] < 60000) { wt[q]++; wviol++; } } bumps++;
                if (bumps % DEC == 0) { wviol = 0; for (long q = 0; q < npair; q++) { if (wt[q] > 1) wt[q]--; } for (long i = 0; i < nvl; i++) wviol += wt[vlist[i]]; } }
            if (viol < best) { best = viol; memcpy(bnu, nu, n * dg); printf("t=%.0f it=%ld violated=%ld weighted=%ld bumps=%ld\n", el, it, viol, wviol, bumps); fflush(stdout);
                if (getenv("OUTNU")) savenu(getenv("OUTNU")); }
        }
        best = WS * sc + best;
    }
    while (best > 0 && !getenv("WMODE")) {
        double el = (double)(clock() - t0) / CLOCKS_PER_SEC; if (el > secs) break;
        double T = T0 * pow(T1 / T0, el / secs); it++;
        if (urand() < PS) {
            int a = rnd() % n, b = rnd() % n; if (a == b) continue;
            int la = sig[a], lb = sig[b]; sig[a] = lb; sig[b] = la; sinv[lb] = a; sinv[la] = b;
            long sc2 = structural(1); long v2 = 0; for (long p = 0; p < npair; p++) { int bad = pbad(p); v2 += bad; }
            long c2 = WS * sc2 + v2;
            if (c2 <= cost || urand() < exp((cost - c2) / T)) { sc = sc2; nvl = 0; for (long p = 0; p < npair; p++) { vpos[p] = -1; if (pbad(p)) vadd(p); } viol = v2; cost = c2; }
            else { sig[a] = la; sig[b] = lb; sinv[la] = a; sinv[lb] = b; structural(1); }
        } else {
            if (nvl == 0) continue;
            long p = vlist[rnd() % nvl]; int g = poff[p] + rnd() % (poff[p + 1] - poff[p]); int fl = gflag[5L * g + rnd() % glen[g]];
            long d = applyflip(fl);
            if (d <= 0 || urand() < exp(-d / T)) cost += d; else applyflip(fl);
        }
        if (cost < best) { best = cost; memcpy(bnu, nu, n * dg); memcpy(bsig, sig, 4L * n);
            printf("t=%.0f it=%ld cost=%ld (structural %ld, violated %ld) T=%.3f\n", el, it, cost, sc, viol, T); fflush(stdout);
            if (best < 300 && getenv("OUTNU")) { savenu(getenv("OUTNU")); if (getenv("OUT")) save(getenv("OUT")); } }
    }
    memcpy(nu, bnu, n * dg); memcpy(sig, bsig, 4L * n); for (int i = 0; i < n; i++) sinv[sig[i]] = i;
    sc = structural(1); recount();
    printf("RESULT best=%ld structural=%ld violated=%ld iters=%ld\n", best, sc, viol, it);
    if (getenv("OUT")) save(getenv("OUT")); if (getenv("OUTNU")) savenu(getenv("OUTNU"));
    return 0;
}
