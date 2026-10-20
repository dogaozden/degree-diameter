/* d6lift.c: Delorme's nested duplication on H(q) plus whiskers, for Delta = q + b - 1 (b = 2 or 3 branches).

   Base graph: points 0..N-1, lines N..2N-1 of H(q) (from hexgen). S = Hermitian spread: the q^3+1 lines of H(q)
   inside an elliptic hyperplane section (found by trying hyperplanes until exactly q^3+1 lines are contained).
   Levels: v = first line of S: 2; points of v: 1; other lines on them (set V): 0; S - v: 1; their points: 0;
   whiskers W: 0; everything else -1.  W = lines meeting S - v (not in S, not in V), pairwise disjoint off S, and
   with no point on a line of V.  W is found by simulated annealing on the set-packing problem.
   Lift: a level-k vertex has b^(k+1) versions (strings of length k+1 over b letters); x^a ~ y^c iff x ~ y and
   one of a, c is a prefix of the other.  Each version gains (b-1) per neighbour of higher level (at most one).
   Usage: d6lift q b seconds seed [out.txt] [whiskers_in.txt]
   Writes the lift as "n m" + edge list to out.txt, and the whisker list to runs/W_q{q}_b{b}_s{seed}.txt. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>

int q, N, L, Q1;
int32_t *ln;      /* L*(q+1) */
uint8_t *crd;     /* N*7 */
int32_t *thr;     /* N*(q+1) lines through each point */
static uint64_t rs = 0x9E3779B97F4A7C15ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline double urand(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
/* field tables as in hexgen */
int p, e, ADD[32][32], MUL[32][32];
void field(void) {
    int nr = 0;
    if (e == 2) { for (int t = 2; t < p; t++) { int sq = 0; for (int u = 1; u < p; u++) if (u * u % p == t) sq = 1; if (!sq) { nr = t; break; } } }
    for (int x = 0; x < q; x++) for (int y = 0; y < q; y++) {
        int a = x % p, b = x / p, c = y % p, d = y / p;
        ADD[x][y] = (a + c) % p + p * ((b + d) % p);
        MUL[x][y] = (a * c + b * d % p * nr) % p + p * ((a * d + b * c) % p);
    }
}

int main(int argc, char **argv) {
    q = atoi(argv[1]); int b = atoi(argv[2]); double secs = atof(argv[3]); int seed = atoi(argv[4]);
    const char *out = (argc > 5 && argv[5][0]) ? argv[5] : NULL; const char *win = argc > 6 ? argv[6] : NULL;
    rs ^= (uint64_t)seed * 0x2545F4914F6CDD1DULL; for (int i = 0; i < 10; i++) rnd();
    for (p = 2; q % p; p++) {}
    e = (p == q) ? 1 : 2; field();
    char fn[64]; sprintf(fn, "hex/hex_q%d.bin", q);
    FILE *f = fopen(fn, "rb"); int32_t hdr[3]; if (fread(hdr, 4, 3, f) != 3) return 1;
    N = hdr[1]; L = hdr[2]; Q1 = q + 1;
    ln = malloc(4L * L * Q1); crd = malloc(7L * N);
    if (fread(ln, 4, (size_t)L * Q1, f) != (size_t)L * Q1 || fread(crd, 1, 7L * N, f) != 7L * N) return 1;
    fclose(f);
    thr = malloc(4L * N * Q1); int *tc = calloc(N, sizeof(int));
    for (int k = 0; k < L; k++) for (int j = 0; j < Q1; j++) { int pt = ln[(long)k * Q1 + j]; thr[(long)pt * Q1 + tc[pt]++] = k; }
    /* elliptic hyperplane */
    int target = q * q * q + 1; char *inH = malloc(N); char *inS = calloc(L, 1); int *S = malloc(sizeof(int) * L); int nS = 0;
    for (int tries = 0; tries < 1000 && nS != target; tries++) {
        int a[7]; for (int j = 0; j < 7; j++) a[j] = rnd() % q;
        for (int i = 0; i < N; i++) { int s = 0; for (int j = 0; j < 7; j++) s = ADD[s][MUL[a[j]][crd[7L * i + j]]]; inH[i] = (s == 0); }
        nS = 0;
        for (int k = 0; k < L; k++) { int all = 1; for (int j = 0; j < Q1; j++) if (!inH[ln[(long)k * Q1 + j]]) { all = 0; break; } if (all) S[nS++] = k; }
    }
    if (nS != target) { fprintf(stderr, "no elliptic hyperplane found\n"); return 1; }
    for (int i = 0; i < nS; i++) inS[S[i]] = 1;
    /* S pairwise opposite <=> every line outside S meets exactly one line of S (and S lines are disjoint) */
    char *onS = calloc(N, 1); int bad = 0;
    for (int i = 0; i < nS; i++) for (int j = 0; j < Q1; j++) { int pt = ln[(long)S[i] * Q1 + j]; if (onS[pt]) bad++; onS[pt] = 1; }
    for (int k = 0; k < L; k++) if (!inS[k]) { int c = 0; for (int j = 0; j < Q1; j++) c += onS[ln[(long)k * Q1 + j]]; if (c != 1) bad++; }
    fprintf(stderr, "q=%d N=%d |S|=%d spread check %s\n", q, N, nS, bad ? "FAILED" : "ok");
    if (bad) return 1;
    { char sf[64]; sprintf(sf, "runs/S_q%d_s%d.txt", q, seed); FILE *g = fopen(sf, "w"); for (int i = 0; i < nS; i++) fprintf(g, "%d\n", S[i]); fclose(g); }
    /* levels */
    signed char *lev = malloc(N + L); memset(lev, -1, N + L);
    int v = S[0];
    for (int i = 1; i < nS; i++) { lev[N + S[i]] = 1; for (int j = 0; j < Q1; j++) lev[ln[(long)S[i] * Q1 + j]] = 0; }
    lev[N + v] = 2;
    char *blocked = calloc(N, 1); char *isV = calloc(L, 1);
    for (int j = 0; j < Q1; j++) {
        int u = ln[(long)v * Q1 + j]; lev[u] = 1;
        for (int t = 0; t < Q1; t++) { int k = thr[(long)u * Q1 + t]; if (k == v) continue; lev[N + k] = 0; isV[k] = 1;
            for (int s = 0; s < Q1; s++) { int r = ln[(long)k * Q1 + s]; if (r != u) blocked[r] = 1; } }
    }
    /* optional: B = union of NB blocks through v (block of a blocked point r = the q+1 spread lines at distance
       3 from r); whiskers are then only allowed at points of spread lines outside B (env NB, BSEED) */
    int *sof = malloc(sizeof(int) * N); for (int i = 0; i < N; i++) sof[i] = -1;
    for (int i = 0; i < nS; i++) for (int j = 0; j < Q1; j++) sof[ln[(long)S[i] * Q1 + j]] = S[i];
    char *inB = calloc(L, 1);
    int NB = getenv("NB") ? atoi(getenv("NB")) : 0;
    if (NB > 0) {
        /* list blocks through v: for blocked points r, the spread lines met by the lines through r */
        int nbk = 0; int *bk = malloc(sizeof(int) * (long)q * q * Q1); char *seenv = calloc(L, 1);
        for (int r = 0; r < N && nbk < q * q; r++) {
            if (!blocked[r] || onS[r]) continue;
            int lst[64], c = 0, newb = 0;
            for (int t = 0; t < Q1; t++) { int k = thr[(long)r * Q1 + t]; int s = -1;
                for (int j = 0; j < Q1; j++) { int pt = ln[(long)k * Q1 + j]; if (sof[pt] >= 0) s = sof[pt]; }
                lst[c++] = s; if (s != v && !seenv[s]) newb = 1; }
            if (!newb) continue;
            for (int t = 0; t < c; t++) { if (lst[t] != v) seenv[lst[t]] = 1; bk[(long)nbk * Q1 + t] = lst[t]; }
            nbk++;
        }
        uint64_t save = rs; rs = 0x1234567ULL + (getenv("BSEED") ? atoi(getenv("BSEED")) : 0) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 5; i++) rnd();
        int *perm = malloc(sizeof(int) * nbk); for (int i = 0; i < nbk; i++) perm[i] = i;
        for (int i = nbk - 1; i > 0; i--) { int j = rnd() % (i + 1); int t = perm[i]; perm[i] = perm[j]; perm[j] = t; }
        rs = save;
        for (int i = 0; i < NB; i++) for (int t = 0; t < Q1; t++) inB[bk[(long)perm[i] * Q1 + t]] = 1;
        int cb = 0; for (int k = 0; k < L; k++) cb += inB[k];
        fprintf(stderr, "blocks through v: %d; B uses %d of them, %d spread lines (incl. v)\n", nbk, NB, cb);
    }
    if (getenv("BFILE")) { FILE *g = fopen(getenv("BFILE"), "r"); int k, cb = 0; while (fscanf(g, "%d", &k) == 1) { inB[k] = 1; cb++; } fclose(g);
        fprintf(stderr, "B from file: %d spread lines\n", cb); }
    /* candidates */
    int *cand = malloc(sizeof(int) * L); int nc = 0;
    for (int k = 0; k < L; k++) {
        if (inS[k] || isV[k]) continue;
        { int s = -1; for (int j = 0; j < Q1; j++) { int pt = ln[(long)k * Q1 + j]; if (sof[pt] >= 0) s = sof[pt]; } if (inB[s]) continue; }
        int ok = 1; for (int j = 0; j < Q1; j++) { int pt = ln[(long)k * Q1 + j]; if (!onS[pt] && blocked[pt]) ok = 0; }
        if (ok) cand[nc++] = k;
    }
    long freepts = 0; for (int i = 0; i < N; i++) if (!onS[i] && !blocked[i]) freepts++;
    fprintf(stderr, "candidates %d, free off-S points %ld, whisker bound %ld\n", nc, freepts, freepts / q);
    /* set packing by annealing: elements = free off-S points */
    int *owner = malloc(sizeof(int) * N); for (int i = 0; i < N; i++) owner[i] = -1;
    char *chosen = calloc(nc, 1); int cur = 0, best = 0; char *bestc = calloc(nc, 1);
    int ew = getenv("SPT") ? q + 1 : q;  /* SPT: also forbid two whiskers at one spread point */
    int *el = malloc(sizeof(int) * (long)nc * ew);
    for (int c = 0; c < nc; c++) { int m = 0; for (int j = 0; j < Q1; j++) { int pt = ln[(long)cand[c] * Q1 + j]; if (!onS[pt]) el[(long)c * ew + m++] = pt; } if (ew > q) for (int j = 0; j < Q1; j++) { int pt = ln[(long)cand[c] * Q1 + j]; if (onS[pt]) el[(long)c * ew + q] = pt; } if (m != q) { fprintf(stderr, "whisker with %d off-S points\n", m); return 1; } }
    if (win) {
        FILE *g = fopen(win, "r"); int k;
        int *pos = malloc(sizeof(int) * L); for (int i = 0; i < L; i++) pos[i] = -1; for (int c = 0; c < nc; c++) pos[cand[c]] = c;
        while (fscanf(g, "%d", &k) == 1) { int c = pos[k]; if (c < 0) { fprintf(stderr, "input whisker %d not a candidate\n", k); return 1; }
            for (int j = 0; j < ew; j++) if (owner[el[(long)c * ew + j]] >= 0) { fprintf(stderr, "input whiskers conflict\n"); return 1; }
            chosen[c] = 1; cur++; for (int j = 0; j < ew; j++) owner[el[(long)c * ew + j]] = c; }
        fclose(g); best = cur; memcpy(bestc, chosen, nc);
        fprintf(stderr, "loaded %d whiskers\n", cur);
    }
    clock_t t0 = clock(); double T0 = getenv("T0") ? atof(getenv("T0")) : 0.5, T1 = getenv("T1") ? atof(getenv("T1")) : 0.08; long it = 0; double T = T0;
    int conf[64];
    while (secs > 0) {
        if ((it & 0xFFFF) == 0) {
            double el_s = (double)(clock() - t0) / CLOCKS_PER_SEC; if (el_s > secs) break;
            T = T0 * pow(T1 / T0, el_s / secs);
            if ((it & 0x3FFFFFF) == 0) fprintf(stderr, "t=%.0fs cur=%d best=%d T=%.3f\n", el_s, cur, best, T);
        }
        it++;
        int c = rnd() % nc; if (chosen[c]) continue;
        int k = 0;
        for (int j = 0; j < ew; j++) { int o = owner[el[(long)c * ew + j]]; if (o >= 0) { int dup = 0; for (int s = 0; s < k; s++) if (conf[s] == o) dup = 1; if (!dup) conf[k++] = o; } }
        int delta = 1 - k;
        if (delta < 0 && urand() >= exp(delta / T)) continue;
        for (int s = 0; s < k; s++) { int o = conf[s]; chosen[o] = 0; for (int j = 0; j < ew; j++) owner[el[(long)o * ew + j]] = -1; }
        chosen[c] = 1; for (int j = 0; j < ew; j++) owner[el[(long)c * ew + j]] = c;
        cur += delta;
        if (cur > best) { best = cur; memcpy(bestc, chosen, nc); }
    }
    fprintf(stderr, "whiskers best=%d after %ld moves\n", best, it);
    sprintf(fn, "runs/W_q%d_b%d_s%d.txt", q, b, seed);
    FILE *wf = fopen(fn, "w"); for (int c = 0; c < nc; c++) if (bestc[c]) { fprintf(wf, "%d\n", cand[c]); lev[N + cand[c]] = 0; } fclose(wf);
    /* level checks: neighbour levels differ by <= 1, at most one higher neighbour */
    int nV = 2 * N; /* base vertices: points then lines */
    long viol = 0;
    for (int x = 0; x < nV; x++) {
        int hi = 0;
        int isP = x < N;
        for (int j = 0; j < Q1; j++) {
            int y = isP ? N + thr[(long)x * Q1 + j] : ln[(long)(x - N) * Q1 + j];
            int d = lev[y] - lev[x]; if (d > 1 || d < -1) viol++; if (d == 1) hi++;
        }
        if (hi > 1) viol++;
    }
    long gain = 0, pw[8]; pw[0] = 1; for (int i = 1; i < 8; i++) pw[i] = pw[i - 1] * b;
    for (int x = 0; x < nV; x++) if (lev[x] >= 0) gain += pw[lev[x] + 1] - 1;
    long n = 2L * N + gain;
    fprintf(stderr, "level violations %ld, gain %ld, order %ld\n", viol, gain, n);
    if (viol) return 1;
    if (!out) return 0;
    /* ids */
    long *base = malloc(sizeof(long) * (nV + 1)); base[0] = 0;
    for (int x = 0; x < nV; x++) base[x + 1] = base[x] + (lev[x] >= 0 ? pw[lev[x] + 1] : 1);
    long m = 0;
    for (int x = 0; x < N; x++) for (int j = 0; j < Q1; j++) {
        int y = N + thr[(long)x * Q1 + j]; int lx = lev[x] + 1, ly = lev[y] + 1; /* string lengths */
        long nx = pw[lx], ny = pw[ly];
        if (lx <= ly) m += ny; else m += nx;
    }
    FILE *o = fopen(out, "w"); fprintf(o, "%ld %ld\n", n, m);
    for (int x = 0; x < N; x++) for (int j = 0; j < Q1; j++) {
        int y = N + thr[(long)x * Q1 + j]; int lx = lev[x] + 1, ly = lev[y] + 1;
        if (lx <= ly) { for (long c = 0; c < pw[ly]; c++) fprintf(o, "%ld %ld\n", base[x] + c / pw[ly - lx], base[y] + c); }
        else { for (long a = 0; a < pw[lx]; a++) fprintf(o, "%ld %ld\n", base[x] + a, base[y] + a / pw[lx - ly]); }
    }
    fclose(o);
    fprintf(stderr, "wrote %s: n=%ld m=%ld\n", out, n, m);
    return 0;
}
