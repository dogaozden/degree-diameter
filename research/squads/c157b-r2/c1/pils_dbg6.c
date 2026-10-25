/* pils.c: iterated local search for 1-defective point sets of H(q): the collinearity graph on the set is a matching,
   and a pair {x,y} (collinear, both points allowed) is allowed only if allow[x] and allow[y].
   Local search: free insertions, pair insertions (a single w plus an allowed collinear point with no other chosen
   neighbour), (1,2)-swaps (a single w replaced by two points that are blocked only by w, collinear only if allowed).
   Kicks (50/50): (a) force-insert a point x with 1..KMAX blockers removed; (b) force-insert an allowed collinear pair
   {x,y} with all their blockers removed. Rejected kicks are undone from a log; a worse-by-2 kick is accepted with
   probability 3%; the search restarts from the best set when it is 4 below it. Removed elements are tabu for forced
   insertion for TT iterations.
   usage: pils HEXBIN SEED SECONDS START.txt ALLOW.txt OUT.txt */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>

static void verify(const int *S, int n, int *pairs, int *bad);
static double wall(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }

static int q, N, Q1, DEG;
static int *LP, *PL, *NB;
static unsigned char *allow, *in;
static int *blk, *sol, *pos, ns;
static int *bestsol, bestn;
static int *logE; static unsigned char *logOp; static long nlog, logcap;
static int logging = 1;
static int *dq; static unsigned char *dqf; static long dqh = 0, dqn = 0;
static long *tabu;
static uint32_t *mk; static uint32_t stamp = 0;
static long it = 0; static int KMAX = 2; static const int TT = 10;

static void logpush(int e, int op) {
    if (!logging) return;
    if (nlog >= logcap) { logcap = logcap * 2 + 4096; logE = realloc(logE, sizeof(int) * logcap); logOp = realloc(logOp, logcap); }
    logE[nlog] = e; logOp[nlog] = (unsigned char)op; nlog++;
}
static void add(int e) {
    if (in[e]) { fprintf(stderr, "ADD of chosen %d it=%ld logging=%d\n", e, it, logging); exit(9); }
    in[e] = 1; pos[e] = ns; sol[ns++] = e;
    const int *nb = NB + (long)e * DEG; for (int k = 0; k < DEG; k++) blk[nb[k]]++;
    logpush(e, 1);
}
static void rem(int e) {
    if (!in[e]) { fprintf(stderr, "REM of unchosen %d it=%ld logging=%d\n", e, it, logging); exit(10); }
    in[e] = 0; int p = pos[e]; sol[p] = sol[--ns]; pos[sol[p]] = p;
    const int *nb = NB + (long)e * DEG; for (int k = 0; k < DEG; k++) blk[nb[k]]--;
    logpush(e, 0);
}
static void dpush(int e) { if (!dqf[e]) { dqf[e] = 1; dq[(dqh + dqn) % N] = e; dqn++; } }
static int dpop(void) { int e = dq[dqh]; dqh = (dqh + 1) % N; dqn--; dqf[e] = 0; return e; }
static int blocker(int e) { const int *nb = NB + (long)e * DEG; for (int k = 0; k < DEG; k++) if (in[nb[k]]) return nb[k]; return -1; }
static int feasible(int e) {
    if (in[e]) return 0;
    int b = blk[e];
    if (b == 0) return 1;
    if (b >= 2 || !allow[e]) return 0;
    int w = blocker(e);
    return blk[w] == 0 && allow[w];
}
/* after the neighbourhood of w changed: queue the neighbours of w, and the single blocker of every 1-tight neighbour */
static void push_around(int w) {
    const int *nb = NB + (long)w * DEG;
    for (int k = 0; k < DEG; k++) {
        int y = nb[k]; dpush(y);
        if (!in[y] && blk[y] == 1) dpush(blocker(y));
    }
}
static int T[512];
static int try12(int w) {                    /* w chosen, blk[w] == 0 (a single) */
    int nt = 0; const int *nb = NB + (long)w * DEG;
    for (int k = 0; k < DEG; k++) { int y = nb[k]; if (!in[y] && blk[y] == 1 && nt < 512) T[nt++] = y; }
    if (nt < 2) return 0;
    for (int i = 0; i < nt; i++) {
        stamp++; if (stamp == 0) { memset(mk, 0, sizeof(uint32_t) * N); stamp = 1; }
        const int *nbi = NB + (long)T[i] * DEG;
        for (int k = 0; k < DEG; k++) mk[nbi[k]] = stamp;
        for (int j = i + 1; j < nt; j++) {
            int ok = (mk[T[j]] != stamp) || (allow[T[i]] && allow[T[j]]);
            if (!ok) continue;
            int a = T[i], b = T[j];
            rem(w); add(a); add(b);
            push_around(w); dpush(a); dpush(b);
            return 1;
        }
    }
    return 0;
}
static void ls(void) {
    while (dqn > 0) {
        int e = dpop();
        if (!in[e]) { if (feasible(e)) { int wb = (blk[e] == 1) ? blocker(e) : -1; add(e);
                if (it >= 3800) { int pr_, bd_; verify(sol, ns, &pr_, &bd_); if (bd_) { fprintf(stderr, "feasible-add e=%d blk_before=%d blocker=%d allow e %d w %d blk_w_now %d\n", e, blk[e]-(blk[e]==1 ? 1:0), wb, allow[e], wb>=0?allow[wb]:-1, wb>=0?blk[wb]:-1); exit(7);} } } }
        else if (blk[e] == 0) { int r_ = try12(e); if (r_ && it >= 3800) { int pr_, bd_; verify(sol, ns, &pr_, &bd_); if (bd_) { fprintf(stderr, "try12 e=%d bad=%d\n", e, bd_); exit(8);} } }
    }
}
static void kick_remove(int w) {
    int p = (blk[w] == 1) ? blocker(w) : -1;
    tabu[w] = it + TT;
    rem(w);
    push_around(w);
    if (p >= 0 && blk[p] == 0) { dpush(p); const int *np = NB + (long)p * DEG; for (int k = 0; k < DEG; k++) dpush(np[k]); }
}
static int pick_x(void) {                    /* a non-chosen point with few blockers, not tabu */
    for (long tries = 0; ; tries++) {
        int x = rnd() % N;
        if (!in[x] && blk[x] <= KMAX && tabu[x] < it) return x;
        if (tries > 200000) { KMAX++; tries = 0; fprintf(stderr, "KMAX -> %d\n", KMAX); }
    }
}
static void single_kick(void) {
    int x = pick_x(); int B[8], nb_ = 0; const int *nb = NB + (long)x * DEG;
    for (int k = 0; k < DEG && nb_ < 8; k++) if (in[nb[k]]) B[nb_++] = nb[k];
    for (int i = 0; i < nb_; i++) kick_remove(B[i]);
    add(x);
}
static void pair_kick(void) {
    for (int tries = 0; ; tries++) {
        int x = pick_x(); if (!allow[x]) continue;
        int c = PL[(long)x * Q1 + (rnd() % Q1)];
        int y = LP[(long)c * Q1 + (rnd() % Q1)]; if (y == x || in[y] || !allow[y] || blk[y] > KMAX) continue;
        int B[16], nb_ = 0; const int *nx = NB + (long)x * DEG, *ny = NB + (long)y * DEG;
        for (int k = 0; k < DEG; k++) if (in[nx[k]] && nb_ < 16) B[nb_++] = nx[k];
        for (int k = 0; k < DEG; k++) if (in[ny[k]] && nb_ < 16) B[nb_++] = ny[k];
        if (nb_ >= 16) continue;
        for (int i = 0; i < nb_; i++) kick_remove(B[i]);
        add(x); add(y);
        return;
    }
}
static void undo(void) {
    logging = 0;
    for (long i = nlog - 1; i >= 0; i--) { if (logOp[i]) rem(logE[i]); else add(logE[i]); }
    logging = 1; nlog = 0;
}
static void restore_best(void) {
    logging = 0;
    while (ns) rem(sol[ns - 1]);
    for (int i = 0; i < bestn; i++) add(bestsol[i]);
    logging = 1; nlog = 0;
}
static void write_best(const char *fn) {
    FILE *o = fopen(fn, "w"); for (int i = 0; i < bestn; i++) fprintf(o, "%d\n", bestsol[i]); fclose(o);
}
static void verify(const int *S, int n, int *pairs, int *bad) {
    unsigned char *s = calloc(N, 1); for (int i = 0; i < n; i++) s[S[i]] = 1;
    int np = 0, nbad = 0;
    for (int i = 0; i < n; i++) {
        int x = S[i], c = 0, p = -1; const int *nb = NB + (long)x * DEG;
        for (int k = 0; k < DEG; k++) if (s[nb[k]]) { c++; p = nb[k]; }
        if (c > 1) nbad++;
        else if (c == 1) {
            np++; int c2 = 0; const int *np2 = NB + (long)p * DEG;
            for (int k = 0; k < DEG; k++) if (s[np2[k]]) c2++;
            if (!allow[x] || !allow[p] || c2 != 1) nbad++;
        }
    }
    free(s); *pairs = np / 2; *bad = nbad;
}
int main(int argc, char **argv) {
    if (argc < 7) { fprintf(stderr, "usage: pils HEXBIN SEED SECONDS START ALLOW OUT\n"); return 1; }
    FILE *f = fopen(argv[1], "rb"); int hdr[3]; if (!f || fread(hdr, 4, 3, f) != 3) return 1;
    q = hdr[0]; N = hdr[1]; Q1 = q + 1; DEG = Q1 * q;
    int Lc = hdr[2];
    LP = malloc(sizeof(int) * (long)Lc * Q1); if (fread(LP, 4, (size_t)Lc * Q1, f) != (size_t)Lc * Q1) return 1; fclose(f);
    PL = malloc(sizeof(int) * (long)N * Q1); int *c0 = calloc(N, sizeof(int));
    for (int l = 0; l < Lc; l++) for (int i = 0; i < Q1; i++) { int p = LP[l * Q1 + i]; PL[p * Q1 + c0[p]++] = l; }
    NB = malloc(sizeof(int) * (long)N * DEG); mk = calloc(N, sizeof(uint32_t));
    for (int p = 0; p < N; p++) {
        int k = 0;
        for (int i = 0; i < Q1; i++) { int c = PL[p * Q1 + i]; for (int t = 0; t < Q1; t++) { int y = LP[c * Q1 + t]; if (y != p) NB[(long)p * DEG + k++] = y; } }
        if (k != DEG) { fprintf(stderr, "bad degree at %d\n", p); return 1; }
    }
    rs ^= (uint64_t)atoll(argv[2]) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 20; i++) rnd();
    double secs = atof(argv[3]);
    allow = calloc(N, 1); { FILE *g = fopen(argv[5], "r"); int e; while (fscanf(g, "%d", &e) == 1) allow[e] = 1; fclose(g); }
    in = calloc(N, 1); blk = calloc(N, sizeof(int)); sol = malloc(sizeof(int) * N); pos = malloc(sizeof(int) * N);
    bestsol = malloc(sizeof(int) * N); dq = malloc(sizeof(int) * N); dqf = calloc(N, 1); tabu = calloc(N, sizeof(long));
    logcap = 1 << 16; logE = malloc(sizeof(int) * logcap); logOp = malloc(logcap);
    ns = 0; nlog = 0;
    { FILE *g = fopen(argv[4], "r"); int e, rej = 0; while (fscanf(g, "%d", &e) == 1) { if (feasible(e)) add(e); else rej++; } fclose(g);
      if (rej) fprintf(stderr, "start: %d rejected\n", rej); }
    int st0 = ns;
    int *perm = malloc(sizeof(int) * N); for (int i = 0; i < N; i++) perm[i] = i;
    for (int i = N - 1; i > 0; i--) { int j = rnd() % (i + 1); int t = perm[i]; perm[i] = perm[j]; perm[j] = t; }
    for (int pass = 0; pass < 2; pass++) for (int i = 0; i < N; i++) if (feasible(perm[i])) add(perm[i]);
    for (int i = 0; i < N; i++) dpush(perm[i]);
    ls(); nlog = 0;
    fprintf(stderr, "start %d, after greedy+LS %d\n", st0, ns);
    bestn = ns; memcpy(bestsol, sol, sizeof(int) * ns);
    long best_it = 0; double t0 = wall(), lp = 0;
    long acc_worse = 0, rej_ct = 0;
    while (1) {
        if ((it & 127) == 0) {
            double el = wall() - t0; if (el > secs) break;
            if (el - lp > 60) { lp = el; fprintf(stderr, "t=%.0f it=%ld cur=%d best=%d acc_worse=%ld rej=%ld\n", el, it, ns, bestn, acc_worse, rej_ct);
                write_best(argv[6]); }
        }
        it++; nlog = 0; long prev = ns;
        int kind_ = rnd() & 1;
        if (kind_) pair_kick(); else single_kick();
        { int pr_, bd_; if (it > 1990) { verify(sol, ns, &pr_, &bd_); if (bd_) { fprintf(stderr, "BROKEN right after kick: kind=%d it=%ld bad=%d\n", kind_, it, bd_); exit(5);} } }
        ls();
        { int pr_, bd_; if (it > 1990) { verify(sol, ns, &pr_, &bd_); if (bd_) { fprintf(stderr, "BROKEN after ls: kind=%d it=%ld bad=%d ns=%d\n", kind_, it, bd_, ns); exit(6);} } }
        long delta = (long)ns - prev;
        if (delta < 0) {
            if (delta >= -2 && (rnd() % 100) < 3) acc_worse++;
            else { undo(); rej_ct++; }
        }
        nlog = 0;
        if (ns > bestn) { bestn = ns; memcpy(bestsol, sol, sizeof(int) * ns); best_it = it; }
        if (bestn - ns >= 4 || (it - best_it > 4000000 && ns < bestn)) { restore_best(); best_it = it; }
    }
    restore_best();
    int pairs, bad; verify(bestsol, bestn, &pairs, &bad);
    write_best(argv[6]);
    printf("best %d (%d pairs) after %ld iterations; violations %d\n", bestn, pairs, it, bad);
    return bad ? 2 : 0;
}
