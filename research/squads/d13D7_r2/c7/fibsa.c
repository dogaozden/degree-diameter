/* c7 wildcard: "fiber-line" model of pairwise-opposite sets of H(11).
   Affine model: points t=(a,b,c,e,f) in F_11^5, pairwise compatible iff Q'(t-t')=c^2-ae-bf != 0 (for differences).
   Fiber (b,c): candidate points (a, b, c, sig*a+g, h) for a in F_11, i.e. one affine line per (b,c) with label (sig,g,h).
   Two candidates in the same fiber never conflict (sig != 0); any subset of a fiber's line is allowed.
   Inner: k-fixed min-conflict tabu for an independent set of size k in the 1331-candidate conflict graph.
   Outer: simulated-style move = relabel one fiber, repair with tabu at size m (accept if ok), try m+1.
   usage: fibsa OFFSETS SEED CPU_SECONDS OUT_AFFINE */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define Q 11
#define NF 121
#define NC 1331

static int sig[NF], gl[NF], hl[NF];
static int CA[NC], CB[NC], CC[NC], CE[NC], CF[NC];
static uint8_t M[NC][NC];
static int inS[NC], cnt[NC];
static long tabu[NC];
static long G = 0;
static int S[NC], spos[NC], ssz = 0;
static uint64_t rs = 0x9E3779B97F4A7C15ULL;

static uint32_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return (uint32_t)(rs >> 16); }
static int md(int x) { x %= Q; return x < 0 ? x + Q : x; }

static void setcoords(int fib) {
    int b = fib % Q, c = fib / Q;
    for (int a = 0; a < Q; a++) {
        int id = fib * Q + a;
        CA[id] = a; CB[id] = b; CC[id] = c;
        CE[id] = md(sig[fib] * a + gl[fib]); CF[id] = hl[fib];
    }
}
static int conflict(int i, int j) {
    int da = md(CA[i] - CA[j]), db = md(CB[i] - CB[j]), dc = md(CC[i] - CC[j]);
    int de = md(CE[i] - CE[j]), df = md(CF[i] - CF[j]);
    return md(dc * dc - da * de - db * df) == 0;
}
static void rebuild_fiber(int fib) {
    setcoords(fib);
    for (int a = 0; a < Q; a++) {
        int i = fib * Q + a;
        for (int j = 0; j < NC; j++) {
            if (j == i) { M[i][j] = 0; continue; }
            uint8_t v = (uint8_t)conflict(i, j);
            M[i][j] = v; M[j][i] = v;
        }
    }
}
static void s_add(int v) {
    inS[v] = 1; spos[v] = ssz; S[ssz++] = v;
    for (int w = 0; w < NC; w++) cnt[w] += M[v][w];
}
static void s_rem(int v) {
    inS[v] = 0; int p = spos[v]; int last = S[--ssz]; S[p] = last; spos[last] = p;
    for (int w = 0; w < NC; w++) cnt[w] -= M[v][w];
}
static int tabu_k(int k, long maxit) {
    while (ssz > k) {
        int bu = S[0];
        for (int i = 1; i < ssz; i++) if (cnt[S[i]] > cnt[bu]) bu = S[i];
        s_rem(bu);
    }
    while (ssz < k) {
        int bv = -1;
        for (int v = 0; v < NC; v++) if (!inS[v] && (bv < 0 || cnt[v] < cnt[bv])) bv = v;
        s_add(bv);
    }
    for (long it = 0; it < maxit; it++, G++) {
        long cost = 0;
        for (int i = 0; i < ssz; i++) cost += cnt[S[i]];
        if (cost == 0) return 1;
        int bu = -1, bc = -1, nt = 0;
        for (int i = 0; i < ssz; i++) {
            int v = S[i];
            if (tabu[v] > G) continue;
            if (cnt[v] > bc) { bc = cnt[v]; bu = v; nt = 1; }
            else if (cnt[v] == bc) { nt++; if (rnd() % nt == 0) bu = v; }
        }
        if (bu < 0) bu = S[rnd() % ssz];
        s_rem(bu); tabu[bu] = G + 7 + rnd() % 10;
        int bv = -1; bc = 1 << 30; nt = 0;
        for (int v = 0; v < NC; v++) {
            if (inS[v] || tabu[v] > G) continue;
            if (cnt[v] < bc) { bc = cnt[v]; bv = v; nt = 1; }
            else if (cnt[v] == bc) { nt++; if (rnd() % nt == 0) bv = v; }
        }
        if (bv < 0) bv = bu;
        s_add(bv); tabu[bv] = G + 2 + rnd() % 3;
    }
    return 0;
}
static void write_sol(const char *path, int m) {
    FILE *f = fopen(path, "w");
    fprintf(f, "# %d affine points (a b c e f), fiber-line model\n", m);
    for (int i = 0; i < ssz; i++) { int v = S[i]; fprintf(f, "%d %d %d %d %d\n", CA[v], CB[v], CC[v], CE[v], CF[v]); }
    fclose(f);
}
static double cpu(void) { return (double)clock() / CLOCKS_PER_SEC; }

int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage: fibsa OFFSETS SEED CPU_SECONDS OUT_AFFINE\n"); return 1; }
    rs ^= (uint64_t)atoll(argv[2]) * 0x2545F4914F6CDD1DULL + 1;
    for (int i = 0; i < 10; i++) rnd();
    double limit = atof(argv[3]);
    int used[NF]; memset(used, 0, sizeof used);
    for (int p = 0; p < NF; p++) { sig[p] = 1 + rnd() % 10; gl[p] = rnd() % Q; hl[p] = rnd() % Q; }
    FILE *fo = fopen(argv[1], "r"); char buf[256];
    while (fgets(buf, sizeof buf, fo)) {
        if (buf[0] == '#') continue;
        int a, b, c, e, f;
        if (sscanf(buf, "%d %d %d %d %d", &a, &b, &c, &e, &f) != 5) continue;
        int fib = b + Q * c; used[fib] = 1; sig[fib] = 9; gl[fib] = md(e - 9 * a); hl[fib] = md(f);
    }
    fclose(fo);
    for (int p = 0; p < NF; p++) setcoords(p);
    for (int i = 0; i < NC; i++) for (int j = 0; j < NC; j++) M[i][j] = (i != j) ? (uint8_t)conflict(i, j) : 0;
    /* initial S: all candidates of used fibers (full lines) */
    for (int p = 0; p < NF; p++) if (used[p]) for (int a = 0; a < Q; a++) s_add(p * Q + a);
    /* sanity: cost 0? */
    { long cost = 0; for (int i = 0; i < ssz; i++) cost += cnt[S[i]]; fprintf(stderr, "init size %d cost %ld\n", ssz, cost / 2); }
    int m = ssz, bestm = ssz;
    static int oldS[NC]; int oldsz;
    long moves = 0, accepted = 0, plus = 0, downs = 0;
    int oldsig, oldg, oldh;
    while (cpu() < limit) {
        int p = rnd() % NF;
        oldsz = ssz; memcpy(oldS, S, sizeof(int) * ssz);
        oldsig = sig[p]; oldg = gl[p]; oldh = hl[p];
        for (int a = 0; a < Q; a++) { int i = p * Q + a; if (inS[i]) s_rem(i); }
        sig[p] = 1 + rnd() % 10; gl[p] = rnd() % Q; hl[p] = rnd() % Q;
        rebuild_fiber(p);
        for (int a = 0; a < Q; a++) { int i = p * Q + a; int s = 0; for (int k = 0; k < ssz; k++) s += M[S[k]][i]; cnt[i] = s; }
        moves++;
        int ok = tabu_k(m, 1000);
        if (ok) {
            accepted++;
            int ok2 = tabu_k(m + 1, 3000);
            if (ok2) { m = m + 1; plus++; }
            else {
                /* restore a valid size-m set: rebuild from the solution found at size m is not stored, so retry m */
                int okb = tabu_k(m, 1000);
                if (!okb) { /* fall back: revert */
                    while (ssz) s_rem(S[0]);
                    sig[p] = oldsig; gl[p] = oldg; hl[p] = oldh; rebuild_fiber(p);
                    for (int k = 0; k < oldsz; k++) s_add(oldS[k]);
                }
            }
            if (m > bestm) { bestm = m; write_sol(argv[4], m); fprintf(stderr, "cpu %.1f moves %ld new best m=%d\n", cpu(), moves, m); }
        } else {
            /* rare downhill move (size m-1) to leave the plateau */
            if (m > 1 && rnd() % 64 == 0 && tabu_k(m - 1, 1000)) { m = m - 1; downs++; accepted++; }
            else {
                while (ssz) s_rem(S[0]);
                sig[p] = oldsig; gl[p] = oldg; hl[p] = oldh; rebuild_fiber(p);
                for (int k = 0; k < oldsz; k++) s_add(oldS[k]);
            }
        }
        if (moves % 500 == 0) fprintf(stderr, "cpu %.1f moves %ld acc %ld m=%d best=%d\n", cpu(), moves, accepted, m, bestm);
    }
    /* final: write the best valid set (current S if valid) */
    { long cost = 0; for (int i = 0; i < ssz; i++) cost += cnt[S[i]]; if (cost == 0 && ssz > 0) { write_sol(argv[4], ssz); bestm = ssz; } }
    fprintf(stderr, "done moves %ld accepted %ld plus %ld downs %ld best %d\n", moves, accepted, plus, downs, bestm);
    printf("%d\n", bestm);
    return 0;
}
