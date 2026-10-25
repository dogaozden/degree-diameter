/* ils1.c: iterated local search for "1-defective" line sets of the generalized hexagon H(q). Two lines are adjacent
   when concurrent. A set S is valid when every line of S has at most one S-neighbour, and such a pair has both lines
   allowed (allow[]). Objective: |S| (a pair counts 2).
   Moves: forced insertion of a random line with few S-neighbours (its S-neighbours are removed, partners of removed
   singles are freed), greedy refill of the touched region (free lines first, then partners of single lines),
   (1,2)-type swaps (remove s, refill, keep if larger), ARW-style acceptance (a loss d is accepted with probability
   1/(1+d*gap), gap = best - current), restore of the best after a deep fall. Undo through a journal.
   usage: ils1 HEXBIN ALLOW START SECONDS SEED OUT */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>

static int q, Q1, NL, DG;
static int *LP, *PL, *NB;
static unsigned char *allow, *inS;
static int *kc, *sid, *lastT, *mk, *smk, *pos, *sol, *bestS, *cb, *tlist;
static int nS, cnt1, bestN, mkst = 1, smst = 1, ncb, ntl;
static int *jr, jlen, jcap;
static uint64_t rs;
static unsigned char *frozen;
static int freezeMode = 0;
static int PMAX = 1 << 30;   /* cap on the number of pairs (pairs cost hub constraints in the scorer) */

static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline double urand(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double wall(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }

/* add / remove without journal; cnt1 = number of S-lines with exactly one S-neighbour (pairs = cnt1/2) */
static void addv(int v) {
    int c = kc[v];
    if (c == 1) cnt1++;
    inS[v] = 1; pos[v] = nS; sol[nS++] = v;
    const int *nb = NB + (size_t)v * DG;
    for (int j = 0; j < DG; j++) {
        int u = nb[j];
        if (inS[u]) { int k = kc[u]; if (k == 0) cnt1++; else if (k == 1) cnt1--; }
        kc[u]++; sid[u] += v;
    }
}
static void remv(int v) {
    if (kc[v] == 1) cnt1--;
    inS[v] = 0;
    int p = pos[v]; int w = sol[--nS]; sol[p] = w; pos[w] = p;
    const int *nb = NB + (size_t)v * DG;
    for (int j = 0; j < DG; j++) {
        int u = nb[j];
        kc[u]--; sid[u] -= v;
        if (inS[u]) { int k = kc[u]; if (k == 1) cnt1++; else if (k == 0) cnt1--; }
    }
}
static inline void J_add(int v) { addv(v); if (jlen < jcap) jr[jlen++] = v * 2; }
static inline void J_rem(int v) { remv(v); if (jlen < jcap) jr[jlen++] = v * 2 + 1; }
static void undo_to(int j) {
    while (jlen > j) { int e = jr[--jlen]; int v = e >> 1; if (e & 1) addv(v); else remv(v); }
}
/* x not in S: may be inserted now? (no S-neighbour, or one single allowed partner) */
static inline int canIns(int x) {
    int c = kc[x];
    if (c == 0) return 1;
    if (c == 1) { int w = sid[x]; return allow[x] && allow[w] && kc[w] == 0 && cnt1 / 2 < PMAX; }
    return 0;
}
static inline void cadd(int x) { if (mk[x] != mkst) { mk[x] = mkst; cb[ncb++] = x; } }
static void shuffle(int *a, int n) { for (int i = n - 1; i > 0; i--) { int j = rnd() % (i + 1); int t = a[i]; a[i] = a[j]; a[j] = t; } }
/* greedy refill of the candidate buffer cb: free lines first, then partners of single lines */
static void refill(void) {
    shuffle(cb, ncb);
    for (int i = 0; i < ncb; i++) { int x = cb[i]; if (!inS[x] && kc[x] == 0) J_add(x); }
    for (int i = 0; i < ncb; i++) { int x = cb[i]; if (!inS[x] && kc[x] == 1 && canIns(x)) J_add(x); }
}
/* (1,2)-type move: remove s, refill its neighbourhood (and its partner's); keep if the size grows, else undo */
static int try_swap(int s) {
    if (freezeMode && frozen[s]) return 0;
    int j0 = jlen, n0 = nS;
    int p = (kc[s] == 1) ? sid[s] : -1;
    J_rem(s);
    mkst++; ncb = 0;
    const int *a = NB + (size_t)s * DG;
    for (int j = 0; j < DG; j++) cadd(a[j]);
    if (p >= 0) { const int *b = NB + (size_t)p * DG; for (int j = 0; j < DG; j++) cadd(b[j]); }
    refill();
    if (nS > n0) return 1;
    undo_to(j0);
    return 0;
}
static void restore_best(void) {
    while (nS) remv(sol[nS - 1]);
    jlen = 0;
    for (int i = 0; i < bestN; i++) addv(bestS[i]);
}
static int pick(void) {
    int bx = -1;
    for (int r = 0; r < 4; r++) {
        int y = (int)(rnd() % NL);
        if (inS[y] || kc[y] > 6) continue;
        if (bx < 0 || kc[y] < kc[bx] || (kc[y] == kc[bx] && lastT[y] < lastT[bx])) bx = y;
    }
    return bx;
}
static void save(const char *fn, const int *S, int n) {
    FILE *o = fopen(fn, "w"); if (!o) return;
    for (int i = 0; i < n; i++) fprintf(o, "%d\n", S[i]);
    fclose(o);
}
static int verify(const int *S, int n, int *pairs) {
    unsigned char *ins = calloc(NL, 1);
    for (int i = 0; i < n; i++) ins[S[i]] = 1;
    int bad = 0, pr = 0;
    for (int i = 0; i < n; i++) {
        int s = S[i], c = 0, w = -1;
        for (int j = 0; j < DG; j++) { int u = NB[(size_t)s * DG + j]; if (ins[u]) { c++; w = u; } }
        if (c > 1) bad++;
        else if (c == 1) { pr++; if (!allow[s] || !allow[w]) bad++; }
    }
    free(ins); *pairs = pr / 2; return bad;
}

int main(int argc, char **argv) {
    if (argc < 7) { fprintf(stderr, "usage: ils1 HEXBIN ALLOW START SECONDS SEED OUT [PMAX]\n"); return 1; }
    if (argc > 7 && strcmp(argv[7], "frozen") == 0) freezeMode = 1; else if (argc > 7) PMAX = atoi(argv[7]);
    frozen = calloc(NL, 1);
    FILE *f = fopen(argv[1], "rb"); if (!f) return 1;
    int hdr[3]; if (fread(hdr, 4, 3, f) != 3) return 1;
    q = hdr[0]; NL = hdr[1]; Q1 = q + 1; DG = q * Q1;
    LP = malloc(sizeof(int) * (size_t)NL * Q1);
    if (fread(LP, 4, (size_t)NL * Q1, f) != (size_t)NL * Q1) return 1;
    fclose(f);
    PL = malloc(sizeof(int) * (size_t)NL * Q1);
    int *c0 = calloc(NL, sizeof(int));
    for (int l = 0; l < NL; l++) for (int i = 0; i < Q1; i++) { int p = LP[(size_t)l * Q1 + i]; PL[(size_t)p * Q1 + c0[p]++] = l; }
    for (int p = 0; p < NL; p++) if (c0[p] != Q1) { fprintf(stderr, "bad incidence\n"); return 1; }
    free(c0);
    NB = malloc(sizeof(int) * (size_t)NL * DG);
    for (int l = 0; l < NL; l++) {
        int k = 0;
        for (int i = 0; i < Q1; i++) { int p = LP[(size_t)l * Q1 + i];
            for (int t = 0; t < Q1; t++) { int m = PL[(size_t)p * Q1 + t]; if (m != l) NB[(size_t)l * DG + k++] = m; } }
        if (k != DG) { fprintf(stderr, "degree\n"); return 1; }
    }
    allow = calloc(NL, 1);
    { FILE *g = fopen(argv[2], "r"); int e; while (fscanf(g, "%d", &e) == 1) allow[e] = 1; fclose(g); }
    inS = calloc(NL, 1); kc = calloc(NL, sizeof(int)); sid = calloc(NL, sizeof(int)); lastT = calloc(NL, sizeof(int));
    mk = calloc(NL, sizeof(int)); smk = calloc(NL, sizeof(int)); pos = malloc(sizeof(int) * NL); sol = malloc(sizeof(int) * NL);
    bestS = malloc(sizeof(int) * NL); cb = malloc(sizeof(int) * (NL + 4096)); tlist = malloc(sizeof(int) * (NL + 4096));
    jcap = 1 << 22; jr = malloc(sizeof(int) * jcap); jlen = 0;
    double secs = atof(argv[4]);
    rs = 0x9E3779B97F4A7C15ULL ^ ((uint64_t)atoll(argv[5]) * 0x2545F4914F6CDD1DULL); for (int i = 0; i < 10; i++) rnd();

    { FILE *g = fopen(argv[3], "r"); int e, bad = 0; while (fscanf(g, "%d", &e) == 1) { if (!inS[e] && canIns(e)) J_add(e); else bad++; } fclose(g);
      fprintf(stderr, "start: %d lines, %d skipped\n", nS, bad); }
    jlen = 0;
    if (freezeMode) { int np = 0; for (int i = 0; i < nS; i++) { int s = sol[i]; if (kc[s] == 1) { frozen[s] = 1; np++; } }
        PMAX = cnt1 / 2; fprintf(stderr, "freeze mode: %d paired lines frozen, pair cap %d\n", np, PMAX); }
    { int *perm = malloc(sizeof(int) * NL); for (int i = 0; i < NL; i++) perm[i] = i; shuffle(perm, NL);
      mkst++; ncb = NL; memcpy(cb, perm, sizeof(int) * NL); refill(); free(perm); jlen = 0; }
    fprintf(stderr, "greedy: %d\n", nS);
    for (int sw = 0; sw < 4; sw++) {
        int before = nS, n0 = nS;
        int *tmp = malloc(sizeof(int) * n0); memcpy(tmp, sol, sizeof(int) * n0);
        for (int i = 0; i < n0; i++) if (inS[tmp[i]]) try_swap(tmp[i]);
        free(tmp); jlen = 0;
        fprintf(stderr, "sweep %d: %d\n", sw, nS);
        if (nS == before) break;
    }
    bestN = nS; memcpy(bestS, sol, sizeof(int) * nS);
    { int pr; int bad = verify(bestS, bestN, &pr); fprintf(stderr, "start-verify: size %d pairs %d violations %d\n", bestN, pr, bad); }

    double t0 = wall(), lastp = 0; long it = 0; long nacc = 0;
    while (1) {
        it++;
        if ((it & 255) == 0) {
            double el = wall() - t0;
            if (el > secs) break;
            if (el - lastp > 60) { lastp = el; int pr = cnt1 / 2;
                fprintf(stderr, "t=%.0f it=%ld cur=%d best=%d pairs=%d acc=%ld\n", el, it, nS, bestN, pr, nacc);
                save(argv[6], bestS, bestN); }
        }
        int x = pick(); if (x < 0) continue;
        if (freezeMode) { int bad = 0; const int *ay = NB + (size_t)x * DG; for (int j = 0; j < DG; j++) if (inS[ay[j]] && frozen[ay[j]]) { bad = 1; break; } if (bad) continue; }
        jlen = 0; int prevN = nS;
        mkst++; ncb = 0;
        const int *ax = NB + (size_t)x * DG;
        for (int j = 0; j < DG; j++) {
            int u = ax[j];
            if (!inS[u]) continue;
            int pu = (kc[u] == 1) ? sid[u] : -1;
            J_rem(u);
            const int *au = NB + (size_t)u * DG;
            for (int t = 0; t < DG; t++) cadd(au[t]);
            if (pu >= 0) { const int *ap = NB + (size_t)pu * DG; for (int t = 0; t < DG; t++) cadd(ap[t]); }
        }
        J_add(x);
        /* touched list = candidates plus x */
        ntl = ncb; memcpy(tlist, cb, sizeof(int) * ncb); tlist[ntl++] = x;
        refill();
        smst++;
        for (int i = 0; i < ntl; i++) {
            int t = tlist[i], s = -1;
            if (inS[t]) s = t; else if (kc[t] == 1) s = sid[t];
            if (s >= 0 && inS[s] && smk[s] != smst) { smk[s] = smst; try_swap(s); }
        }
        int accept;
        if (nS >= prevN) accept = 1;
        else { int delta = prevN - nS, gap = bestN - nS; accept = urand() < 1.0 / (1.0 + (double)delta * gap); }
        if (accept) {
            nacc++;
            for (int i = 0; i < jlen; i++) lastT[jr[i] >> 1] = (int)(it & 0x3fffffff);
            if (nS > bestN) { bestN = nS; memcpy(bestS, sol, sizeof(int) * nS); }
        } else undo_to(0);
        if (nS < bestN - 12) restore_best();
    }
    save(argv[6], bestS, bestN);
    { int pr; int bad = verify(bestS, bestN, &pr);
      fprintf(stderr, "final: best %d pairs %d violations %d iterations %ld\n", bestN, pr, bad, it);
      printf("best %d pairs %d violations %d iterations %ld\n", bestN, pr, bad, it);
      return bad ? 2 : 0; }
}
