/* routecount2.c: route numbers for GEOMETRIC labellings of Gomez's Omega H_q, any reading of Fig. 2.21a/b
   (OMEGA_REPAIR.md, Theorem 3.3).  A labelling is geometric when every transfer map (mark of hub row t in one copy ->
   mark of the same hub in another copy) is the restriction of an automorphism of the incidence graph I(H(q))
   (a collineation, or a duality when q = 3^e).  Then a route reaches exactly a ball B(z, R) of the target copy, R the
   largest admissible total segment length; the centre z has the target type iff R is even.

   Per block: type a/b and inner class P/L (reading 2 = inner P on a-blocks, L on b-blocks; reading 1 = inner L).
   For each hub class X and copy c' it misses, the routes give centres with radii 4,3,2,1,0.  Taking one radius-4 centre
   as reference t, the points opposite t that no route reaches number at least
        q^5 - (m4 - 1) q^4 - m3 q^3 - m2 q^2 - m1 q - m0                         (Lemma 3.1)
   and this is printed for the best (X, c').  Every pattern of the given length is tried (blocks are interchangeable,
   so a pattern is a multiset of the four block kinds aP, aL, bP, bL).
   usage: routecount2 q A [reading]   reading: all (default) | 1 | 2 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>

static int A, C;
static char btype[64], binner[64];
static int att[64][10];   /* att[c][X] = 0 not attached, 1 attached at points, 2 attached at lines */

static void wiring(void) {
    memset(att, 0, sizeof att);
    for (int B = 0; B < A; B++) for (int k = 0; k < 5; k++) {
        int a = btype[B] == 'a';
        int u1 = a ? k + 4 : k + 3, u2 = a ? k + 1 : k + 4;     /* unbarred k */
        int b1 = a ? k + 2 : k + 4, b2 = a ? k + 3 : k + 1;     /* barred k */
        int inner = binner[B] == 'P' ? 1 : 2, outer = 3 - inner;
        /* type a: unbarred on inner (star), barred on outer (arc); type b: unbarred on outer, barred on inner */
        int tu = a ? inner : outer, tb = a ? outer : inner;
        att[5 * B + u1 % 5][k] = att[5 * B + u2 % 5][k] = tu;
        att[5 * B + b1 % 5][5 + k] = att[5 * B + b2 % 5][5 + k] = tb;
    }
}
/* Symbolic centres.  A geometric labelling is P_c = a_c P_0, L_c = b_c L_0 with collineations a_c, b_c and, when some
   transfer joins points to lines (reading 1), L_0 P_0^-1 = delta|points for a duality delta (Lemma 3.0).  The transfer
   through class Y from copy c (mark type s) to copy d (mark type s') is g(d,s') delta^e g(c,s)^-1 with g(c,P) = a_c,
   g(c,L) = b_c, e = 0 if s = s', +1 if (s,s') = (P,L), -1 if (L,P).  The centre of a route is W(P_0 t) with
   W = T_{r-1} ... T_1 g(c1,s1) delta^[s1 = L].  W is kept as a freely reduced word; routes with the same reduced word
   have the same centre (different words may still coincide, which only lowers the true coverage). */
typedef struct { int w[16]; int len; int R; } Cen;
static Cen cen[64][8192]; static int ncen[64];
static int W[32], wl;     /* W[0] is applied last (leftmost) */
#define SYM(c, s) (2 * (c) + (s))          /* s: 0 = P, 1 = L */
#define DELTA 1000
static void add(int cp, int R) {
    for (int i = 0; i < ncen[cp]; i++) if (cen[cp][i].len == wl && !memcmp(cen[cp][i].w, W, sizeof(int) * wl)) {
        if (R > cen[cp][i].R) cen[cp][i].R = R; return; }
    if (ncen[cp] >= 8192) { fprintf(stderr, "too many centres\n"); exit(1); }
    Cen *e = &cen[cp][ncen[cp]++]; memcpy(e->w, W, sizeof(int) * wl); e->len = wl; e->R = R;
}
/* letters: 2*sym + inv */
static int saveW[64][32], savel[64];
static void push_left(int letter) {      /* W <- letter * W, freely reduced */
    if (wl > 0 && (W[0] ^ 1) == letter) { memmove(W, W + 1, sizeof(int) * (wl - 1)); wl--; return; }
    memmove(W + 1, W, sizeof(int) * wl); W[0] = letter; wl++;
}
static int srcX;
static void dfs(int c, int tin, int Yin, int used, int minseg, int r) {
    if (!att[c][srcX]) {
        int tt = 0; for (int Y = (srcX < 5 ? 0 : 5); Y < (srcX < 5 ? 5 : 10); Y++) if (att[c][Y]) tt = att[c][Y];
        int last = tin != tt, budget = 7 - used, par = (minseg + last) & 1, R = budget;
        if ((R & 1) != par) R--;
        if (R >= minseg + last && R >= 0) add(c, R);
    }
    if (r == 4) return;
    for (int Y = 0; Y < 10; Y++) if (att[c][Y]) {
        int tY = att[c][Y], seg = tin != tY;
        if (seg == 0 && Y == Yin) seg = 2;
        if (used + 2 + minseg + seg > 7) continue;
        for (int d = 0; d < C; d++) if (d != c && att[d][Y]) {
            memcpy(saveW[r], W, sizeof(int) * wl); savel[r] = wl;
            int s = att[c][Y] - 1, s2 = att[d][Y] - 1;
            push_left(2 * SYM(c, s) + 1);                    /* g(c,s)^-1 */
            if (s != s2) push_left(2 * DELTA + (s == 1));    /* delta (P->L) or delta^-1 (L->P) */
            push_left(2 * SYM(d, s2));                       /* g(d,s') */
            dfs(d, att[d][Y], Y, used + 2, minseg + seg, r + 1);
            memcpy(W, saveW[r], sizeof(int) * savel[r]); wl = savel[r];
        }
    }
}
static double bestbound(int q, int *m4, int *m2) {
    double Q = q, best = -1e30;
    for (int X = 0; X < 10; X++) {
        memset(ncen, 0, sizeof ncen); srcX = X;
        for (int c1 = 0; c1 < C; c1++) if (att[c1][X]) { wl = 0; int s1 = att[c1][X] - 1; if (s1) push_left(2 * DELTA); push_left(2 * SYM(c1, s1)); dfs(c1, att[c1][X], X, 1, 0, 1); }
        for (int cp = 0; cp < C; cp++) if (!att[cp][X]) {
            int m[5] = {0}; for (int i = 0; i < ncen[cp]; i++) m[cen[cp][i].R]++;
            if (!m[4]) continue;
            double s = pow(Q, 5) - (m[4] - 1) * pow(Q, 4) - m[3] * pow(Q, 3) - m[2] * Q * Q - m[1] * Q - m[0];
            if (s > best) { best = s; *m4 = m[4]; *m2 = m[2]; }
        }
    }
    return best;
}
int main(int argc, char **argv) {
    if (!strcmp(argv[1], "starved")) {      /* reading 2: pairs with exactly alpha twisted radius-4 centres, per bar, max m2 */
        int q = atoi(argv[2]); A = atoi(argv[3]); C = 5 * A; (void)q;
        for (int na = 0; na <= A; na++) {
            for (int B = 0; B < A; B++) { btype[B] = B < na ? 'a' : 'b'; binner[B] = B < na ? 'P' : 'L'; } btype[A] = binner[A] = 0;
            wiring(); int cnt[2] = {0, 0}, mx[2] = {0, 0};
            for (int X = 0; X < 10; X++) {
                memset(ncen, 0, sizeof ncen); srcX = X;
                for (int c1 = 0; c1 < C; c1++) if (att[c1][X]) { wl = 0; int s1 = att[c1][X] - 1; if (s1) push_left(2 * DELTA); push_left(2 * SYM(c1, s1)); dfs(c1, att[c1][X], X, 1, 0, 1); }
                for (int cp = 0; cp < C; cp++) if (!att[cp][X]) { int m[5] = {0};
                    for (int i = 0; i < ncen[cp]; i++) m[cen[cp][i].R]++;
                    if (m[4] == A + 1) { int b = X >= 5; cnt[b]++; if (m[2] > mx[b]) mx[b] = m[2]; } }
            }
            printf("q=%d a^%d b^%d: starved unbarred pairs %d (max m2 %d), starved barred pairs %d (max m2 %d)\n", q, na, A - na, cnt[0], mx[0], cnt[1], mx[1]);
        }
        return 0;
    }
    if (!strcmp(argv[1], "total")) {        /* reading 2: sum over all (X, c') of N * max(0, bound): far pairs, at least */
        int q = atoi(argv[2]); A = atoi(argv[3]); C = 5 * A; double Q = q, N = (pow(Q, 6) - 1) / (Q - 1);
        for (int na = 0; na <= A; na++) {
            for (int B = 0; B < A; B++) { btype[B] = B < na ? 'a' : 'b'; binner[B] = B < na ? 'P' : 'L'; } btype[A] = binner[A] = 0;
            wiring(); double tot = 0; int npos = 0, npairs = 0;
            for (int X = 0; X < 10; X++) {
                memset(ncen, 0, sizeof ncen); srcX = X;
                for (int c1 = 0; c1 < C; c1++) if (att[c1][X]) { wl = 0; int s1 = att[c1][X] - 1; if (s1) push_left(2 * DELTA); push_left(2 * SYM(c1, s1)); dfs(c1, att[c1][X], X, 1, 0, 1); }
                for (int cp = 0; cp < C; cp++) if (!att[cp][X]) { int m[5] = {0}; npairs++;
                    for (int i = 0; i < ncen[cp]; i++) m[cen[cp][i].R]++;
                    double s = pow(Q, 5) - (m[4] - 1) * pow(Q, 4) - m[3] * pow(Q, 3) - m[2] * Q * Q - m[1] * Q - m[0];
                    if (s > 0) { tot += s * N; npos++; } }
            }
            printf("q=%d types a^%d b^%d: %d of %d (hub class, missed copy) pairs have a positive bound; far pairs >= %.4g\n", q, na, A - na, npos, npairs, tot);
        }
        return 0;
    }
    if (!strcmp(argv[1], "sweep")) {
        for (int a = atoi(argv[2]); a <= atoi(argv[3]); a++) {
            A = a; C = 5 * A; double worst[2] = {1e30, 1e30}; int wk[2] = {0, 0}, w4[2], w2[2];
            for (int na = 0; na <= A; na++) {
                for (int B = 0; B < A; B++) { btype[B] = B < na ? 'a' : 'b'; binner[B] = B < na ? 'P' : 'L'; } btype[A] = binner[A] = 0;
                wiring();
                for (int e = 0; e < 2; e++) { int q = 2 * a - 3 + e, m4, m2; double b = bestbound(q, &m4, &m2);
                    if (b < worst[e]) { worst[e] = b; wk[e] = na; w4[e] = m4; w2[e] = m2; } }
            }
            for (int e = 0; e < 2; e++) printf("alpha=%d q=%d: worst pattern a^%d b^%d: m4=%d m2=%d, uncovered per hub >= %.0f %s\n",
                a, 2 * a - 3 + e, wk[e], a - wk[e], w4[e], w2[e], worst[e], worst[e] > 0 ? "IMPOSSIBLE" : "open");
            fflush(stdout);
        }
        return 0;
    }
    int q = atoi(argv[1]); A = atoi(argv[2]); C = 5 * A; const char *rd = argc > 3 ? argv[3] : "all";
    double Q = q;
    const char *kinds[4] = {"aP", "aL", "bP", "bL"};
    /* multisets: counts n0..n3 summing to A */
    for (int n0 = 0; n0 <= A; n0++) for (int n1 = 0; n0 + n1 <= A; n1++) for (int n2 = 0; n0 + n1 + n2 <= A; n2++) {
        int n3 = A - n0 - n1 - n2, cnt[4] = {n0, n1, n2, n3}, B = 0;
        for (int k = 0; k < 4; k++) for (int j = 0; j < cnt[k]; j++) { btype[B] = kinds[k][0]; binner[B] = kinds[k][1]; B++; }
        btype[A] = binner[A] = 0;
        int r2 = n1 == 0 && n2 == 0, r1 = n0 == 0 && n2 == 0;     /* reading 2: aP, bL only; reading 1: inner L only */
        if (!strcmp(rd, "1") && !r1) continue;
        if (!strcmp(rd, "2") && !r2) continue;
        wiring();
        double best = -1e30; int bX = -1, bc = -1, bm[5] = {0};
        for (int X = 0; X < 10; X++) {
            memset(ncen, 0, sizeof ncen); srcX = X;
            for (int c1 = 0; c1 < C; c1++) if (att[c1][X]) { wl = 0; int s1 = att[c1][X] - 1; if (s1) push_left(2 * DELTA); push_left(2 * SYM(c1, s1)); dfs(c1, att[c1][X], X, 1, 0, 1); }
            for (int cp = 0; cp < C; cp++) if (!att[cp][X]) {
                int m[5] = {0}; for (int i = 0; i < ncen[cp]; i++) m[cen[cp][i].R]++;
                double s;
                if (m[4] == 0) s = 1e30;   /* no radius-4 centre: count against the whole class instead */
                else s = pow(Q, 5) - (m[4] - 1) * pow(Q, 4) - m[3] * pow(Q, 3) - m[2] * Q * Q - m[1] * Q - m[0];
                if (s > best) { best = s; bX = X; bc = cp; memcpy(bm, m, sizeof m); }
            }
        }
        printf("q=%d blocks=", q); for (int b = 0; b < A; b++) printf("%c%c", btype[b], binner[b]);
        printf(" %s: best X=%d c'=%d m4..m0=%d,%d,%d,%d,%d  uncovered per hub >= %.0f%s\n", r2 ? "(reading 2)" : r1 ? "(reading 1)" : "", bX, bc,
               bm[4], bm[3], bm[2], bm[1], bm[0], best, best > 0 ? "  IMPOSSIBLE" : "");
    }
    return 0;
}
