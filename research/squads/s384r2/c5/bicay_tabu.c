/* bicay_tabu.c: tabu search over bi-Cayley graphs BiCay(G; R, L, S) (same model and cost as bicay.c, from squad-6-5).
 *
 * G a group with an index-2 subgroup E (parity 0 on E, 1 off E). Vertices (g,i), g in G, i in {0,1}.
 * Edges (g,0)~(r g,0) for r in R; (g,1)~(l g,1) for l in L; (g,0)~(s g,1) for s in S.
 * S = {1} u (a-1 further elements of E); R, L = inverse-closed subsets of G \ E of size b, i.e. unions of classes
 * {x, x^-1} (size 2) and odd involutions (size 1). The graph is (a+b)-regular on 2|G| vertices.
 * Cost = (2|G| - #vertices within distance D of (1,0)) + (same for (1,1)); cost 0 <=> diameter <= D (right
 * multiplication is an automorphism). The (5,5) record on 360 vertices is a=2, b=3 on S3 x D30.
 *
 * Tabu search. Neighbourhood of one step: S: replace S[i] (i >= 1) by an even element not in S; R: replace one
 * class of R by a class of the same size not in R (so |R| = b is kept); L: the same for L. Every neighbour is
 * evaluated; the best admissible one is taken even if it is worse. A move makes the removed element (S) or class
 * (R, L) tabu for re-entry for TMIN..TMAX steps; a tabu move is still allowed if it gives a new global best.
 * After STALL steps without a new global best, the search restarts from the best state with KICK random moves
 * and an empty tabu list. Stops at cost 0 or after SECS seconds.
 *
 * usage: bicay_tabu GROUPFILE [EDGES]
 *   GROUPFILE: m; m rows of the multiplication table (element 0 = identity, row g col h = index of g*h);
 *   one row of parities (0 = in E, 1 = outside). Written by export_bc.g.
 *   env: A (|S|, 2), B (|R| = |L|, 4), D (5), SECS (60), SEED (1), TMIN (5), TMAX (12), STALL (1500), KICK (3)
 * stdout: "RESULT best <cost> steps <n> restarts <r> secs <t>" and, if cost 0, "SOL S .. | R .. | L .." (EDGES is then
 *   written as an edge list for apsp: first line 2|G|, then one "u v" per edge, side 0 vertex g, side 1 vertex m+g).
 * stderr: "best <cost> step <n> t <secs>" for each new global best.
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXM 1024
#define MAXS 16
#define INF (1 << 30)
static int m, D = 5, a = 2, b = 4;
static uint16_t *mul;
static int inv_[MAXM], par[MAXM];
#define MUL(x, y) mul[(size_t)(x) * m + (y)]
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline int rndi(int n) { return (int)(rnd() % (uint64_t)n); }

/* classes of odd elements: pairs {x, x^-1} (size 2) and odd involutions (size 1) */
static int ncls, cls[MAXM][2], clsz[MAXM];
static int pc[MAXM], npc, ic[MAXM], nic;
static int even[MAXM], neven;

/* state: S[0] = identity; Rc/Lc = class indices with total size b */
static int S[MAXS], Rc[MAXS], nRc, Lc[MAXS], nLc;
static int R[MAXS], nR, L[MAXS], nL;
static void expand(const int *C, int n, int *X, int *nX) {
    int k = 0; for (int i = 0; i < n; i++) for (int u = 0; u < clsz[C[i]]; u++) X[k++] = cls[C[i]][u];
    *nX = k;
}
static void rebuild(void) { expand(Rc, nRc, R, &nR); expand(Lc, nLc, L, &nL); }

/* ---- evaluation (as bicay.c) ---- */
static int dist_[2 * MAXM], stamp_[2 * MAXM], stampv = 0, q_[2 * MAXM];
static int reach_from(int o) {      /* number of vertices within distance D of (1, o) */
    stampv++;
    int h = 0, t = 0, v0 = o * m;
    stamp_[v0] = stampv; dist_[v0] = 0; q_[t++] = v0;
    while (h < t) {
        int v = q_[h++], d = dist_[v]; if (d == D) continue;
        int g = v < m ? v : v - m, i = v >= m;
        int nb[2 * MAXS], k = 0;
        if (!i) { for (int j = 0; j < nR; j++) nb[k++] = MUL(R[j], g); for (int j = 0; j < a; j++) nb[k++] = m + MUL(S[j], g); }
        else { for (int j = 0; j < nL; j++) nb[k++] = m + MUL(L[j], g); for (int j = 0; j < a; j++) nb[k++] = MUL(inv_[S[j]], g); }
        for (int j = 0; j < k; j++) { int w = nb[j]; if (stamp_[w] != stampv) { stamp_[w] = stampv; dist_[w] = d + 1; q_[t++] = w; } }
    }
    return t;
}
static int cost(void) { return (2 * m - reach_from(0)) + (2 * m - reach_from(1)); }

/* ---- moves ---- */
typedef struct { int type, slot, val, old; } move_t;   /* type 0: S, 1: R class, 2: L class */
static move_t mv_[1 << 16]; static int nmv;
static long tabu_S[MAXM], tabu_Rc[MAXM], tabu_Lc[MAXM];
static int in_arr(int x, const int *A, int n) { for (int i = 0; i < n; i++) if (A[i] == x) return 1; return 0; }
static void apply(move_t mv) {
    if (mv.type == 0) S[mv.slot] = mv.val;
    else if (mv.type == 1) { Rc[mv.slot] = mv.val; expand(Rc, nRc, R, &nR); }
    else { Lc[mv.slot] = mv.val; expand(Lc, nLc, L, &nL); }
}
static void add_class_moves(int type, const int *C, int n) {
    for (int i = 0; i < n; i++) {
        const int *pool = clsz[C[i]] == 2 ? pc : ic; int np = clsz[C[i]] == 2 ? npc : nic;
        for (int k = 0; k < np; k++) if (!in_arr(pool[k], C, n)) { move_t mv = {type, i, pool[k], C[i]}; mv_[nmv++] = mv; }
    }
}
static void gen_moves(void) {
    nmv = 0;
    for (int i = 1; i < a; i++) for (int k = 0; k < neven; k++) if (!in_arr(even[k], S, a)) { move_t mv = {0, i, even[k], S[i]}; mv_[nmv++] = mv; }
    add_class_moves(1, Rc, nRc);
    add_class_moves(2, Lc, nLc);
}
static void rand_move(move_t *mv) {       /* a uniformly random move (used for kicks); no move if none exists */
    gen_moves();
    if (nmv) *mv = mv_[rndi(nmv)];
}
static long tabu_of(move_t mv) { return mv.type == 0 ? tabu_S[mv.val] : mv.type == 1 ? tabu_Rc[mv.val] : tabu_Lc[mv.val]; }
static void set_tabu(move_t mv, long until) {  /* the old value may not come back */
    if (mv.type == 0) tabu_S[mv.old] = until; else if (mv.type == 1) tabu_Rc[mv.old] = until; else tabu_Lc[mv.old] = until;
}
/* random class set of total size b (k2 pairs, b-2k2 involutions) */
static void rand_set(int *C, int *nC) {
    for (;;) {
        int k2 = rndi(b / 2 + 1), k1 = b - 2 * k2;
        if (k2 > npc || k1 > nic) continue;
        static int used[MAXM]; memset(used, 0, sizeof used);
        int n = 0;
        for (int i = 0; i < k2;) { int c = pc[rndi(npc)]; if (!used[c]) { used[c] = 1; C[n++] = c; i++; } }
        for (int i = 0; i < k1;) { int c = ic[rndi(nic)]; if (!used[c]) { used[c] = 1; C[n++] = c; i++; } }
        *nC = n; return;
    }
}
static int feasible_b(void) { for (int k2 = 0; k2 <= b / 2; k2++) if (k2 <= npc && b - 2 * k2 <= nic) return 1; return 0; }

static int getenv_int(const char *k, int def) { const char *s = getenv(k); return s ? atoi(s) : def; }

int main(int argc, char **argv) {
    if (argc < 2) { fprintf(stderr, "usage: bicay_tabu GROUPFILE [EDGES]\n"); return 2; }
    a = getenv_int("A", 2); b = getenv_int("B", 4); D = getenv_int("D", 5);
    double SECS = getenv("SECS") ? atof(getenv("SECS")) : 60;
    int TMIN = getenv_int("TMIN", 5), TMAX = getenv_int("TMAX", 12), STALL = getenv_int("STALL", 1500), KICK = getenv_int("KICK", 3);
    if (getenv("SEED")) { rs ^= (uint64_t)atoll(getenv("SEED")) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 20; i++) rnd(); }
    if (a < 1 || a > MAXS || b < 1 || 2 * b > MAXS) { fprintf(stderr, "bad A/B\n"); return 2; }
    FILE *f = fopen(argv[1], "r"); if (!f || fscanf(f, "%d", &m) != 1 || m > MAXM) return 2;
    mul = malloc(sizeof(uint16_t) * (size_t)m * m);
    for (long i = 0; i < (long)m * m; i++) { int x; if (fscanf(f, "%d", &x) != 1) return 2; mul[i] = x; }
    for (int i = 0; i < m; i++) if (fscanf(f, "%d", &par[i]) != 1) return 2;
    fclose(f);
    for (int i = 0; i < m; i++) for (int j = 0; j < m; j++) if (MUL(i, j) == 0) inv_[i] = j;

    /* classes */
    int seen[MAXM]; memset(seen, 0, sizeof seen);
    for (int g = 0; g < m; g++) if (par[g] && !seen[g]) {
        int h = inv_[g]; cls[ncls][0] = g; cls[ncls][1] = h; clsz[ncls] = h == g ? 1 : 2;
        seen[g] = seen[h] = 1;
        if (clsz[ncls] == 2) pc[npc++] = ncls; else ic[nic++] = ncls;
        ncls++; }
    for (int g = 1; g < m; g++) if (!par[g]) even[neven++] = g;
    if (!feasible_b()) { printf("RESULT error no inverse-closed odd set of size %d (pairs %d, involutions %d)\n", b, npc, nic); return 0; }

    /* state: random start */
    S[0] = 0;
    for (int i = 1; i < a; i++) { int x; do x = even[rndi(neven)]; while (in_arr(x, S, i)); S[i] = x; }
    rand_set(Rc, &nRc); rand_set(Lc, &nLc); rebuild();
    int cur = cost();
    int bestAll = cur, bS[MAXS], bRc[MAXS], bLc[MAXS], bnR = nRc, bnL = nLc;
    memcpy(bS, S, sizeof S); memcpy(bRc, Rc, sizeof Rc); memcpy(bLc, Lc, sizeof Lc);
    double t0 = now(); long step = 0, lastImp = 0; int restarts = 0;
    fprintf(stderr, "m=%d a=%d b=%d D=%d: %d odd classes (%d pairs, %d involutions), %d even non-identity; start cost %d\n",
            m, a, b, D, ncls, npc, nic, neven, cur);
    while (bestAll > 0 && now() - t0 < SECS) {
        step++;
        gen_moves();
        int bc = INF, nt = 0, pick = -1;
        for (int k = 0; k < nmv; k++) {
            move_t mv = mv_[k];
            move_t back = {mv.type, mv.slot, mv.old, mv.val};
            apply(mv); int c = cost(); apply(back);
            int tabu = tabu_of(mv) > step;
            if (tabu && c >= bestAll) continue;
            if (c < bc) { bc = c; nt = 1; pick = k; }
            else if (c == bc) { nt++; if (rndi(nt) == 0) pick = k; }
        }
        if (pick < 0) { if (!nmv) break; pick = rndi(nmv); bc = INF; }
        move_t mv = mv_[pick];
        set_tabu(mv, step + TMIN + rndi(TMAX - TMIN + 1));
        apply(mv);
        cur = bc < INF ? bc : cost();
        if (cur < bestAll) {
            bestAll = cur; lastImp = step;
            memcpy(bS, S, sizeof S); memcpy(bRc, Rc, sizeof Rc); memcpy(bLc, Lc, sizeof Lc); bnR = nRc; bnL = nLc;
            fprintf(stderr, "best %d step %ld t %.1f\n", bestAll, step, now() - t0);
        }
        if (step - lastImp > STALL) {   /* restart from the best state with random kicks, empty tabu list */
            restarts++; lastImp = step;
            memcpy(S, bS, sizeof S); memcpy(Rc, bRc, sizeof Rc); nRc = bnR; memcpy(Lc, bLc, sizeof Lc); nLc = bnL; rebuild();
            memset(tabu_S, 0, sizeof tabu_S); memset(tabu_Rc, 0, sizeof tabu_Rc); memset(tabu_Lc, 0, sizeof tabu_Lc);
            for (int k = 0; k < KICK; k++) { move_t km = {0, 0, 0, 0}; rand_move(&km); if (nmv) apply(km); }
        }
    }
    double secs = now() - t0;
    printf("RESULT best %d steps %ld restarts %d secs %.1f\n", bestAll, step, restarts, secs);
    if (bestAll == 0) {
        memcpy(S, bS, sizeof S); memcpy(Rc, bRc, sizeof Rc); nRc = bnR; memcpy(Lc, bLc, sizeof Lc); nLc = bnL; rebuild();
        printf("SOL S"); for (int i = 0; i < a; i++) printf(" %d", S[i]);
        printf(" | R"); for (int i = 0; i < nR; i++) printf(" %d", R[i]);
        printf(" | L"); for (int i = 0; i < nL; i++) printf(" %d", L[i]); printf("\n");
        if (argc > 2) {
            FILE *o = fopen(argv[2], "w");
            if (o) {
                fprintf(o, "%d\n", 2 * m);
                for (int g = 0; g < m; g++) {
                    for (int j = 0; j < nR; j++) { int h = MUL(R[j], g); if (g < h) fprintf(o, "%d %d\n", g, h); }
                    for (int j = 0; j < nL; j++) { int h = MUL(L[j], g); if (g < h) fprintf(o, "%d %d\n", m + g, m + h); }
                    for (int j = 0; j < a; j++) fprintf(o, "%d %d\n", g, m + MUL(S[j], g));
                }
                fclose(o);
            }
        }
    }
    return 0;
}
