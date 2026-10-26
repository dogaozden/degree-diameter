/* pairs.c (card c2, round r2-d11D5): systematic PAIRS of moves on a doubled-matching base.
   Cost = plusopt2.c total() (same walk model, copied).  Early abort per 64-source batch.
   Move1 (demand): sigma swaps of the preimage points p=sinv[T1], q=sinv[T2], flag swaps with a line end in {T1,T2}
     or a point end in {p,q}.  Generic mode (T1 < 0): Move1 touches the failing vertices of the input state.
   Move2: every sigma swap and every flag swap touching a vertex of a failing triple left by Move1 (flag second
     line l2 shares a point with l1).  A pair is kept only if it strictly beats the current cost.
   After a round the best pair is applied and the search repeats from the new failing set (greedy chain).
   usage: pairs base.in T1 T2 B1 SECS OUTPFX     (T1 T2 = -1 -1 for generic)
*/
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>

static int n, dg, V, nbatch;
static int *ln, *pt, *sig, *sinv, *stampL;
static int stampc = 0;
static uint64_t *R0, *F0, *N0;
static uint64_t *C1[6], *C2[6];
static int border[64];
#define FMAX 16384
static int rs_s[FMAX], rs_t[FMAX], rs_c[FMAX], rs_n, recording;

static long batch_cost(int bi) {
    int s0 = bi * 64;
    int ns = V - s0 < 64 ? V - s0 : 64;
    uint64_t full = ns == 64 ? ~0ULL : ((1ULL << ns) - 1);
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
            if (a0 | a1 | a2) {
                const int *nb = x < n ? pt + x * dg : ln + (x - n) * dg; int off = x < n ? n : 0;
                for (int j = 0; j < dg; j++) { uint64_t *y = N0 + (nb[j] + off) * 3; y[0] |= a0; y[1] |= a1; y[2] |= a2; }
            }
            a0 |= pu;
            if (x < n) { uint64_t *y = N0 + (n + sig[x]) * 3; y[1] |= a0; y[2] |= a1; y[0] |= a2; }
            else { uint64_t *y = N0 + sinv[x - n] * 3; y[2] |= a0; y[0] |= a1; y[1] |= a2; }
        }
        for (int i = 0; i < 3 * V; i++) R0[i] |= N0[i];
        uint64_t *tmp = F0; F0 = N0; N0 = tmp;
    }
    long c = 0;
    for (int t = 0; t < V; t++) {
        uint64_t ok0 = R0[t * 3] | C1[0][t] | C1[2][t] | C2[4][t] | C2[5][t];
        uint64_t m[3] = { full & ~ok0, full & ~R0[t * 3 + 1], full & ~R0[t * 3 + 2] };
        for (int cc = 0; cc < 3; cc++) {
            if (!m[cc]) continue;
            c += __builtin_popcountll(m[cc]);
            if (recording)
                for (uint64_t mm = m[cc]; mm; mm &= mm - 1)
                    if (rs_n < FMAX) { rs_s[rs_n] = s0 + __builtin_ctzll(mm); rs_t[rs_n] = t; rs_c[rs_n] = cc; rs_n++; }
        }
    }
    return c;
}
/* early abort: returns the exact cost when it is <= bound, otherwise some value > bound */
static long total_b(long bound) {
    long c = 0;
    for (int i = 0; i < nbatch; i++) { c += batch_cost(border[i]); if (c > bound) return c; }
    return c;
}
static long total_full(void) {
    long c = 0; rs_n = 0; recording = 1;
    for (int i = 0; i < nbatch; i++) c += batch_cost(border[i]);
    recording = 0; return c;
}
static void set_order(void) {   /* batches holding failing sources first (more likely to abort early) */
    int hot[64] = {0}, k = 0;
    for (int i = 0; i < rs_n; i++) hot[rs_s[i] / 64] = 1;
    for (int b = 0; b < nbatch; b++) if (hot[b]) border[k++] = b;
    for (int b = 0; b < nbatch; b++) if (!hot[b]) border[k++] = b;
}

typedef struct { int type, a, b, c, d; } Move;   /* type 0: sig_swap(a,b); type 1: flag_swap(line a, pos b, line c, pos d) */
static int has(const int *a, int v) { for (int j = 0; j < dg; j++) if (a[j] == v) return 1; return 0; }
static void repl(int *a, int from, int to) { for (int j = 0; j < dg; j++) if (a[j] == from) { a[j] = to; return; } }
static void sig_swap(int a, int b) { int la = sig[a], lb = sig[b]; sig[a] = lb; sig[b] = la; sinv[lb] = a; sinv[la] = b; }
static void flag_swap(int l1, int k1, int l2, int k2) {
    int p1 = ln[l1 * dg + k1], p2 = ln[l2 * dg + k2];
    ln[l1 * dg + k1] = p2; ln[l2 * dg + k2] = p1;
    repl(pt + p1 * dg, l1, l2); repl(pt + p2 * dg, l2, l1);
}
static void apply_mv(Move m) { if (m.type == 0) sig_swap(m.a, m.b); else flag_swap(m.a, m.b, m.c, m.d); }  /* involution */
static int flag_ok(int l1, int k1, int l2, int k2) {
    if (l1 == l2) return 0;
    int p1 = ln[l1 * dg + k1], p2 = ln[l2 * dg + k2];
    if (p1 == p2) return 0;
    return !has(ln + l2 * dg, p1) && !has(ln + l1 * dg, p2);
}
static void show(Move m, char *buf) {
    if (m.type == 0) sprintf(buf, "sig(%d,%d)", m.a, m.b);
    else sprintf(buf, "flag(L%d.%d<->L%d.%d)", m.a, m.b, m.c, m.d);
}

/* demand Move1 list around lines T1,T2 (preimage points p,q) */
static int gen_demand(int T1, int T2, Move *out, int cap) {
    int cnt = 0, X[2] = { sinv[T1], sinv[T2] }, Lt[2] = { T1, T2 };
    for (int xi = 0; xi < 2; xi++) for (int b = 0; b < n; b++) if (b != X[xi] && cnt < cap) out[cnt++] = (Move){ 0, X[xi], b, 0, 0 };
    for (int li = 0; li < 2; li++) for (int k1 = 0; k1 < dg; k1++) for (int l2 = 0; l2 < n; l2++) for (int k2 = 0; k2 < dg; k2++)
        if (cnt < cap && flag_ok(Lt[li], k1, l2, k2)) out[cnt++] = (Move){ 1, Lt[li], k1, l2, k2 };
    for (int xi = 0; xi < 2; xi++) for (int j = 0; j < dg; j++) {
        int l1 = pt[X[xi] * dg + j], k1 = 0; while (ln[l1 * dg + k1] != X[xi]) k1++;
        for (int l2 = 0; l2 < n; l2++) for (int k2 = 0; k2 < dg; k2++)
            if (cnt < cap && flag_ok(l1, k1, l2, k2)) out[cnt++] = (Move){ 1, l1, k1, l2, k2 };
    }
    return cnt;
}
/* local Move list touching vertices W (points < n, lines >= n) */
static int gen_touch(const int *W, int nW, Move *out, int cap) {
    int cnt = 0;
    for (int wi = 0; wi < nW; wi++) {
        int w = W[wi], a = w < n ? w : sinv[w - n];
        for (int b = 0; b < n && cnt < cap; b++) if (b != a) out[cnt++] = (Move){ 0, a, b, 0, 0 };
        for (int j = 0; j < dg; j++) {
            int l1, k1 = 0;
            if (w < n) { l1 = pt[w * dg + j]; while (ln[l1 * dg + k1] != w) k1++; }
            else { l1 = w - n; k1 = j; }
            stampc++; stampL[l1] = stampc;
            int L2[128], nl = 0;
            for (int k = 0; k < dg; k++) { int q = ln[l1 * dg + k];
                for (int i2 = 0; i2 < dg; i2++) { int l2 = pt[q * dg + i2]; if (stampL[l2] != stampc) { stampL[l2] = stampc; L2[nl++] = l2; } } }
            for (int i2 = 0; i2 < nl; i2++) for (int k2 = 0; k2 < dg; k2++)
                if (cnt < cap && flag_ok(l1, k1, L2[i2], k2)) out[cnt++] = (Move){ 1, l1, k1, L2[i2], k2 };
        }
    }
    return cnt;
}
static void save_state(const char *fn) {
    FILE *g = fopen(fn, "w"); if (!g) return; fprintf(g, "%d %d\n", n, dg);
    for (int l = 0; l < n; l++) for (int k = 0; k < dg; k++) fprintf(g, "%d%c", ln[l * dg + k], k == dg - 1 ? '\n' : ' ');
    for (int p = 0; p < n; p++) fprintf(g, "%d\n", sig[p]);
    fclose(g);
}
static double now(void) { return (double)clock() / CLOCKS_PER_SEC; }
static int W_from_rs(int *W) {   /* distinct vertices of the recorded failing triples */
    static int mark[1 << 12]; static int stampw = 0; stampw++; int nW = 0;
    for (int i = 0; i < rs_n; i++) for (int e = 0; e < 2; e++) {
        int v = e ? rs_t[i] : rs_s[i];
        if (mark[v] != stampw) { mark[v] = stampw; W[nW++] = v; }
    }
    return nW;
}

int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: pairs base.in T1 T2 B1 SECS [OUTPFX]\n"); return 1; }
    FILE *f = fopen(argv[1], "r"); if (!f || fscanf(f, "%d %d", &n, &dg) != 2) return 1; V = 2 * n;
    ln = malloc(4L * n * dg); for (int i = 0; i < n * dg; i++) if (fscanf(f, "%d", &ln[i]) != 1) return 1;
    sig = malloc(4L * n); sinv = malloc(4L * n); for (int i = 0; i < n; i++) if (fscanf(f, "%d", &sig[i]) != 1) return 1; fclose(f);
    for (int i = 0; i < n; i++) sinv[sig[i]] = i;
    pt = malloc(4L * n * dg); int *fill = calloc(n, 4);
    for (int l = 0; l < n; l++) for (int k = 0; k < dg; k++) { int p = ln[l * dg + k]; pt[p * dg + fill[p]++] = l; }
    stampL = calloc(n, sizeof(int));
    R0 = malloc(24L * V); F0 = malloc(24L * V); N0 = malloc(24L * V);
    for (int d = 0; d < 6; d++) { C1[d] = malloc(8L * V); C2[d] = malloc(8L * V); }
    nbatch = (V + 63) / 64; for (int b = 0; b < nbatch; b++) border[b] = b;
    int T1 = atoi(argv[2]), T2 = atoi(argv[3]); long B1 = atol(argv[4]); double SECS = atof(argv[5]);
    const char *OUT = argc > 6 ? argv[6] : "pairs_out";
    long cur = total_full(); set_order();
    printf("start cost=%ld  T1=%d T2=%d B1=%ld SECS=%.0f\n", cur, T1, T2, B1, SECS); fflush(stdout);
    if (cur == 0) { char fn[512]; sprintf(fn, "%s_0.in", OUT); save_state(fn); printf("ALREADY 0\n"); return 0; }
    long cap = 400000, cap2 = 400000;
    Move *M1 = malloc(sizeof(Move) * cap), *M2 = malloc(sizeof(Move) * cap2);
    int W[4096];
    int round = 0; double t_start = now();
    while (cur > 0 && now() - t_start < SECS) {
        int nW0 = W_from_rs(W);
        int nM1 = (round == 0 && T1 >= 0) ? gen_demand(T1, T2, M1, cap) : gen_touch(W, nW0, M1, cap);
        long bestc = cur; Move bm1 = {0}, bm2 = {0}; int have = 0;
        long hist[64] = {0}; long n1ok = 0, n2eval = 0; int stop = 0;
        printf("round %d: cost=%ld  failing vertices=%d  M1=%d\n", round, cur, nW0, nM1); fflush(stdout);
        for (int i1 = 0; i1 < nM1 && !stop; i1++) {
            if ((i1 & 1023) == 0 && now() - t_start > SECS) { stop = 1; break; }
            Move m1 = M1[i1];
            apply_mv(m1);
            long c1 = total_b(B1);
            if (c1 <= B1) {
                c1 = total_full(); set_order(); n1ok++;
                hist[c1 < 63 ? c1 : 63]++;
                if (c1 == 0) { char fn[512]; sprintf(fn, "%s_0.in", OUT); save_state(fn); printf("FOUND cost 0 with one move\n"); return 0; }
                int nW = W_from_rs(W);
                int nM2 = getenv("NOM2") ? 0 : gen_touch(W, nW, M2, cap2);
                for (int i2 = 0; i2 < nM2; i2++) {
                    apply_mv(M2[i2]);
                    long c2 = total_b(bestc - 1);
                    n2eval++;
                    if (c2 < bestc) {
                        bestc = c2; bm1 = m1; bm2 = M2[i2]; have = 1;
                        char s1[64], s2[64]; show(m1, s1); show(M2[i2], s2);
                        printf("  new best pair cost=%ld : %s then %s  (c1=%ld)\n", c2, s1, s2, c1); fflush(stdout);
                        if (c2 == 0) {
                            char fn[512]; sprintf(fn, "%s_0.in", OUT); save_state(fn);
                            printf("FOUND cost 0\n"); fflush(stdout); return 0;
                        }
                    }
                    apply_mv(M2[i2]);   /* undo (involution) */
                    if (now() - t_start > SECS) { stop = 1; break; }
                }
            }
            apply_mv(m1);   /* undo */
        }
        printf("round %d done: M1 ok(c1<=%ld)=%ld  M2 evals=%ld  best=%ld  hist c1:", round, B1, n1ok, n2eval, have ? bestc : cur);
        for (int h = 0; h < 64; h++) if (hist[h]) printf(" %d:%ld", h, hist[h]);
        printf("  t=%.0f\n", now() - t_start); fflush(stdout);
        if (getenv("NOM2")) { for (int h = 0; h < 64; h++) if (hist[h]) printf(" hist %d:%ld", h, hist[h]); printf("\n"); break; }
        if (!have) break;
        /* adopt the best pair and continue the greedy chain */
        apply_mv(bm1); apply_mv(bm2);
        cur = total_full(); set_order();
        char s1[64], s2[64]; show(bm1, s1); show(bm2, s2);
        printf("ADOPT %s then %s -> cost %ld\n", s1, s2, cur); fflush(stdout);
        char fn[512]; sprintf(fn, "%s_%ld.in", OUT, cur); save_state(fn);
        round++;
        T1 = -1;   /* later rounds are generic */
    }
    printf("END cost=%ld rounds=%d t=%.0f\n", cur, round, now() - t_start);
    return 0;
}
