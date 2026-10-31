/* lift3d.c (r3d): D5-symmetric polarity double covers.
   M = symmetric 0/1 matrix on m = t*k vertices (u,x) = u*t + x, x in Z_t (t odd, default 5); M has row sums 3
   (loop counts once). Symmetry group D5 = <tau, sigma>: tau: x -> x+1 (free), sigma: x -> -x (fixes (u,0)).
   Quotient description (sigma-invariant M):
     F-edge {u,v}   (voltage 0):  M[(u,x),(v,x)]  for all x.       Simple graph on the k base vertices.
     L1 at u        (voltage 0):  M[(u,x),(u,x)]  for all x (M-loop, uses 1 stub).
     T-link {u,v}, class g in 1..(t-1)/2 (u != v): M[(u,x),(v,x+g)] and M[(u,x),(v,x-g)] for all x.
     L2 at u, class g:            M[(u,x),(u,x+g)] and M[(u,x),(u,x-g)] for all x.
   Vertex types: u < A is type a (3 F-slots: F-edges + L1); u >= A is type b (1 F-slot + 1 T-slot: T-link or L2).
   The double cover G: A_i ~ B_j iff M_ij = 1 (i, j in 0..m-1), n = 2m.
   Cost (translation and sigma invariant): S = sum over base u of (c_u + x_u), where for the source (u,0):
     c_u = #{j != src : no even walk of length <= 6 from src to j}   (same-side far pairs, half of them)
     x_u = #{j : no odd walk of length <= 7 from src to j}          (cross far pairs)
   far(G) = t * S exactly (checked with bin/score37 in calibration).
   Usage: lift3d k A seed seconds T0 T1 sweeps outprefix [init.state | -]
     writes outprefix_best.state and outprefix_best.edges (cover edge list, n = 2m) whenever S improves.
*/
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>
#include <limits.h>

#define MAXK 32
#define MAXM 128

typedef struct { uint64_t w[2]; } BS;
typedef struct {
    uint32_t fm[MAXK];   /* F-neighbour masks */
    int l1[MAXK];        /* L1 flags */
    int tp[MAXK];        /* T partner; tp[u] == u for L2; -1 for type a */
    int tc[MAXK];        /* class of the T-link / L2 at u */
} St;

static int k, A, t, C, m;
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline int rndi(int n) { return (int)(rnd() % (uint64_t)n); }
static inline double rndu(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) { struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts); return ts.tv_sec + 1e-9 * ts.tv_nsec; }

static inline int bit(const BS *b, int i) { return (b->w[i >> 6] >> (i & 63)) & 1; }
static inline void bset(BS *b, int i) { b->w[i >> 6] |= 1ULL << (i & 63); }
static inline int pc(const BS *b) { return __builtin_popcountll(b->w[0]) + __builtin_popcountll(b->w[1]); }
static inline void bor(BS *a, const BS *b) { a->w[0] |= b->w[0]; a->w[1] |= b->w[1]; }

/* out = union of R[w] over w in src */
static void orset(BS *out, const BS *src, const BS *R) {
    BS r = {{0, 0}};
    for (int w = 0; w < 2; w++) {
        uint64_t x = src->w[w];
        while (x) { int i = __builtin_ctzll(x) + 64 * w; bor(&r, &R[i]); x &= x - 1; }
    }
    *out = r;
}

static void bs_sym(BS *N, int a, int b) { bset(&N[a], b); bset(&N[b], a); }

static void build(const St *s, BS *N) {
    memset(N, 0, sizeof(BS) * m);
    for (int u = 0; u < k; u++) {
        for (int v = u + 1; v < k; v++) if ((s->fm[u] >> v) & 1)
            for (int x = 0; x < t; x++) bs_sym(N, u * t + x, v * t + x);
        if (s->l1[u]) for (int x = 0; x < t; x++) bs_sym(N, u * t + x, u * t + x);
        int v = s->tp[u], g = s->tc[u];
        if (v < 0) continue;
        if (v == u) {
            for (int x = 0; x < t; x++) { bs_sym(N, u * t + x, u * t + (x + g) % t); bs_sym(N, u * t + x, u * t + (x - g + t) % t); }
        } else if (u < v) {
            for (int x = 0; x < t; x++) { bs_sym(N, u * t + x, v * t + (x + g) % t); bs_sym(N, u * t + x, v * t + (x - g + t) % t); }
        }
    }
}

/* S = sum_u (c_u + x_u); also fills the number of same-side and cross far pairs if asked */
static int cost_S(const St *s) {
    static BS N[MAXM], R2[MAXM];
    build(s, N);
    for (int v = 0; v < m; v++) orset(&R2[v], &N[v], N);
    int S = 0;
    for (int u = 0; u < k; u++) {
        int src = u * t;
        BS R2s = R2[src], R4s, R6s, O3, O5, O7;
        orset(&R4s, &R2s, R2);
        orset(&R6s, &R4s, R2);
        BS E = R2s; bor(&E, &R4s); bor(&E, &R6s); bset(&E, src);
        int c = m - pc(&E);
        orset(&O3, &N[src], R2);
        orset(&O5, &O3, R2);
        orset(&O7, &O5, R2);
        BS Od = N[src]; bor(&Od, &O3); bor(&Od, &O5); bor(&Od, &O7);
        int x = m - pc(&Od);
        S += c + x;
    }
    return S;
}

static inline int adjF(const St *s, int a, int b) { return (s->fm[a] >> b) & 1; }
static inline void addF(St *s, int a, int b) { s->fm[a] |= 1u << b; s->fm[b] |= 1u << a; }
static inline void remF(St *s, int a, int b) { s->fm[a] &= ~(1u << b); s->fm[b] &= ~(1u << a); }
static inline void setlink(St *s, int a, int b, int g) { s->tp[a] = b; s->tp[b] = a; s->tc[a] = g; s->tc[b] = g; }
static inline void setL2(St *s, int a, int g) { s->tp[a] = a; s->tc[a] = g; }

static int rand_fedge(const St *s, int *a, int *b) {
    for (int tries = 0; tries < 1000; tries++) {
        int u = rndi(k);
        if (!s->fm[u]) continue;
        int cnt = __builtin_popcount(s->fm[u]), r = rndi(cnt);
        uint32_t x = s->fm[u];
        while (r--) x &= x - 1;
        *a = u; *b = __builtin_ctz(x); return 1;
    }
    return 0;
}
static int rand_link(const St *s, int *u_out) { /* random endpoint of a non-loop T-link */
    for (int tries = 0; tries < 1000; tries++) {
        int u = rndi(k);
        if (s->tp[u] >= 0 && s->tp[u] != u) { *u_out = u; return 1; }
    }
    return 0;
}
static int rand_L2(const St *s, int *u_out) {
    for (int tries = 0; tries < 1000; tries++) {
        int u = rndi(k);
        if (s->tp[u] == u) { *u_out = u; return 1; }
    }
    return 0;
}
static int rand_L1(const St *s, int excl1, int excl2, int *u_out) {
    for (int tries = 0; tries < 1000; tries++) {
        int u = rndi(k);
        if (s->l1[u] && u != excl1 && u != excl2) { *u_out = u; return 1; }
    }
    return 0;
}

static int mv_F2(St *s) { /* F-edges {a,b},{c,d} -> {a,c},{b,d} (or {a,d},{b,c}) */
    int a, b, c, d;
    if (!rand_fedge(s, &a, &b) || !rand_fedge(s, &c, &d)) return 0;
    if (rnd() & 1) { int tt = c; c = d; d = tt; }
    if (a == c || a == d || b == c || b == d) return 0;
    if (adjF(s, a, c) || adjF(s, b, d)) return 0;
    remF(s, a, b); remF(s, c, d); addF(s, a, c); addF(s, b, d);
    return 1;
}
static int mv_L1slide(St *s) { /* F-edge {a,b} + L1 at c -> F-edge {a,c} + L1 at b */
    int a, b, c;
    if (!rand_fedge(s, &a, &b)) return 0;
    if (!rand_L1(s, a, b, &c)) return 0;
    if (rnd() & 1) { int tt = a; a = b; b = tt; }
    if (s->l1[b]) return 0;
    if (adjF(s, a, c)) return 0;
    remF(s, a, b); addF(s, a, c); s->l1[b] = 1; s->l1[c] = 0;
    return 1;
}
static int mv_Fsplit(St *s) { /* F-edge {a,b} -> L1 at a and L1 at b */
    int a, b;
    if (!rand_fedge(s, &a, &b)) return 0;
    if (s->l1[a] || s->l1[b]) return 0;
    remF(s, a, b); s->l1[a] = 1; s->l1[b] = 1;
    return 1;
}
static int mv_Fmerge(St *s) { /* L1 at a and L1 at b -> F-edge {a,b} */
    int a, b;
    if (!rand_L1(s, -1, -1, &a)) return 0;
    if (!rand_L1(s, a, -1, &b)) return 0;
    if (adjF(s, a, b)) return 0;
    s->l1[a] = 0; s->l1[b] = 0; addF(s, a, b);
    return 1;
}
static int mv_T2(St *s) { /* T-links {u1,v1},{u2,v2} -> {u1,u2},{v1,v2} (or {u1,v2},{v1,u2}) */
    int u1, u2;
    if (!rand_link(s, &u1) || !rand_link(s, &u2)) return 0;
    int v1 = s->tp[u1], v2 = s->tp[u2];
    if (u2 == u1 || u2 == v1) return 0;
    if (rnd() & 1) { int tt = u2; u2 = v2; v2 = tt; }
    setlink(s, u1, u2, 1 + rndi(C));
    setlink(s, v1, v2, 1 + rndi(C));
    return 1;
}
static int mv_TL2(St *s) { /* T-link {a,b} + L2 at c -> T-link {a,c} + L2 at b */
    int a, c;
    if (!rand_link(s, &a)) return 0;
    int b = s->tp[a];
    if (!rand_L2(s, &c)) return 0;
    if (rnd() & 1) { int tt = a; a = b; b = tt; }
    setlink(s, a, c, 1 + rndi(C));
    setL2(s, b, 1 + rndi(C));
    return 1;
}
static int mv_Tsplit(St *s) { /* T-link {a,b} -> L2 at a and L2 at b */
    int a;
    if (!rand_link(s, &a)) return 0;
    int b = s->tp[a];
    setL2(s, a, 1 + rndi(C)); setL2(s, b, 1 + rndi(C));
    return 1;
}
static int mv_Tmerge(St *s) { /* L2 at a and L2 at b -> T-link {a,b} */
    int a, b;
    if (!rand_L2(s, &a) || !rand_L2(s, &b)) return 0;
    if (a == b) return 0;
    setlink(s, a, b, 1 + rndi(C));
    return 1;
}
static int mv_volt(St *s) { /* change the class of a T-link or L2 */
    int u;
    if (C < 2) return 0;
    for (int tries = 0; tries < 1000; tries++) {
        int c = rndi(k);
        if (s->tp[c] >= 0) { u = c; goto found; }
    }
    return 0;
found:;
    int g = 1 + (s->tc[u] - 1 + 1 + rndi(C - 1)) % C;
    s->tc[u] = g;
    if (s->tp[u] != u) s->tc[s->tp[u]] = g;
    return 1;
}

static int do_move(St *s) {
    double r = rndu();
    if (r < 0.25) return mv_F2(s);
    if (r < 0.35) return mv_L1slide(s);
    if (r < 0.40) return mv_Fsplit(s);
    if (r < 0.45) return mv_Fmerge(s);
    if (r < 0.65) return mv_T2(s);
    if (r < 0.73) return mv_TL2(s);
    if (r < 0.78) return mv_Tsplit(s);
    if (r < 0.83) return mv_Tmerge(s);
    return mv_volt(s);
}

/* consistency check of the slot structure (used after every accepted move) */
static int check_state(const St *s) {
    for (int u = 0; u < k; u++) {
        int F = __builtin_popcount(s->fm[u]) + s->l1[u];
        if (F != (u < A ? 3 : 1)) return 0;
        if ((s->fm[u] >> u) & 1) return 0;
        for (int v = 0; v < k; v++) if (((s->fm[u] >> v) & 1) != ((s->fm[v] >> u) & 1)) return 0;
        if (u < A) { if (s->tp[u] != -1) return 0; }
        else {
            int v = s->tp[u];
            if (v < 0 || v >= k) return 0;
            if (s->tp[v] != u || s->tc[v] != s->tc[u]) return 0;
            if (s->tc[u] < 1 || s->tc[u] > C) return 0;
        }
    }
    return 1;
}

static void init_random(St *s) {
    int B = k - A, tot = 3 * A + B;
    for (;;) {
        memset(s, 0, sizeof *s);
        for (int u = 0; u < k; u++) s->tp[u] = -1;
        int l1c = (tot & 1) ? 1 : 0;
        l1c += 2 * rndi(2);
        int perm[MAXK];
        for (int u = 0; u < k; u++) perm[u] = u;
        for (int u = k - 1; u > 0; u--) { int j = rndi(u + 1), tt = perm[u]; perm[u] = perm[j]; perm[j] = tt; }
        for (int i = 0; i < l1c; i++) s->l1[perm[i]] = 1;
        int sl[3 * MAXK], ns = 0;
        for (int u = 0; u < k; u++) for (int c = 0; c < (u < A ? 3 : 1) - s->l1[u]; c++) sl[ns++] = u;
        int ok = 0;
        for (int att = 0; att < 200000 && !ok; att++) {
            for (int i = ns - 1; i > 0; i--) { int j = rndi(i + 1), tt = sl[i]; sl[i] = sl[j]; sl[j] = tt; }
            ok = 1;
            for (int i = 0; i + 1 < ns; i += 2) {
                int a = sl[i], b = sl[i + 1];
                if (a == b || adjF(s, a, b)) { ok = 0; break; }
                addF(s, a, b);
            }
            if (!ok) { for (int u = 0; u < k; u++) s->fm[u] = 0; }
        }
        if (!ok || (ns & 1)) continue;
        /* T part: b vertices, L2 count with parity of B */
        int bl[MAXK], nb = 0;
        for (int u = A; u < k; u++) bl[nb++] = u;
        int l2c = (B & 1) ? 1 : 0;
        l2c += 2 * rndi(2);
        if (l2c > nb) l2c = nb & 1;
        for (int i = nb - 1; i > 0; i--) { int j = rndi(i + 1), tt = bl[i]; bl[i] = bl[j]; bl[j] = tt; }
        for (int i = 0; i < l2c; i++) setL2(s, bl[i], 1 + rndi(C));
        for (int i = l2c; i + 1 < nb; i += 2) setlink(s, bl[i], bl[i + 1], 1 + rndi(C));
        if (check_state(s)) return;
    }
}

static void write_state(const St *s, const char *fn, int S) {
    FILE *f = fopen(fn, "w");
    if (!f) { perror(fn); return; }
    fprintf(f, "H %d %d %d S=%d far=%d\n", k, A, t, S, t * S);
    for (int u = 0; u < k; u++) for (int v = u + 1; v < k; v++) if ((s->fm[u] >> v) & 1) fprintf(f, "F %d %d\n", u, v);
    for (int u = 0; u < k; u++) if (s->l1[u]) fprintf(f, "L1 %d\n", u);
    for (int u = 0; u < k; u++) if (s->tp[u] >= 0 && s->tp[u] > u) fprintf(f, "T %d %d %d\n", u, s->tp[u], s->tc[u]);
    for (int u = 0; u < k; u++) if (s->tp[u] == u) fprintf(f, "L2 %d %d\n", u, s->tc[u]);
    fclose(f);
}
static int read_state(St *s, const char *fn) {
    FILE *f = fopen(fn, "r");
    if (!f) { perror(fn); return 0; }
    char line[256];
    memset(s, 0, sizeof *s);
    for (int u = 0; u < k; u++) s->tp[u] = -1;
    while (fgets(line, sizeof line, f)) {
        int a, b, c;
        if (line[0] == 'F' && sscanf(line, "F %d %d", &a, &b) == 2) addF(s, a, b);
        else if (line[0] == 'L' && line[1] == '1' && sscanf(line, "L1 %d", &a) == 1) s->l1[a] = 1;
        else if (line[0] == 'T' && sscanf(line, "T %d %d %d", &a, &b, &c) == 3) setlink(s, a, b, c);
        else if (line[0] == 'L' && line[1] == '2' && sscanf(line, "L2 %d %d", &a, &b) == 2) setL2(s, a, b);
    }
    fclose(f);
    return check_state(s);
}
static void write_cover(const St *s, const char *fn) {
    static BS N[MAXM];
    build(s, N);
    FILE *f = fopen(fn, "w");
    if (!f) { perror(fn); return; }
    fprintf(f, "%d\n", 2 * m);
    for (int i = 0; i < m; i++) for (int j = i; j < m; j++) if (bit(&N[i], j)) {
        if (i == j) fprintf(f, "%d %d\n", i, m + i);
        else { fprintf(f, "%d %d\n", i, m + j); fprintf(f, "%d %d\n", j, m + i); }
    }
    fclose(f);
}

int main(int argc, char **argv) {
    if (argc < 9) { fprintf(stderr, "usage: lift3d k A seed seconds T0 T1 sweeps outprefix [init.state|-] [pert]\n"); return 1; }
    k = atoi(argv[1]); A = atoi(argv[2]);
    uint64_t seed = strtoull(argv[3], 0, 10);
    double secs = atof(argv[4]), T0 = atof(argv[5]), T1 = atof(argv[6]);
    long sweeps = atol(argv[7]);
    const char *outp = argv[8];
    t = 5; C = (t - 1) / 2; m = k * t;
    rs ^= seed * 0x9E3779B97F4A7C15ULL; if (!rs) rs = 1;
    for (int i = 0; i < 20; i++) rnd();
    St cur, best; int bestS = INT_MAX;
    if (argc > 9 && strcmp(argv[9], "-") != 0) { if (!read_state(&cur, argv[9])) { fprintf(stderr, "bad init\n"); return 1; } }
    else init_random(&cur);
    double t0 = now();
    int restarts = 0;
    char fn[512];
    long totalIt = 0;
    int firstRound = 1;
    int pert = (argc > 10) ? atoi(argv[10]) : 0;
    while (now() - t0 < secs) {
        if (!firstRound) {
            if (pert > 0 && bestS < INT_MAX) {
                cur = best;
                for (int p = 0; p < pert; p++) { St tmp = cur; if (do_move(&tmp)) cur = tmp; }
            } else init_random(&cur);
        }
        firstRound = 0;
        int S = cost_S(&cur);
        for (long it = 0; it < sweeps; it++) {
            double T = T0 * pow(T1 / T0, (double)it / (double)(sweeps > 1 ? sweeps - 1 : 1));
            St nxt = cur;
            totalIt++;
            if (!do_move(&nxt)) continue;
            if (!check_state(&nxt)) { fprintf(stderr, "BUG: invalid state\n"); return 2; }
            int S2 = cost_S(&nxt);
            int d = S2 - S;
            if (d <= 0 || rndu() < exp(-d / T)) {
                cur = nxt; S = S2;
                if (S < bestS) {
                    bestS = S; best = cur;
                    snprintf(fn, sizeof fn, "%s_best.state", outp); write_state(&best, fn, bestS);
                    snprintf(fn, sizeof fn, "%s_best.edges", outp); write_cover(&best, fn);
                    printf("improve S=%d far=%d (restart %d, it %ld, %.1fs)\n", bestS, t * bestS, restarts, it, now() - t0);
                    fflush(stdout);
                    if (bestS == 0) goto done;
                }
            }
            if ((it & 0xFFFF) == 0 && now() - t0 > secs) break;
        }
        restarts++;
    }
done:
    printf("done: restarts=%d iters=%ld best S=%d far=%d time=%.1fs\n", restarts, totalIt, bestS, t * bestS, now() - t0);
    return 0;
}
