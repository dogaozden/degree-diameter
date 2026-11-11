/* prod2opt.c (card h09): fast cost and full 2-opt for Haar graphs H(G,S), G = G1 x G2, G1 = Z_m1 x|_r1 Z_k1,
 * G2 = Z_m2 x|_r2 Z_k2, |S| = d = 4, D = 10 (cost = number of B-side vertices at distance > 9 from (e,A)).
 *
 * Fast cost (no BFS): vertex (x,A) ~ (s x,B) and (h,B) ~ (s^-1 h,A). So the A-vertices at distance 2t from (e,A)
 * form X_t = T^t, T = {s_j^-1 s_i} (contains e), and the B-vertices at distance <= 2t+1 form S X_t. Hence
 *   cost = N - |S T^4|,   and  |S T^4| is computed from X2 = T T, X4 = X2 X2, S X4 with a full N x N product table.
 *
 * usage: prod2opt STATE m1 k1 r1 m2 k2 r2 SLOTI SLOTJ SECONDS PROGFILE OUTPREFIX
 *   SLOTI = 0 means "evaluate the base state only". Otherwise 2-opt over all pairs {x<y} of G\{e} placed in slots
 *   SLOTI, SLOTJ (1..d-1), the other slots fixed. Progress (pair counter) is kept in PROGFILE and resumed.
 *   Writes OUTPREFIX.cands (cost <= 1 hits), OUTPREFIX_sol_<c>.txt for cost 0.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define D 10
#define MAXD 8
static int m1, k1, r1, m2, k2, r2, n1, n2, N, d;
static int *mt1, *mt2;
static int *E1, *E2;     /* factor components of each element */
static inline int MUL(int g, int h) { return mt1[E1[g] * n1 + E1[h]] * n2 + mt2[E2[g] * n2 + E2[h]]; }
static int *INV;
static int S[MAXD];
static int *sT, *sX2, *sX4, *sC;
static int cT, cX2, cX4, cC;
static int *LT, *LX2, *LX4;
static int nT, nX2, nX4;

static int mulm(int m, int k, int r, int g, int h) {
    int a1 = g / k, j1 = g % k, a2 = h / k, j2 = h % k;
    int R = 1 % m;
    for (int t = 0; t < j1; t++) R = R * r % m;
    int a = (a1 + R * a2) % m;
    int j = (j1 + j2) % k;
    return a * k + j;
}

static double now(void) { struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts); return ts.tv_sec + 1e-9 * ts.tv_nsec; }

static void build(void) {
    n1 = m1 * k1; n2 = m2 * k2; N = n1 * n2;
    mt1 = malloc(sizeof(int) * n1 * n1);
    mt2 = malloc(sizeof(int) * n2 * n2);
    for (int g = 0; g < n1; g++) for (int h = 0; h < n1; h++) mt1[g * n1 + h] = mulm(m1, k1, r1, g, h);
    for (int g = 0; g < n2; g++) for (int h = 0; h < n2; h++) mt2[g * n2 + h] = mulm(m2, k2, r2, g, h);
    E1 = malloc(sizeof(int) * N); E2 = malloc(sizeof(int) * N);
    for (int g = 0; g < N; g++) { E1[g] = g / n2; E2[g] = g % n2; }
    INV = malloc(sizeof(int) * N);
    for (int g = 0; g < N; g++) {
        int f = -1;
        for (int h = 0; h < N; h++) if (MUL(g, h) == 0) { f = h; break; }
        INV[g] = f;
    }
    sT = calloc(N, sizeof(int)); sX2 = calloc(N, sizeof(int)); sX4 = calloc(N, sizeof(int)); sC = calloc(N, sizeof(int));
    LT = malloc(sizeof(int) * N); LX2 = malloc(sizeof(int) * N); LX4 = malloc(sizeof(int) * N);
}

/* |S T^4| complement: returns N - |S T^4| */
static int cost(void) {
    cT++;
    nT = 0;
    for (int i = 0; i < d; i++) for (int j = 0; j < d; j++) {
        int t = MUL(INV[S[j]], S[i]);
        if (sT[t] != cT) { sT[t] = cT; LT[nT++] = t; }
    }
    cX2++;
    nX2 = 0;
    for (int a = 0; a < nT; a++) for (int b = 0; b < nT; b++) {
        int z = MUL(LT[a], LT[b]);
        if (sX2[z] != cX2) { sX2[z] = cX2; LX2[nX2++] = z; }
    }
    cX4++;
    nX4 = 0;
    for (int a = 0; a < nX2; a++) {
        for (int b = 0; b < nX2; b++) {
            int z = MUL(LX2[a], LX2[b]);
            if (sX4[z] != cX4) { sX4[z] = cX4; LX4[nX4++] = z; }
        }
    }
    cC++;
    int cov = 0;
    for (int i = 0; i < d; i++) {
        for (int b = 0; b < nX4; b++) {
            int u = MUL(S[i], LX4[b]);
            if (sC[u] != cC) { sC[u] = cC; cov++; }
        }
    }
    return N - cov;
}

/* exact check of cost 0 by BFS over 2N vertices from (e,A) and (e,B), D = 10 */
static int bfs_ok(void) {
    int V = 2 * N;
    uint8_t *dist = malloc(V);
    int32_t *Q = malloc(sizeof(int32_t) * V);
    int ok = 1;
    for (int src = 0; src < 2 && ok; src++) {
        memset(dist, 255, V);
        int s0 = src == 0 ? 0 : N;
        int qh = 0, qt = 0;
        Q[qt++] = s0; dist[s0] = 0;
        while (qh < qt) {
            int v = Q[qh++];
            int dv = dist[v] + 1;
            if (v < N) {
                int g = v;
                for (int i = 0; i < d; i++) { int u = N + MUL(S[i], g); if (dist[u] == 255) { dist[u] = dv; Q[qt++] = u; } }
            } else {
                int h = v - N;
                for (int i = 0; i < d; i++) { int u = MUL(INV[S[i]], h); if (dist[u] == 255) { dist[u] = dv; Q[qt++] = u; } }
            }
        }
        for (int v = 0; v < V; v++) if (dist[v] > D) { ok = 0; break; }
    }
    free(dist); free(Q);
    return ok;
}

static void parse_state(const char *fn) {
    FILE *f = fopen(fn, "r");
    if (!f) { fprintf(stderr, "no state %s\n", fn); exit(2); }
    char line[4096];
    if (!fgets(line, sizeof line, f) || sscanf(line, "%d", &d) != 1) { fprintf(stderr, "bad header\n"); exit(2); }
    int got = 0;
    while (got < d && fgets(line, sizeof line, f)) {
        char *sp = strchr(line, ' ');
        if (!sp) continue;
        const char *q1 = strstr(sp, "meta(a=");
        if (!q1) { fprintf(stderr, "no meta in %s\n", line); exit(2); }
        int a1, j1, a2 = 0, j2 = 0;
        if (sscanf(q1, "meta(a=%d,j=%d)", &a1, &j1) != 2) { fprintf(stderr, "bad meta\n"); exit(2); }
        const char *q2 = strstr(q1 + 7, "meta(a=");
        if (q2) { if (sscanf(q2, "meta(a=%d,j=%d)", &a2, &j2) != 2) { fprintf(stderr, "bad meta2\n"); exit(2); } }
        S[got++] = (a1 * k1 + j1) * n2 + (a2 * k2 + j2);   /* n2 set by build() beforehand */
    }
    fclose(f);
    if (got != d) { fprintf(stderr, "short state\n"); exit(2); }
}

static void write_sol(const char *path, int cost) {
    FILE *f = fopen(path, "w");
    if (!f) return;
    fprintf(f, "%d %d prod meta %d %d %d meta %d %d %d n 1 N %d cost %d\n", d, D, m1, k1, r1, m2, k2, r2, N, cost);
    for (int i = 0; i < d; i++) {
        int g = S[i], g1 = g / n2, g2 = g % n2;
        fprintf(f, "%d prod[meta(a=%d,j=%d);meta(a=%d,j=%d)] z=0\n", g, g1 / k1, g1 % k1, g2 / k2, g2 % k2);
    }
    fclose(f);
}

int main(int argc, char **argv) {
    if (argc < 13) { fprintf(stderr, "usage: prod2opt STATE m1 k1 r1 m2 k2 r2 SLOTI SLOTJ SECONDS PROGFILE OUTPREFIX\n"); return 2; }
    const char *statef = argv[1];
    m1 = atoi(argv[2]); k1 = atoi(argv[3]); r1 = atoi(argv[4]);
    m2 = atoi(argv[5]); k2 = atoi(argv[6]); r2 = atoi(argv[7]);
    int si = atoi(argv[8]), sj = atoi(argv[9]);
    double secs = atof(argv[10]);
    const char *progf = argv[11], *outp = argv[12];
    double t0 = now();
    build();
    parse_state(statef);
    fprintf(stderr, "N=%d d=%d build %.2fs\n", N, d, now() - t0);
    int base = cost();
    fprintf(stderr, "base cost=%d  S =", base);
    for (int i = 0; i < d; i++) fprintf(stderr, " %d", S[i]);
    fprintf(stderr, "\n");
    if (si == 0) {
        /* timing of the evaluator */
        double ta = now(); int reps = 2000, last = 0;
        for (int r = 0; r < reps; r++) last = cost();
        fprintf(stderr, "eval time %.1f us (cost %d)\n", 1e6 * (now() - ta) / reps, last);
        return 0;
    }
    long long c0 = 0;
    { FILE *pf = fopen(progf, "r"); if (pf) { if (fscanf(pf, "%lld", &c0) != 1) c0 = 0; fclose(pf); } }
    if (sj == 0) {  /* 1-opt: replace slot si by every x in G \ {e}, resuming at x = c0 */
        int S0[MAXD]; memcpy(S0, S, sizeof S);
        int b1 = 1 << 30, bx1 = -1, h1[4] = {0, 0, 0, 0};
        long long x = c0 < 1 ? 1 : c0; long long nev1 = 0;
        t0 = now();
        for (; x < N; x++) {
            if (now() - t0 > secs) break;
            int bad = 0;
            for (int i = 0; i < d; i++) if (i != si && S0[i] == x) bad = 1;
            if (bad) continue;
            S[si] = (int)x;
            int cc = cost(); nev1++;
            if (cc < 4) h1[cc]++;
            if (cc < b1) { b1 = cc; bx1 = (int)x; }
            if (cc <= 1) fprintf(stderr, "1opt slot %d x %lld cost %d\n", si, x, cc);
            if (cc <= (getenv("LISTMAX") ? atoi(getenv("LISTMAX")) : 3) && getenv("LISTOUT")) { FILE *lf = fopen(getenv("LISTOUT"), "a"); if (lf) { fprintf(lf, "%lld %d\n", x, cc); fclose(lf); } }
            if (cc == 0) { int ok = bfs_ok(); char sp[1100]; snprintf(sp, sizeof sp, "%s_sol_1opt_%d_%lld.txt", outp, si, x); write_sol(sp, 0); fprintf(stderr, "COST0 1opt ok=%d file=%s\n", ok, sp); }
            S[si] = S0[si];
        }
        FILE *pf1 = fopen(progf, "w"); if (pf1) { fprintf(pf1, "%lld\n", x); fclose(pf1); }
        fprintf(stderr, "1opt slot %d: x %lld..%lld evals=%lld hist(0,1,2,3)=%lld,%lld,%lld,%lld best=%d (x=%d) time=%.1f\n",
                si, c0, x, nev1, h1[0], h1[1], h1[2], h1[3], b1, bx1, now() - t0);
        return 0;
    }
    if (si < 1 || sj < 1 || si == sj || sj >= d) { fprintf(stderr, "bad slots\n"); return 2; }
    int S0[MAXD]; memcpy(S0, S, sizeof S);
    char candp[1024]; snprintf(candp, sizeof candp, "%s.cands", outp);
    FILE *cf = fopen(candp, "a");
    long long c = 0, nev = 0;
    int best = 1 << 30, bx = -1, by = -1;
    long long hist[4] = {0, 0, 0, 0};
    int stop = 0;
    t0 = now();
    if (getenv("LIST")) {  /* pairs: slot si = x from LIST file (one x per line), slot sj = every y in G \\ {e} */
        int *LST = malloc(sizeof(int) * N); int nl = 0;
        FILE *lf = fopen(getenv("LIST"), "r");
        if (!lf) { fprintf(stderr, "no list\n"); return 2; }
        long long xx; int cc2;
        while (fscanf(lf, "%lld %d", &xx, &cc2) == 2) if (nl < N) LST[nl++] = (int)xx;
        fclose(lf);
        long long tot = (long long)nl * (N - 1), cc_ = c0;
        for (; cc_ < tot; cc_++) {
            if ((nev & 63) == 0 && now() - t0 > secs) break;
            int x = LST[cc_ / (N - 1)], y = 1 + (int)(cc_ % (N - 1));
            if (x == y) continue;
            int bad = 0;
            for (int i = 0; i < d; i++) if (i != si && i != sj && (S0[i] == x || S0[i] == y)) bad = 1;
            if (bad) continue;
            S[si] = x; S[sj] = y;
            int cv = cost(); nev++;
            if (cv < 4) hist[cv]++;
            if (cv < best) { best = cv; bx = x; by = y; }
            if (cv <= 1 && cf) fprintf(cf, "slots %d %d x %d y %d cost %d\n", si, sj, x, y, cv);
            if (cv == 0) { int ok = bfs_ok(); char sp[1100]; snprintf(sp, sizeof sp, "%s_sol_l_%lld.txt", outp, cc_); write_sol(sp, 0); fprintf(stderr, "COST0 list x=%d y=%d bfs_ok=%d file=%s\n", x, y, ok, sp); }
            S[si] = S0[si]; S[sj] = S0[sj];
        }
        if (cf) fclose(cf);
        FILE *pfl = fopen(progf, "w"); if (pfl) { fprintf(pfl, "%lld\n", cc_); fclose(pfl); }
        fprintf(stderr, "LIST slots %d,%d (nlist=%d) counter %lld..%lld of %lld evals=%lld hist(0,1,2,3)=%lld,%lld,%lld,%lld best=%d (x=%d y=%d) time=%.1f\n",
                si, sj, nl, c0, cc_, tot, nev, hist[0], hist[1], hist[2], hist[3], best, bx, by, now() - t0);
        return 0;
    }
    if (getenv("SAMPLE")) {  /* pseudo-random pairs (x,y) spread over the whole pair space, resumable by counter c */
        long long nn = N - 1; long long cc_ = c0;
        for (; ; cc_++) {
            if ((nev & 63) == 0 && now() - t0 > secs) break;
            int x = 1 + (int)((cc_ * 7919 + 13) % nn), y = 1 + (int)((cc_ * 104729 + 7) % nn);
            if (x == y) continue;
            int bad = 0;
            for (int i = 0; i < d; i++) if (i != si && i != sj && (S0[i] == x || S0[i] == y)) bad = 1;
            if (bad) continue;
            S[si] = x; S[sj] = y;
            int cv = cost(); nev++;
            if (cv < 4) hist[cv]++;
            if (cv < best) { best = cv; bx = x; by = y; }
            if (cv <= 1 && cf) fprintf(cf, "slots %d %d x %d y %d cost %d\n", si, sj, x, y, cv);
            if (cv == 0) { int ok = bfs_ok(); char sp[1100]; snprintf(sp, sizeof sp, "%s_sol_s_%lld.txt", outp, cc_); write_sol(sp, 0); fprintf(stderr, "COST0 sample x=%d y=%d bfs_ok=%d file=%s\n", x, y, ok, sp); }
            S[si] = S0[si]; S[sj] = S0[sj];
        }
        if (cf) fclose(cf);
        FILE *pfs = fopen(progf, "w"); if (pfs) { fprintf(pfs, "%lld\n", cc_); fclose(pfs); }
        fprintf(stderr, "SAMPLE slots %d,%d counter %lld..%lld evals=%lld hist(0,1,2,3)=%lld,%lld,%lld,%lld best=%d (x=%d y=%d) time=%.1f\n",
                si, sj, c0, cc_, nev, hist[0], hist[1], hist[2], hist[3], best, bx, by, now() - t0);
        return 0;
    }
    for (int x = 1; x < N && !stop; x++) {
        for (int y = x + 1; y < N; y++, c++) {
            if (c < c0) continue;
            if ((nev & 127) == 0 && now() - t0 > secs) { stop = 1; break; }
            int bad = 0;
            for (int i = 0; i < d; i++) if (i != si && i != sj && (S0[i] == x || S0[i] == y)) { bad = 1; break; }
            if (bad) continue;
            S[si] = x; S[sj] = y;
            int cc = cost();
            nev++;
            if (cc < 4) hist[cc]++;
            if (cc < best) { best = cc; bx = x; by = y; }
            if (cc <= 1 && cf) fprintf(cf, "slots %d %d x %d y %d cost %d\n", si, sj, x, y, cc);
            if (cc == 0) {
                int ok = bfs_ok();
                char sp[1100]; snprintf(sp, sizeof sp, "%s_sol_%lld.txt", outp, c);
                write_sol(sp, 0);
                fprintf(stderr, "COST0 c=%lld x=%d y=%d bfs_ok=%d file=%s\n", c, x, y, ok, sp);
                if (cf) fprintf(cf, "COST0 slots %d %d x %d y %d bfs_ok %d file %s\n", si, sj, x, y, ok, sp);
            }
            S[si] = S0[si]; S[sj] = S0[sj];
        }
        if (stop) break;
    }
    /* c counts pairs visited; c is complete only if the loop was not stopped */
    long long next = stop ? c : c;
    if (cf) fclose(cf);
    FILE *pf = fopen(progf, "w");
    if (pf) { fprintf(pf, "%lld\n", next); fclose(pf); }
    long long total = (long long)(N - 1) * (N - 2) / 2;
    fprintf(stderr, "slots %d,%d pairs %lld..%lld of %lld evals=%lld hist(0,1,2,3)=%lld,%lld,%lld,%lld best=%d (x=%d y=%d) time=%.1f\n",
            si, sj, c0, next, total, nev, hist[0], hist[1], hist[2], hist[3], best, bx, by, now() - t0);
    return 0;
}
