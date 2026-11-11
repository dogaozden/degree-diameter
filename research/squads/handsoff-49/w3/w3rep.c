/* w3lift: voltage lifts of a small bipartite base (W(3) incidence graph, 80 vertices) over a group of order N <= 128.
   Lift vertex (v, x) = v*N + x. Base edge e = (eu, ev) with voltage g gives lift edges (eu, x) ~ (ev, g*x).
   Tree edges (BFS tree from vertex 0) have voltage identity (index 0); the cotree edges are free.
   Cost = sum over roots (u, e) of the number of lift vertices (w, x) with no walk of length <= D from u to w with
   voltage product x (dart voltages multiplied on the left, in walk order). Cost 0 <=> diameter <= D (if connected).
   Cyclic groups (table = addition mod N) use bit rotations; other groups use a generic left multiplication.
   Usage:
     w3lift BASE GROUP seconds seed OUTPREFIX [INIT]    anneal. GROUP = cyc:N | tab:FILE.bin  (groups.py format)
     w3lift BASE GROUP eval VOLTFILE                      cost of a voltage file (one value per base edge)
   Env: T0 (2.0), T1 (0.15), PERIOD (300000 steps), D (9), QUIET.
   On cost 0 writes OUTPREFIX.volt (base edge voltages) and OUTPREFIX.edges (lift edge list, n = b*N). */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>

typedef uint64_t u128;
#define MAXB 80
#define MAXE 256
#define MAXN 64

static int b, m, N, D = 9;
static int eu[MAXE], ev[MAXE], istree[MAXE], freeE[MAXE], nfree;
static int volt[MAXE];
static uint16_t MT[MAXN][MAXN];
static int INV[MAXN];
static int cyc;
static u128 FULL;
static uint64_t *LT; /* LT[(a*8+c)*256+byte] = left-multiplication image of the byte chunk c */
static int nin[MAXB], inE[MAXB][8], inFwd[MAXB][8];  /* incoming darts: edge, forward (dart eu->ev) flag */
static uint64_t rs = 0x9E3779B97F4A7C15ULL;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }

static void read_base(const char *fn) {
    FILE *f = fopen(fn, "r"); if (!f) { fprintf(stderr, "no base %s\n", fn); exit(2); }
    if (fscanf(f, "%d %d", &b, &m) != 2) exit(2);
    for (int e = 0; e < m; e++) if (fscanf(f, "%d %d", &eu[e], &ev[e]) != 2) exit(2);
    fclose(f);
}

static void load_group(const char *s) {
    if (!strncmp(s, "cyc:", 4)) {
        N = atoi(s + 4);
        for (int a = 0; a < N; a++) for (int c = 0; c < N; c++) MT[a][c] = (a + c) % N;
    } else if (!strncmp(s, "tab:", 4)) {
        FILE *f = fopen(s + 4, "rb"); int32_t n32;
        if (!f || fread(&n32, 4, 1, f) != 1) { fprintf(stderr, "cannot read table\n"); exit(2); }
        N = n32; if (N > MAXN) { fprintf(stderr, "N too big\n"); exit(2); }
        static uint16_t buf[MAXN * MAXN];
        if (fread(buf, 2, (size_t)N * N, f) != (size_t)N * N) exit(2);
        fclose(f);
        for (int a = 0; a < N; a++) for (int c = 0; c < N; c++) MT[a][c] = buf[a * N + c];
    } else { fprintf(stderr, "bad group\n"); exit(2); }
    cyc = 1;
    for (int a = 0; a < N && cyc; a++) for (int c = 0; c < N; c++) if (MT[a][c] != (a + c) % N) { cyc = 0; break; }
    for (int g = 0; g < N; g++) {
        INV[g] = -1;
        for (int h = 0; h < N; h++) if (MT[g][h] == 0) { INV[g] = h; break; }
        if (INV[g] < 0) { fprintf(stderr, "no inverse\n"); exit(2); }
    }
    FULL = (N == 64) ? ~(u128)0 : (((u128)1 << N) - 1);
    LT = malloc(sizeof(uint64_t) * (size_t)N * 8 * 256);
    for (int a = 0; a < N; a++) for (int c = 0; c < 8; c++) for (int by = 0; by < 256; by++) {
        uint64_t r = 0;
        for (int j = 0; j < 8; j++) if (by >> j & 1) { int x = 8 * c + j; if (x < N) r |= (uint64_t)1 << MT[a][x]; }
        LT[((size_t)a * 8 + c) * 256 + by] = r;
    }
}

static void build_structure(void) {
    /* BFS spanning tree from 0 */
    int seen[MAXB] = {0}, q[MAXB], qh = 0, qt = 0;
    for (int e = 0; e < m; e++) istree[e] = 0;
    seen[0] = 1; q[qt++] = 0;
    while (qh < qt) {
        int x = q[qh++];
        for (int e = 0; e < m; e++) {
            int y = -1;
            if (eu[e] == x) y = ev[e]; else if (ev[e] == x) y = eu[e];
            if (y >= 0 && !seen[y]) { seen[y] = 1; istree[e] = 1; q[qt++] = y; }
        }
    }
    if (qt != b) { fprintf(stderr, "base not connected\n"); exit(2); }
    nfree = 0;
    for (int e = 0; e < m; e++) if (!istree[e]) freeE[nfree++] = e;
    for (int w = 0; w < b; w++) nin[w] = 0;
    for (int e = 0; e < m; e++) {
        int w = ev[e]; inE[w][nin[w]] = e; inFwd[w][nin[w]] = 1; nin[w]++;
        w = eu[e]; inE[w][nin[w]] = e; inFwd[w][nin[w]] = 0; nin[w]++;
    }
    for (int w = 0; w < b; w++) if (nin[w] > 8) { fprintf(stderr, "degree too big\n"); exit(2); }
}

static inline int pop128(u128 S) { return __builtin_popcountll(S); }

static inline u128 lmul(int a, u128 S) {
    if (cyc) {
        if (a == 0) return S;
        return ((S << a) | (S >> (N - a))) & FULL;
    }
    const uint64_t *t = LT + (size_t)a * 8 * 256;
    return t[S & 255] | t[256 + ((S >> 8) & 255)] | t[512 + ((S >> 16) & 255)] | t[768 + ((S >> 24) & 255)]
         | t[1024 + ((S >> 32) & 255)] | t[1280 + ((S >> 40) & 255)] | t[1536 + ((S >> 48) & 255)] | t[1792 + ((S >> 56) & 255)];
}

/* returns total cost, or a value > limit as soon as the running total exceeds limit */
static long cost_eval(long limit) {
    u128 cur[MAXB], nxt[MAXB], R[MAXB];
    long total = 0;
    for (int r = 0; r < b; r++) {
        for (int w = 0; w < b; w++) { cur[w] = 0; R[w] = 0; }
        cur[r] = 1; R[r] = 1;
        for (int L = 1; L <= D; L++) {
            for (int w = 0; w < b; w++) {
                u128 acc = 0;
                for (int k = 0; k < nin[w]; k++) {
                    int e = inE[w][k], fwd = inFwd[w][k];
                    int src = fwd ? eu[e] : ev[e];
                    if (!cur[src]) continue;
                    int g = fwd ? volt[e] : INV[volt[e]];
                    acc |= lmul(g, cur[src]);
                }
                nxt[w] = acc;
            }
            for (int w = 0; w < b; w++) { R[w] |= nxt[w]; cur[w] = nxt[w]; }
        }
        for (int w = 0; w < b; w++) total += N - pop128(R[w]);
        if (total > limit) return total;
    }
    return total;
}

static void write_lift(const char *prefix) {
    char fn[512];
    snprintf(fn, sizeof fn, "%s.volt", prefix);
    FILE *f = fopen(fn, "w");
    fprintf(f, "%d %d %d\n", b, m, N);
    for (int e = 0; e < m; e++) fprintf(f, "%d %d %d\n", eu[e], ev[e], volt[e]);
    fclose(f);
    snprintf(fn, sizeof fn, "%s.edges", prefix);
    f = fopen(fn, "w");
    fprintf(f, "%d\n", b * N);
    for (int e = 0; e < m; e++)
        for (int x = 0; x < N; x++)
            fprintf(f, "%d %d\n", eu[e] * N + x, ev[e] * N + MT[volt[e]][x]);
    fclose(f);
}

static void read_volt(const char *fn) {
    FILE *f = fopen(fn, "r"); int bb, mm, NN; int a, c, g;
    if (!f) { fprintf(stderr, "no volt file\n"); exit(2); }
    if (fscanf(f, "%d %d %d", &bb, &mm, &NN) != 3) exit(2);
    for (int e = 0; e < m; e++) { if (fscanf(f, "%d %d %d", &a, &c, &g) != 3) exit(2); volt[e] = g; }
    fclose(f);
}


/* ---------- walk-directed repair ---------- */
static int rp_e[16], rp_f[16], rp_dart[16], rp_pre[17];
static int rp_target, rp_x;
static int cand_e[60000], cand_g[60000], ncand;

static void rp_walks(int x, int depth, int lastE) {
    if (depth > 0 && x == rp_target) {
        int Q = 0;                                  /* Q = a_{depth-1} ... a_{p+1}, identity at p = depth-1 */
        for (int p = depth - 1; p >= 0; p--) {
            int t = MT[INV[Q]][rp_x];               /* Q^{-1} x */
            int ap = MT[t][INV[rp_pre[p]]];         /* ... pre_p^{-1} */
            int g = rp_f[p] ? ap : INV[ap];
            if (ncand < 60000) { cand_e[ncand] = rp_e[p]; cand_g[ncand] = g; ncand++; }
            Q = MT[Q][rp_dart[p]];                  /* Q_{p-1} = Q_p * a_p */
        }
    }
    if (depth == D) return;
    for (int k = 0; k < nin[x]; k++) {
        int e = inE[x][k];
        if (e == lastE) continue;                   /* non-backtracking */
        int fwdOut = (x == eu[e]);                  /* dart x -> other end is forward (eu -> ev) */
        int other = fwdOut ? ev[e] : eu[e];
        int a = fwdOut ? volt[e] : INV[volt[e]];
        rp_e[depth] = e; rp_f[depth] = fwdOut; rp_dart[depth] = a;
        rp_pre[depth + 1] = MT[a][rp_pre[depth]];
        rp_walks(other, depth + 1, e);
    }
}

static void root_R(int r, u128 *R) {
    u128 cur[MAXB], nxt[MAXB];
    for (int w = 0; w < b; w++) { cur[w] = 0; R[w] = 0; }
    cur[r] = 1; R[r] = 1;
    for (int L = 1; L <= D; L++) {
        for (int w = 0; w < b; w++) {
            u128 acc = 0;
            for (int k = 0; k < nin[w]; k++) {
                int e = inE[w][k], fwd = inFwd[w][k];
                int src = fwd ? eu[e] : ev[e];
                if (!cur[src]) continue;
                int g = fwd ? volt[e] : INV[volt[e]];
                acc |= lmul(g, cur[src]);
            }
            nxt[w] = acc;
        }
        for (int w = 0; w < b; w++) { R[w] |= nxt[w]; cur[w] = nxt[w]; }
    }
}

static int repair_run(double secs, const char *outp, long cur_init) {
    double T = getenv("RT") ? atof(getenv("RT")) : 1.0;
    int K = getenv("RK") ? atoi(getenv("RK")) : 60;
    long cur = cur_init, best = cur_init;
    int bestv[MAXE]; memcpy(bestv, volt, sizeof volt);
    double t0 = now(); long it = 0, nacc = 0;
    u128 R[MAXB];
    static int perm[60000];
    int stall = 0;
    while (1) {
        it++;
        if ((it & 15) == 0 && now() - t0 > secs) break;
        int r = rnd() % b;
        root_R(r, R);
        int miss[MAXB * 64][2], nm = 0;
        for (int w = 0; w < b; w++) for (int x = 0; x < N; x++) if (!(R[w] >> x & 1)) { miss[nm][0] = w; miss[nm][1] = x; nm++; }
        if (nm == 0) continue;
        int pick = rnd() % nm;
        rp_target = miss[pick][0]; rp_x = miss[pick][1];
        ncand = 0;
        rp_pre[0] = 0;
        rp_walks(r, 0, -1);
        if (ncand == 0) continue;
        for (int i = 0; i < ncand; i++) perm[i] = i;
        int nsample = ncand < K ? ncand : K;
        for (int i = 0; i < nsample; i++) { int j = i + rnd() % (ncand - i); int tmp = perm[i]; perm[i] = perm[j]; perm[j] = tmp; }
        long bc = cur * 2 + 16; int bi = -1;
        for (int s = 0; s < nsample; s++) {
            int c_i = perm[s], e = cand_e[c_i], g = cand_g[c_i];
            if (g == volt[e]) continue;
            int old = volt[e]; volt[e] = g;
            long c = cost_eval(bc);
            volt[e] = old;
            if (c < bc || (c == bc && bi < 0 && c <= cur + 16)) { bc = c; bi = c_i; }
        }
        if (bi < 0) continue;
        double thr = -T * log(rnd01() + 1e-300);
        if ((double)(bc - cur) <= thr) {
            volt[cand_e[bi]] = cand_g[bi];
            cur = bc; nacc++;
            if (cur < best) {
                best = cur; memcpy(bestv, volt, sizeof volt); stall = 0;
                if (!getenv("QUIET")) fprintf(stderr, "rep it %ld t=%.1f best %ld\n", it, now() - t0, best);
                if (best == 0) break;
            }
        }
        stall++;
    }
    memcpy(volt, bestv, sizeof volt);
    fprintf(stderr, "repair done it=%ld acc=%ld best=%ld\n", it, nacc, best);
    if (best == 0) {
        char p[512]; snprintf(p, sizeof p, "%s_c0", outp); write_lift(p);
        printf("FOUND cost 0 n=%d file=%s.edges\n", b * N, p); fflush(stdout);
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 4) { fprintf(stderr, "usage: see header\n"); return 2; }
    if (getenv("D")) D = atoi(getenv("D"));
    read_base(argv[1]);
    load_group(argv[2]);
    build_structure();
    if (!strcmp(argv[3], "eval")) {
        read_volt(argv[4]);
        long c = cost_eval(1L << 60);
        printf("COST %ld\n", c);
        return 0;
    }
    double secs = atof(argv[3]);
    uint64_t seed = (uint64_t)atoll(argv[4]);
    const char *outp = argc > 5 ? argv[5] : "w3best";
    rs ^= seed * 0x2545F4914F6CDD1DULL + 12345; for (int i = 0; i < 20; i++) rnd();
    int quiet = getenv("QUIET") != NULL;
    for (int e = 0; e < m; e++) volt[e] = 0;
    if (argc > 6) read_volt(argv[6]);
    else for (int i = 0; i < nfree; i++) volt[freeE[i]] = rnd() % N;
    long cur = cost_eval(1L << 60);
    fprintf(stderr, "N=%d cyc=%d start cost %ld\n", N, cyc, cur);
    if (getenv("REPAIR")) {
        repair_run(secs, outp, cur);
        char p[512]; snprintf(p, sizeof p, "%s_best", outp);
        printf("END(repair) N=%d best=%ld cost_check=%ld file=%s.volt\n", N, cost_eval(1L << 60), cost_eval(1L << 60), p);
        write_lift(p);
        return 0;
    }
    double T0 = getenv("T0") ? atof(getenv("T0")) : 2.0;
    double T1 = getenv("T1") ? atof(getenv("T1")) : 0.15;
    long PERIOD = getenv("PERIOD") ? atol(getenv("PERIOD")) : 300000;
    long best = cur;
    int bestv[MAXE]; memcpy(bestv, volt, sizeof volt);
    double t0 = now(); long it = 0;
    while (1) {
        it++;
        if ((it & 255) == 0 && now() - t0 > secs) break;
        double frac = (double)(it % PERIOD) / (double)PERIOD;
        double T = T0 * pow(T1 / T0, frac);
        int e = freeE[rnd() % nfree];
        int old = volt[e], nv;
        if (cyc && (rnd() & 1)) { int d = 1 + rnd() % 3; if (rnd() & 1) d = N - d; nv = (old + d) % N; }
        else { do { nv = rnd() % N; } while (nv == old); }
        volt[e] = nv;
        double thr = -T * log(rnd01() + 1e-300);
        long limit = cur + (long)floor(thr);
        long c = cost_eval(limit);
        if (c <= limit) {
            cur = c;
            if (cur < best) {
                best = cur; memcpy(bestv, volt, sizeof volt);
                if (!quiet) fprintf(stderr, "it %ld t=%.1f best %ld\n", it, now() - t0, best);
                if (best == 0) break;
            }
        } else volt[e] = old;
    }
    memcpy(volt, bestv, sizeof volt);
    if (best == 0) { char p[512]; snprintf(p, sizeof p, "%s_c0", outp); write_lift(p); printf("FOUND cost 0 n=%d file=%s.edges\n", b * N, p); }
    char p[512]; snprintf(p, sizeof p, "%s_best", outp);
    write_lift(p);
    printf("END N=%d best=%ld iters=%ld time=%.1f file=%s.volt\n", N, best, it, now() - t0, p);
    return 0;
}
