/* w3s: voltage lifts of the W(3) incidence graph (80 vertices, 160 edges) over a group of order N <= 64, optionally
   invariant under a base collineation (SYM file from mksym.py; voltage constant on edge orbits, phi = identity).
   Lift vertex (v,x) = v*N+x; base edge e=(eu,ev) with voltage g gives lift edges (eu,x) ~ (ev, g*x).
   Cost = sum over root representatives r (weighted by orbit size) of the number of (w, x) with no non-backtracking
   walk of length <= D from r to w with voltage x (cost 0 <=> diameter <= D).
   Usage:
     w3s BASE GROUP eval VOLTFILE                 cost of a voltage file (lines: eu ev volt, in base edge order)
     w3s BASE GROUP anneal SECS SEED OUTPREFIX [VOLTFILE]    simulated annealing over variables
     w3s BASE GROUP repair SECS SEED OUTPREFIX [VOLTFILE]    walk-directed repair (REPAIR moves) with SA acceptance
   GROUP = cyc:N | tab:FILE.bin. Env: SYM=file, D (9), T0 T1 PERIOD (anneal), RT RK (repair), QUIET.
   On cost 0 writes OUTPREFIX_c0.volt and OUTPREFIX_c0.edges (lift edge list, n = 80 N). */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>

#define MAXB 80
#define MAXE 256
#define MAXN 64
typedef uint64_t S64;

static int b, m, N, D = 9;
static int eu[MAXE], ev[MAXE];
static int volt[MAXE];
static int nin[MAXB], inE[MAXB][8], inFwd[MAXB][8];
static int nreps, reps[MAXB], wts[MAXB];
static int nvar, vof[MAXE], vmem[MAXE], vst[MAXE + 1], vmemn;   /* variable k has members vmem[vst[k] .. vst[k+1]) */
static uint16_t MT[MAXN][MAXN];
static int INV[MAXN], cyc;
static S64 FULL;
static S64 *LT;
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
    FULL = (N == 64) ? ~(S64)0 : (((S64)1 << N) - 1);
    LT = malloc(sizeof(S64) * (size_t)N * 8 * 256);
    for (int a = 0; a < N; a++) for (int c = 0; c < 8; c++) for (int by = 0; by < 256; by++) {
        S64 r = 0;
        for (int j = 0; j < 8; j++) if (by >> j & 1) { int x = 8 * c + j; if (x < N) r |= (S64)1 << MT[a][x]; }
        LT[((size_t)a * 8 + c) * 256 + by] = r;
    }
}

static void build_structure(void) {
    int seen[MAXB] = {0}, q[MAXB], qh = 0, qt = 0, istree[MAXE] = {0};
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
    for (int w = 0; w < b; w++) nin[w] = 0;
    for (int e = 0; e < m; e++) {
        int w = ev[e]; inE[w][nin[w]] = e; inFwd[w][nin[w]] = 1; nin[w]++;
        w = eu[e]; inE[w][nin[w]] = e; inFwd[w][nin[w]] = 0; nin[w]++;
    }
    for (int w = 0; w < b; w++) if (nin[w] > 8) { fprintf(stderr, "degree too big\n"); exit(2); }
    /* default: all vertices are roots (weight 1); variables: cotree edges (tree edges fixed to identity) */
    nreps = b; for (int v = 0; v < b; v++) { reps[v] = v; wts[v] = 1; }
    for (int e = 0; e < m; e++) { vof[e] = -1; volt[e] = 0; }
    nvar = 0; vmemn = 0;
    for (int e = 0; e < m; e++) if (!istree[e]) {
        vst[nvar] = vmemn; vmem[vmemn++] = e; vof[e] = nvar; nvar++;
    }
    vst[nvar] = vmemn;
}

static void build_sym(const char *fn) {
    FILE *f = fopen(fn, "r"); int nE, K;
    if (!f) { fprintf(stderr, "no sym\n"); exit(2); }
    if (fscanf(f, "%d %d", &nE, &K) != 2 || nE != m) { fprintf(stderr, "sym mismatch\n"); exit(2); }
    int eorb[MAXE];
    for (int e = 0; e < m; e++) if (fscanf(f, "%d", &eorb[e]) != 1) exit(2);
    if (fscanf(f, "%d", &nreps) != 1) exit(2);
    for (int i = 0; i < nreps; i++) if (fscanf(f, "%d %d", &reps[i], &wts[i]) != 2) exit(2);
    fclose(f);
    nvar = K; vmemn = 0;
    for (int k = 0; k < K; k++) {
        vst[k] = vmemn;
        for (int e = 0; e < m; e++) if (eorb[e] == k) { vmem[vmemn++] = e; vof[e] = k; }
    }
    vst[K] = vmemn;
    for (int e = 0; e < m; e++) volt[e] = 0;
}

static inline void set_var(int k, int val) { for (int i = vst[k]; i < vst[k + 1]; i++) volt[vmem[i]] = val; }

static inline int pop64(S64 S) { return __builtin_popcountll(S); }

static inline S64 lmul(int a, S64 S) {
    if (cyc) {
        if (a == 0) return S;
        return ((S << a) | (S >> (N - a))) & FULL;
    }
    const S64 *t = LT + (size_t)a * 8 * 256;
    return t[S & 255] | t[256 + ((S >> 8) & 255)] | t[512 + ((S >> 16) & 255)] | t[768 + ((S >> 24) & 255)]
         | t[1024 + ((S >> 32) & 255)] | t[1280 + ((S >> 40) & 255)] | t[1536 + ((S >> 48) & 255)] | t[1792 + ((S >> 56) & 255)];
}

static void root_R(int r, S64 *R) {
    S64 cur[MAXB], nxt[MAXB];
    for (int w = 0; w < b; w++) { cur[w] = 0; R[w] = 0; }
    cur[r] = 1; R[r] = 1;
    for (int L = 1; L <= D; L++) {
        for (int w = 0; w < b; w++) {
            S64 acc = 0;
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

/* weighted cost; returns a value > limit as soon as the running total exceeds limit */
static long cost_eval(long limit) {
    S64 R[MAXB];
    long total = 0;
    for (int ri = 0; ri < nreps; ri++) {
        root_R(reps[ri], R);
        long sub = 0;
        for (int w = 0; w < b; w++) sub += N - pop64(R[w]);
        total += sub * wts[ri];
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
    FILE *f = fopen(fn, "r"); int bb, mm, NN, a, c, g;
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
        int Q = 0;
        for (int p = depth - 1; p >= 0; p--) {
            int t = MT[INV[Q]][rp_x];
            int ap = MT[t][INV[rp_pre[p]]];
            int g = rp_f[p] ? ap : INV[ap];
            if (ncand < 60000) { cand_e[ncand] = rp_e[p]; cand_g[ncand] = g; ncand++; }
            Q = MT[Q][rp_dart[p]];
        }
    }
    if (depth == D) return;
    for (int k = 0; k < nin[x]; k++) {
        int e = inE[x][k];
        if (e == lastE) continue;
        int fwdOut = (x == eu[e]);
        int other = fwdOut ? ev[e] : eu[e];
        int a = fwdOut ? volt[e] : INV[volt[e]];
        rp_e[depth] = e; rp_f[depth] = fwdOut; rp_dart[depth] = a;
        rp_pre[depth + 1] = MT[a][rp_pre[depth]];
        rp_walks(other, depth + 1, e);
    }
}

static long repair_run(double secs, const char *outp, long cur, int *bestv) {
    double T = getenv("RT") ? atof(getenv("RT")) : 1.0;
    int K = getenv("RK") ? atoi(getenv("RK")) : 60;
    long best = cur;
    memcpy(bestv, volt, sizeof(int) * MAXE);
    double t0 = now(); long it = 0, nacc = 0;
    S64 R[MAXB];
    static int perm[60000];
    static int miss[MAXB * 64][2];
    while (1) {
        it++;
        if ((it & 15) == 0 && now() - t0 > secs) break;
        int r = reps[rnd() % nreps];
        root_R(r, R);
        int nm = 0;
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
            int k = vof[e], oldv = volt[e];
            set_var(k, g);
            long c = cost_eval(bc);
            set_var(k, oldv);
            if (c < bc || (c == bc && bi < 0 && c <= cur + 16)) { bc = c; bi = c_i; }
        }
        if (bi < 0) continue;
        double thr = -T * log(rnd01() + 1e-300);
        if ((double)(bc - cur) <= thr) {
            set_var(vof[cand_e[bi]], cand_g[bi]);
            cur = bc; nacc++;
            if (cur < best) {
                best = cur; memcpy(bestv, volt, sizeof(int) * MAXE);
                if (!getenv("QUIET")) fprintf(stderr, "rep it %ld t=%.1f best %ld\n", it, now() - t0, best);
                if (best == 0) break;
            }
        }
    }
    fprintf(stderr, "repair done it=%ld acc=%ld best=%ld\n", it, nacc, best);
    return best;
}

static long anneal_run(double secs, long cur, int *bestv) {
    double T0 = getenv("T0") ? atof(getenv("T0")) : 6.0;
    double T1 = getenv("T1") ? atof(getenv("T1")) : 0.3;
    long PERIOD = getenv("PERIOD") ? atol(getenv("PERIOD")) : 300000;
    long best = cur;
    memcpy(bestv, volt, sizeof(int) * MAXE);
    double t0 = now(); long it = 0;
    while (1) {
        it++;
        if ((it & 255) == 0 && now() - t0 > secs) break;
        double frac = (double)(it % PERIOD) / (double)PERIOD;
        double T = T0 * pow(T1 / T0, frac);
        int k = rnd() % nvar;
        int e = vmem[vst[k]];
        int old = volt[e], nv;
        if (cyc && (rnd() & 1)) { int d = 1 + rnd() % 3; if (rnd() & 1) d = N - d; nv = (old + d) % N; }
        else { do { nv = rnd() % N; } while (nv == old); }
        set_var(k, nv);
        double thr = -T * log(rnd01() + 1e-300);
        long limit = cur + (long)floor(thr);
        long c = cost_eval(limit);
        if (c <= limit) {
            cur = c;
            if (cur < best) { best = cur; memcpy(bestv, volt, sizeof(int) * MAXE); if (best == 0) break; }
        } else set_var(k, old);
    }
    fprintf(stderr, "anneal done it=%ld best=%ld\n", it, best);
    return best;
}

int main(int argc, char **argv) {
    if (argc < 4) { fprintf(stderr, "usage: see header\n"); return 2; }
    if (getenv("D")) D = atoi(getenv("D"));
    read_base(argv[1]);
    load_group(argv[2]);
    build_structure();
    if (getenv("SYM")) build_sym(getenv("SYM"));
    if (!strcmp(argv[3], "eval")) {
        read_volt(argv[4]);
        printf("COST %ld\n", cost_eval(1L << 60));
        return 0;
    }
    if (argc < 6) { fprintf(stderr, "need SECS SEED OUTPREFIX\n"); return 2; }
    double secs = atof(argv[4]);
    uint64_t seed = (uint64_t)atoll(argv[5]);
    const char *outp = argc > 6 ? argv[6] : "w3s";
    rs ^= seed * 0x2545F4914F6CDD1DULL + 12345; for (int i = 0; i < 20; i++) rnd();
    if (argc > 7) read_volt(argv[7]);
    else for (int k = 0; k < nvar; k++) set_var(k, rnd() % N);
    long cur = cost_eval(1L << 60);
    fprintf(stderr, "N=%d cyc=%d vars=%d reps=%d start cost %ld\n", N, cyc, nvar, nreps, cur);
    static int bestv[MAXE];
    long best;
    if (!strcmp(argv[3], "repair")) best = repair_run(secs, outp, cur, bestv);
    else best = anneal_run(secs, cur, bestv);
    memcpy(volt, bestv, sizeof(int) * MAXE);
    long chk = cost_eval(1L << 60);
    char p[512];
    if (best == 0) {
        snprintf(p, sizeof p, "%s_c0", outp); write_lift(p);
        printf("FOUND cost 0 n=%d file=%s.edges\n", b * N, p); fflush(stdout);
    }
    snprintf(p, sizeof p, "%s_best", outp); write_lift(p);
    printf("END N=%d best=%ld check=%ld file=%s.volt\n", N, best, chk, p);
    return 0;
}
