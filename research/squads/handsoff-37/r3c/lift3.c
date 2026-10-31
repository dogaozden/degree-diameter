/* r2e lift search (card r2e: lift tabu with plateau escape), engine derived from c4/lift.c.
   Lift of a cubic bipartite base (k white + k black, E = 3k base edges (eu,ev,ea)), voltages ea in a group H of order N:
   vertex (u,g) = u*N+g (white), (k+v)*N+g (black), edge (u,g) ~ (v, g*a). n = 2kN.
   Raw cost = sum over the 2k base sources s of lift vertices not within distance 7 of (s,0) (bit-parallel walks).
   Weighted cost (breakout): wc = sum_{s,t} W[s][t] * cnt[s][t], cnt[s][t] = # unreached lift vertices (t,g) from source s.
   MODE=tabu : full-neighbourhood tabu on the raw cost, kick from the best after STALL non-improving steps (c4 behaviour).
   MODE=bo   : same tabu on wc; at a local minimum of wc (no improving move) the weights of all violated (s,t) pairs grow
               by 1 (breakout). BOWALK=1 also takes the best non-tabu move after a bump (tabu walk), else only bumps.
   Env: M (sampled 2-switches; -1 = all), TEN (tabu tenure), STALL (steps without raw improvement before a kick),
        PERT (random moves per kick), INIT (state file "N k" + E lines "u v a"), PERT0 (random moves on INIT first),
        WCAP (weight cap), DUPW (duplicate-edge penalty), D (walk length, 7).
   Usage: lift2 GROUPFILE k seed seconds OUTPREFIX. On raw cost 0 (no duplicates): writes OUTPREFIX_zero.edges, stops.
   Always writes OUTPREFIX_best.state / _best.edges (best raw state with no duplicates). */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>
#include <math.h>

#define MAXK 32
#define MAXE (3 * MAXK)
#define MAXN 1024
static int k, N, E, D = 7;
static int mul[64 * 64], inv_[64];
static int eu[MAXE], ev[MAXE], ea[MAXE];
static uint64_t R[MAXN], R2[MAXN];
static int nbr[3 * MAXN];
static long W[2 * MAXK][2 * MAXK];
static long cnt[2 * MAXK][2 * MAXK];
static long raw_last, dup_last, wc_last;
static double DUPW = 4.0;
static long WCAP = 1000000;
static uint64_t rng = 88172645463325252ULL;
static inline uint64_t xr(void) { rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; return rng; }
static inline double ur(void) { return (xr() >> 11) * (1.0 / 9007199254740992.0); }
static inline int ri(int m) { return (int)(xr() % (uint64_t)m); }

/* returns the (weighted) cost; sets raw_last, dup_last, wc_last */
static long eval(void) {
    int n = 2 * k * N;
    long dup = 0;
    for (int e = 0; e < E; e++) for (int f = e + 1; f < E; f++)
        if (eu[e] == eu[f] && ev[e] == ev[f] && ea[e] == ea[f]) dup++;
    int wv[MAXK][3], wa[MAXK][3], bu[MAXK][3], ba[MAXK][3], dw[MAXK], db[MAXK];
    memset(dw, 0, sizeof dw); memset(db, 0, sizeof db);
    for (int e = 0; e < E; e++) {
        int u = eu[e], v = ev[e];
        wv[u][dw[u]] = v; wa[u][dw[u]++] = ea[e];
        bu[v][db[v]] = u; ba[v][db[v]++] = inv_[ea[e]];
    }
    for (int u = 0; u < k; u++) for (int g = 0; g < N; g++) for (int j = 0; j < 3; j++)
        nbr[3 * (u * N + g) + j] = (k + wv[u][j]) * N + mul[g * N + wa[u][j]];
    for (int v = 0; v < k; v++) for (int h = 0; h < N; h++) for (int j = 0; j < 3; j++)
        nbr[3 * ((k + v) * N + h) + j] = bu[v][j] * N + mul[h * N + ba[v][j]];
    memset(R, 0, sizeof(uint64_t) * n);
    for (int s = 0; s < 2 * k; s++) R[s * N] = 1ULL << s;
    uint64_t *A = R, *B = R2;
    for (int t = 0; t < D; t++) {
        for (int x = 0; x < n; x++)
            B[x] = A[x] | A[nbr[3 * x]] | A[nbr[3 * x + 1]] | A[nbr[3 * x + 2]];
        uint64_t *tmp = A; A = B; B = tmp;
    }
    uint64_t full = (2 * k == 64) ? ~0ULL : ((1ULL << (2 * k)) - 1);
    memset(cnt, 0, sizeof cnt);
    long c = 0, wc = 0;
    for (int x = 0; x < n; x++) {
        uint64_t m = ~A[x] & full; int t = x / N;
        while (m) { int s = __builtin_ctzll(m); cnt[s][t]++; c++; wc += W[s][t]; m &= m - 1; }
    }
    if (A != R) memcpy(R, A, sizeof(uint64_t) * n);
    raw_last = c; dup_last = dup; wc_last = wc;
    return wc + (long)(DUPW * dup * N);
}

typedef struct { int type, e, f, a, olda; } Move;
static void apply(Move *m) {
    if (m->type == 0) { m->olda = ea[m->e]; ea[m->e] = m->a; }
    else { int t = ev[m->e]; ev[m->e] = ev[m->f]; ev[m->f] = t; }
}
static void undo(Move *m) {
    if (m->type == 0) ea[m->e] = m->olda;
    else { int t = ev[m->e]; ev[m->e] = ev[m->f]; ev[m->f] = t; }
}
static void random_move(Move *m) {
    if (ri(2)) { m->type = 0; m->e = ri(E); m->a = (ea[m->e] + 1 + ri(N - 1)) % N; m->f = 0; }
    else { m->type = 1; m->e = ri(E); do { m->f = ri(E); } while (m->f == m->e || ev[m->f] == ev[m->e]); }
}
static void init_random(void) {
    for (int m = 0; m < 3; m++) {
        int pm[MAXK]; for (int i = 0; i < k; i++) pm[i] = i;
        for (int i = k - 1; i > 0; i--) { int j = ri(i + 1); int t = pm[i]; pm[i] = pm[j]; pm[j] = t; }
        for (int u = 0; u < k; u++) { eu[3 * u + m] = u; ev[3 * u + m] = pm[u]; ea[3 * u + m] = ri(N); }
    }
}
static int write_edges(const char *fn) {
    FILE *f = fopen(fn, "w"); if (!f) return 0;
    fprintf(f, "%d\n", 2 * k * N);
    for (int e = 0; e < E; e++) for (int g = 0; g < N; g++)
        fprintf(f, "%d %d\n", eu[e] * N + g, (k + ev[e]) * N + mul[g * N + ea[e]]);
    fclose(f); return 1;
}
static void write_state(const char *fn, int *su, int *sv, int *sa) {
    FILE *f = fopen(fn, "w"); if (!f) return;
    fprintf(f, "%d %d\n", N, k);
    for (int e = 0; e < E; e++) fprintf(f, "%d %d %d\n", su[e], sv[e], sa[e]);
    fclose(f);
}
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }


static double rnd_exp_accept(double dc, double T) {
    if (dc <= 0) return 1.0;
    return exp(-dc / T);
}

/* base-vertex ball: marks base vertices within distance R of seeds (white u = u, black v = k+v) */
static int inball[2 * MAXK];
static void mark_ball(int seed, int R) {
    int dist[2 * MAXK]; for (int i = 0; i < 2 * k; i++) dist[i] = 1000;
    int q[2 * MAXK], qh = 0, qt = 0; dist[seed] = 0; q[qt++] = seed;
    while (qh < qt) {
        int x = q[qh++]; if (dist[x] >= R) continue;
        for (int e = 0; e < E; e++) {
            int a = eu[e], b = k + ev[e], y = -1;
            if (a == x) y = b; else if (b == x) y = a;
            if (y >= 0 && dist[y] > dist[x] + 1) { dist[y] = dist[x] + 1; q[qt++] = y; }
        }
    }
    for (int i = 0; i < 2 * k; i++) if (dist[i] <= R) inball[i] = 1;
}

int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: lift3 GROUPFILE k seed seconds OUTPREFIX\n"); return 2; }
    FILE *fg = fopen(argv[1], "r"); if (!fg) { perror(argv[1]); return 2; }
    if (fscanf(fg, "%d", &N) != 1) return 2;
    for (int i = 0; i < N * N; i++) if (fscanf(fg, "%d", &mul[i]) != 1) return 2;
    fclose(fg);
    for (int a = 0; a < N; a++) for (int b = 0; b < N; b++) if (mul[a * N + b] == 0) inv_[a] = b;
    k = atoi(argv[2]); if (k < 1 || k > MAXK) return 2;
    E = 3 * k; int n = 2 * k * N; if (n > MAXN) return 2;
    rng ^= (uint64_t)atoll(argv[3]) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 5; i++) xr();
    double secs = atof(argv[4]); const char *pre = argv[5];
    const char *mode = getenv("MODE") ? getenv("MODE") : "fbo";
    int isbo = !strcmp(mode, "bo") || !strcmp(mode, "fbo");
    int FOCUS = !strcmp(mode, "fbo");
    int FR = getenv("FR") ? atoi(getenv("FR")) : 1;          /* focus radius (base distance) around the violated pair */
    int TEN = getenv("TEN") ? atoi(getenv("TEN")) : 8;
    long STALL = getenv("STALL") ? atol(getenv("STALL")) : 3000;
    int PERT = getenv("PERT") ? atoi(getenv("PERT")) : 8;
    int PERT0 = getenv("PERT0") ? atoi(getenv("PERT0")) : 0;
    int BOWALK = getenv("BOWALK") ? atoi(getenv("BOWALK")) : 1;
    long DECAY = getenv("DECAY") ? atol(getenv("DECAY")) : 0;  /* halve (W-1) every DECAY bumps (0 = never) */
    double T0 = getenv("T0") ? atof(getenv("T0")) : 0;         /* unused unless MODE=sa */
    if (getenv("DUPW")) DUPW = atof(getenv("DUPW"));
    if (getenv("WCAP")) WCAP = atol(getenv("WCAP"));
    if (getenv("D")) D = atoi(getenv("D"));
    long BUMPGAP = getenv("BUMPGAP") ? atol(getenv("BUMPGAP")) : 0;
    long lastbump = -1000000000L;
    for (int s = 0; s < 2 * k; s++) for (int t = 0; t < 2 * k; t++) W[s][t] = 1;
    init_random();
    if (getenv("INIT")) {
        FILE *fi = fopen(getenv("INIT"), "r"); int NN, kk;
        if (!fi || fscanf(fi, "%d %d", &NN, &kk) != 2 || NN != N || kk != k) { fprintf(stderr, "bad INIT state\n"); return 2; }
        for (int e = 0; e < E; e++) if (fscanf(fi, "%d %d %d", &eu[e], &ev[e], &ea[e]) != 3) return 2;
        fclose(fi);
    }
    for (int p = 0; p < PERT0; p++) { Move m; random_move(&m); apply(&m); }
    long cur = eval(); long curraw = raw_last;
    long gbest_raw = (dup_last == 0) ? raw_last : (1L << 60);
    static int bu[MAXE], bv[MAXE], ba2[MAXE];
    memcpy(bu, eu, sizeof eu); memcpy(bv, ev, sizeof ev); memcpy(ba2, ea, sizeof ea);
    double t0 = now(), el = 0; long it = 0, since = 0, evals = 0, nkick = 0, nbump = 0, nsteps = 0;
    static long tabu_until[MAXE];
    memset(tabu_until, 0, sizeof tabu_until);
    printf("mode=%s N=%d k=%d n=%d FR=%d start raw=%ld wc=%ld dup=%ld\n", mode, N, k, n, FR, raw_last, cur, dup_last); fflush(stdout);
    int found = 0;
    if (raw_last == 0 && dup_last == 0) { char fn[512]; snprintf(fn, sizeof fn, "%s_zero.edges", pre); write_edges(fn); found = 1; }
    while (!found) {
        if ((it & 15) == 0) { el = now() - t0; if (el > secs) break; }
        it++;
        eval();  /* refresh cnt/raw for the current state */
        Move bestm; long bestc = 1L << 60; int have = 0;
        if (FOCUS) {
            /* pick a violated (s,t) pair uniformly, focus on base edges near s and t */
            int ps[2 * MAXK * 2 * MAXK], pt[2 * MAXK * 2 * MAXK], np = 0;
            for (int s = 0; s < 2 * k; s++) for (int t = 0; t < 2 * k; t++) if (cnt[s][t] > 0) { ps[np] = s; pt[np] = t; np++; }
            if (np == 0) np = 0;
            int fe[MAXE], nf = 0;
            if (np > 0) {
                int pick = ri(np);
                memset(inball, 0, sizeof inball);
                mark_ball(ps[pick], FR); int ms[2 * MAXK]; memcpy(ms, inball, sizeof ms);
                memset(inball, 0, sizeof inball);
                mark_ball(pt[pick], FR);
                for (int i = 0; i < 2 * k; i++) if (ms[i]) inball[i] = 1;
                for (int e = 0; e < E; e++) if (inball[eu[e]] || inball[k + ev[e]]) fe[nf++] = e;
            }
            if (nf == 0) { for (int e = 0; e < E; e++) fe[nf++] = e; }
            for (int ii = 0; ii < nf; ii++) {
                int e = fe[ii];
                for (int a = 0; a < N; a++) {
                    if (a == ea[e]) continue;
                    Move m = {0, e, 0, a, 0};
                    apply(&m); long c = eval(); evals++; long r = raw_last; long dp = dup_last; undo(&m);
                    int tabu = tabu_until[e] > it;
                    if (tabu && !(r < gbest_raw && dp == 0)) continue;
                    if (c < bestc || (c == bestc && ri(2))) { bestc = c; bestm = m; have = 1; }
                }
                for (int jj = 0; jj < nf; jj++) {
                    int f = fe[jj];
                    if (f <= e || ev[f] == ev[e]) continue;
                    Move m = {1, e, f, 0, 0};
                    apply(&m); long c = eval(); evals++; long r = raw_last; long dp = dup_last; undo(&m);
                    int tabu = tabu_until[e] > it || tabu_until[f] > it;
                    if (tabu && !(r < gbest_raw && dp == 0)) continue;
                    if (c < bestc || (c == bestc && ri(2))) { bestc = c; bestm = m; have = 1; }
                }
            }
        } else {
            for (int e = 0; e < E; e++) for (int a = 0; a < N; a++) {
                if (a == ea[e]) continue;
                Move m = {0, e, 0, a, 0};
                apply(&m); long c = eval(); evals++; long r = raw_last; long dp = dup_last; undo(&m);
                int tabu = tabu_until[e] > it;
                if (tabu && !(r < gbest_raw && dp == 0)) continue;
                if (c < bestc || (c == bestc && ri(2))) { bestc = c; bestm = m; have = 1; }
            }
            for (int e = 0; e < E; e++) for (int f = e + 1; f < E; f++) {
                if (ev[e] == ev[f]) continue;
                Move m = {1, e, f, 0, 0};
                apply(&m); long c = eval(); evals++; long r = raw_last; long dp = dup_last; undo(&m);
                int tabu = tabu_until[e] > it || tabu_until[f] > it;
                if (tabu && !(r < gbest_raw && dp == 0)) continue;
                if (c < bestc || (c == bestc && ri(2))) { bestc = c; bestm = m; have = 1; }
            }
        }
        if (!have) continue;
        cur = eval();  /* weighted cost of the current state (cnt is for current state) */
        if (isbo && bestc >= cur && it - lastbump >= BUMPGAP) {
            lastbump = it;
            for (int s = 0; s < 2 * k; s++) for (int t = 0; t < 2 * k; t++)
                if (cnt[s][t] > 0 && W[s][t] < WCAP) W[s][t]++;
            nbump++;
            if (DECAY > 0 && nbump % DECAY == 0)
                for (int s = 0; s < 2 * k; s++) for (int t = 0; t < 2 * k; t++) W[s][t] = 1 + (W[s][t] - 1) / 2;
            cur = eval();
            if (!BOWALK) continue;
        }
        apply(&bestm);
        if (bestm.type == 0) tabu_until[bestm.e] = it + TEN + ri(TEN + 1);
        else { tabu_until[bestm.e] = it + TEN + ri(TEN + 1); tabu_until[bestm.f] = it + TEN + ri(TEN + 1); }
        cur = eval(); curraw = raw_last; nsteps++;
        since++;
        if (dup_last == 0 && raw_last < gbest_raw) {
            gbest_raw = raw_last; since = 0;
            memcpy(bu, eu, sizeof eu); memcpy(bv, ev, sizeof ev); memcpy(ba2, ea, sizeof ea);
        }
        if (dup_last == 0 && raw_last == 0) {
            printf("FOUND cost 0 at t=%.1f it=%ld\n", el, it); fflush(stdout);
            char fn[512]; snprintf(fn, sizeof fn, "%s_zero.edges", pre); write_edges(fn);
            break;
        }
        if (since > STALL) {
            memcpy(eu, bu, sizeof eu); memcpy(ev, bv, sizeof ev); memcpy(ea, ba2, sizeof ea);
            for (int p = 0; p < PERT; p++) { Move m; random_move(&m); apply(&m); }
            cur = eval(); curraw = raw_last;
            since = 0; nkick++; memset(tabu_until, 0, sizeof tabu_until);
        }
        if (nsteps % 1000 == 0 && nsteps > 0 && it % 1 == 0) {
            printf("t=%.0f steps=%ld evals=%ld raw=%ld gbest_raw=%ld kicks=%ld bumps=%ld\n",
                   now() - t0, nsteps, evals, curraw, gbest_raw, nkick, nbump); fflush(stdout);
        }
    }
    el = now() - t0;
    memcpy(eu, bu, sizeof eu); memcpy(ev, bv, sizeof ev); memcpy(ea, ba2, sizeof ea);
    eval();
    char fn[512]; snprintf(fn, sizeof fn, "%s_best.state", pre); write_state(fn, eu, ev, ea);
    snprintf(fn, sizeof fn, "%s_best.edges", pre); write_edges(fn);
    printf("END t=%.1f steps=%ld evals=%ld best_raw=%ld far=%ld (N*raw/2) kicks=%ld bumps=%ld evals/s=%.0f\n",
           el, nsteps, evals, gbest_raw, (long)N * gbest_raw / 2, nkick, nbump, evals / (el > 0 ? el : 1));
    return 0;
}
