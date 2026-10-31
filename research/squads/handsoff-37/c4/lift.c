/* c4 lift search: joint base + voltage search for cubic bipartite lifts over a small group H.
   Base: cubic bipartite multigraph on k white + k black vertices, E = 3k base edges (eu, ev, ea):
   edge e joins white eu[e] to black ev[e] with voltage ea[e] in H (group of order N, identity 0).
   Lift: vertex (u,g) = u*N+g (white u < k), (k+v)*N+h (black v), edge (u,g) ~ (v, g*a); n = 2kN.
   Cost (exact, bit-parallel): for each of the 2k base sources s, the number of lift vertices x not reached by
   a walk of length <= 7 from (s,0). Walk reach up to length 7 in a bipartite graph equals the distance-<=7 ball
   (same side distance <= 6 is exactly the requirement). Ordered far pairs = N*cost, unordered far = N*cost/2.
   Duplicate lifted edges (two base edges with the same ends and voltage) are penalised by DUPW.
   Moves: change one voltage; 2-switch of black endpoints of two base edges (voltages stay on their edges).
   Search: MODE=tabu (full voltage neighbourhood + M sampled 2-switches, tabu tenure, perturbation from best)
           MODE=sa   (random moves, Metropolis, geometric temperature cycles).
   Usage: lift GROUPFILE k seed seconds OUTPREFIX    (env: MODE M TEN STALL PERT T0 T1 DUPW INIT)
   On far = 0 (cost 0, no duplicates) writes OUTPREFIX_zero.edges (score37 format). Always writes
   OUTPREFIX_best.state (N k, then "u v a" lines) when the run's best improves at its end. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>

#define MAXK 32
#define MAXE (3 * MAXK)
#define MAXN 1024
static int k, N, E, D = 7;
static int mul[64 * 64], inv_[64];
static int eu[MAXE], ev[MAXE], ea[MAXE];
static uint64_t R[MAXN], R2[MAXN];
static int nbr[3 * MAXN];
static long dup_last, raw_last;
static double DUPW = 4.0;
static uint64_t rng = 88172645463325252ULL;
static inline uint64_t xr(void) { rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; return rng; }
static inline double ur(void) { return (xr() >> 11) * (1.0 / 9007199254740992.0); }
static inline int ri(int m) { return (int)(xr() % (uint64_t)m); }

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
    long c = 0;
    for (int x = 0; x < n; x++) c += __builtin_popcountll(~A[x] & full);
    if (A != R) memcpy(R, A, sizeof(uint64_t) * n);
    raw_last = c; dup_last = dup;
    return c + (long)(DUPW * dup * N);
}

typedef struct { int type, e, f, a, olda, oldf; } Move;
static void apply(Move *m) {
    if (m->type == 0) { m->olda = ea[m->e]; ea[m->e] = m->a; }
    else { int t = ev[m->e]; ev[m->e] = ev[m->f]; ev[m->f] = t; }
}
static void undo(Move *m) {
    if (m->type == 0) ea[m->e] = m->olda;
    else { int t = ev[m->e]; ev[m->e] = ev[m->f]; ev[m->f] = t; }
}
static void random_move(Move *m) {
    if (ri(2)) { m->type = 0; m->e = ri(E); m->a = 1 + ri(N - 1); m->a = (ea[m->e] + m->a) % N; }
    else {
        m->type = 1; m->e = ri(E); do { m->f = ri(E); } while (m->f == m->e || ev[m->f] == ev[m->e]);
    }
}

/* focus: unreached count per source after the last eval (requires eval just called) */
static int focusR = 0;
static int pick_focus_mask(int *inc) {
    /* returns number of included edges; inc[e] = 1 if edge e is within base distance focusR of a random bad source */
    static long cnt[MAXK * 2]; int n = 2 * k * N; uint64_t full = (2 * k == 64) ? ~0ULL : ((1ULL << (2 * k)) - 1);
    memset(cnt, 0, sizeof cnt);
    for (int x = 0; x < n; x++) { uint64_t m = ~R[x] & full; while (m) { int s = __builtin_ctzll(m); cnt[s]++; m &= m - 1; } }
    long tot = 0; for (int s = 0; s < 2 * k; s++) tot += cnt[s];
    if (tot == 0) return 0;
    long pick = (long)(ur() * tot); int s0 = 0;
    for (s0 = 0; s0 < 2 * k; s0++) { if (pick < cnt[s0]) break; pick -= cnt[s0]; }
    if (s0 >= 2 * k) s0 = 0;
    /* base BFS from s0 (whites 0..k-1, blacks k..2k-1) */
    int dist[2 * MAXK]; for (int i = 0; i < 2 * k; i++) dist[i] = 99;
    int q[2 * MAXK], h = 0, t = 0; dist[s0] = 0; q[t++] = s0;
    while (h < t) { int x = q[h++]; if (dist[x] >= focusR) continue;
        for (int e = 0; e < E; e++) {
            int a = eu[e], b = k + ev[e];
            int y = -1; if (a == x) y = b; else if (b == x) y = a;
            if (y >= 0 && dist[y] == 99) { dist[y] = dist[x] + 1; q[t++] = y; }
        } }
    int c = 0;
    for (int e = 0; e < E; e++) { inc[e] = (dist[eu[e]] <= focusR) || (dist[k + ev[e]] <= focusR); c += inc[e]; }
    return c;
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

static void init_random(void) {
    /* random base: three random perfect matchings, random voltages */
    for (int m = 0; m < 3; m++) {
        int pm[MAXK]; for (int i = 0; i < k; i++) pm[i] = i;
        for (int i = k - 1; i > 0; i--) { int j = ri(i + 1); int t = pm[i]; pm[i] = pm[j]; pm[j] = t; }
        for (int u = 0; u < k; u++) { eu[3 * u + m] = u; ev[3 * u + m] = pm[u]; ea[3 * u + m] = ri(N); }
    }
}

int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: lift GROUPFILE k seed seconds OUTPREFIX\n"); return 2; }
    FILE *fg = fopen(argv[1], "r"); if (!fg) { perror(argv[1]); return 2; }
    if (fscanf(fg, "%d", &N) != 1) return 2;
    for (int i = 0; i < N * N; i++) if (fscanf(fg, "%d", &mul[i]) != 1) return 2;
    fclose(fg);
    for (int a = 0; a < N; a++) for (int b = 0; b < N; b++) if (mul[a * N + b] == 0) inv_[a] = b;
    k = atoi(argv[2]); if (k < 1 || k > MAXK) return 2;
    E = 3 * k; int n = 2 * k * N; if (n > MAXN) return 2;
    rng ^= (uint64_t)atoll(argv[3]) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 5; i++) xr();
    double secs = atof(argv[4]); const char *pre = argv[5];
    const char *mode = getenv("MODE") ? getenv("MODE") : "tabu";
    int M = getenv("M") ? atoi(getenv("M")) : 200;
    int TEN = getenv("TEN") ? atoi(getenv("TEN")) : 12;
    long STALL = getenv("STALL") ? atol(getenv("STALL")) : 3000;
    int PERT = getenv("PERT") ? atoi(getenv("PERT")) : 8;
    double T0 = getenv("T0") ? atof(getenv("T0")) : 3.0, T1 = getenv("T1") ? atof(getenv("T1")) : 0.2;
    double CYC = getenv("CYC") ? atof(getenv("CYC")) : 20.0;
    if (getenv("DUPW")) DUPW = atof(getenv("DUPW"));
    if (getenv("D")) D = atoi(getenv("D"));
    if (getenv("FOCUS")) focusR = atoi(getenv("FOCUS"));
    init_random();
    if (getenv("INIT")) { /* start from a saved state file: "N k" then E lines "u v a" */
        FILE *fi = fopen(getenv("INIT"), "r"); int NN, kk;
        if (!fi || fscanf(fi, "%d %d", &NN, &kk) != 2 || NN != N || kk != k) { fprintf(stderr, "bad INIT state\n"); return 2; }
        for (int e = 0; e < E; e++) if (fscanf(fi, "%d %d %d", &eu[e], &ev[e], &ea[e]) != 3) return 2;
        fclose(fi);
    }
    long cur = eval(), gbest = cur; long best_raw = raw_last; long best_dup = dup_last;
    static int bu[MAXE], bv[MAXE], ba2[MAXE];
    memcpy(bu, eu, sizeof eu); memcpy(bv, ev, sizeof ev); memcpy(ba2, ea, sizeof ea);
    int found0 = 0;
    struct timespec t0, t1; clock_gettime(CLOCK_MONOTONIC, &t0);
    double el = 0; long it = 0, since = 0; int tabu_until[MAXE]; memset(tabu_until, 0, sizeof tabu_until);
    long evals = 0, nrest = 0; int RESTART = getenv("RESTART") ? atoi(getenv("RESTART")) : 0;
    printf("mode=%s N=%d k=%d n=%d E=%d start cost=%ld\n", mode, N, k, n, E, cur); fflush(stdout);
    int reported = 0;
    if (!strcmp(mode, "tabu")) {
        for (;;) {
            if ((it & 15) == 0) { clock_gettime(CLOCK_MONOTONIC, &t1); el = (t1.tv_sec - t0.tv_sec) + 1e-9 * (t1.tv_nsec - t0.tv_nsec); if (el > secs) break; }
            it++;
            Move bestm; long bestc = 1L << 60; int have = 0;
            static int inc[MAXE];
            int nfocus = 0;
            if (focusR > 0) { eval(); nfocus = pick_focus_mask(inc); }
            /* full voltage neighbourhood */
            for (int e = 0; e < E; e++) if (focusR == 0 || (nfocus && inc[e])) for (int a = 0; a < N; a++) {
                if (a == ea[e]) continue;
                Move m = {0, e, 0, a, 0, 0};
                int tabu = tabu_until[e] > it;
                apply(&m); long c = eval(); evals++; undo(&m);
                if ((!tabu || c < gbest) && (c < bestc || (c == bestc && ri(2)))) { bestc = c; bestm = m; have = 1; }
            }
            if (focusR > 0) { /* focused 2-switches: first edge in the focus set, second any */
                for (int e = 0; e < E; e++) if (nfocus && inc[e]) for (int f = 0; f < E; f++) {
                    if (f == e || ev[e] == ev[f]) continue;
                    Move m = {1, e, f, 0, 0, 0};
                    int tabu = tabu_until[e] > it || tabu_until[f] > it;
                    apply(&m); long c = eval(); evals++; undo(&m);
                    if ((!tabu || c < gbest) && (c < bestc || (c == bestc && ri(2)))) { bestc = c; bestm = m; have = 1; }
                }
            } else
            if (M < 0) { /* all 2-switches */
                for (int e = 0; e < E; e++) for (int f = e + 1; f < E; f++) {
                    if (ev[e] == ev[f]) continue;
                    Move m = {1, e, f, 0, 0, 0};
                    int tabu = tabu_until[e] > it || tabu_until[f] > it;
                    apply(&m); long c = eval(); evals++; undo(&m);
                    if ((!tabu || c < gbest) && (c < bestc || (c == bestc && ri(2)))) { bestc = c; bestm = m; have = 1; }
                }
            } else
            for (int s = 0; s < M; s++) {
                Move m = {1, 0, 0, 0, 0, 0};
                m.e = ri(E); do { m.f = ri(E); } while (m.f == m.e || ev[m.f] == ev[m.e]);
                int tabu = tabu_until[m.e] > it || tabu_until[m.f] > it;
                apply(&m); long c = eval(); evals++; undo(&m);
                if ((!tabu || c < gbest) && (c < bestc || (c == bestc && ri(2)))) { bestc = c; bestm = m; have = 1; }
            }
            if (!have) continue;
            apply(&bestm);
            if (bestm.type == 0) tabu_until[bestm.e] = it + TEN + ri(TEN + 1);
            else { tabu_until[bestm.e] = it + TEN + ri(TEN + 1); tabu_until[bestm.f] = it + TEN + ri(TEN + 1); }
            cur = eval();
            since++;
            if (cur < gbest) {
                gbest = cur; best_raw = raw_last; best_dup = dup_last; since = 0;
                memcpy(bu, eu, sizeof eu); memcpy(bv, ev, sizeof ev); memcpy(ba2, ea, sizeof ea);
            }
            if (dup_last == 0 && raw_last == 0 && !found0) {
                found0 = 1; printf("FOUND cost 0 at t=%.1f it=%ld\n", el, it); fflush(stdout);
                char fn[512]; snprintf(fn, sizeof fn, "%s_zero.edges", pre); write_edges(fn);
                break;
            }
            if (since > STALL) {
                if (RESTART) { init_random(); nrest++; cur = eval(); }
                else { /* perturb from the global best */
                    memcpy(eu, bu, sizeof eu); memcpy(ev, bv, sizeof ev); memcpy(ea, ba2, sizeof ea);
                    for (int p = 0; p < PERT; p++) { Move m; random_move(&m); apply(&m); }
                    cur = eval();
                }
                since = 0; memset(tabu_until, 0, sizeof tabu_until);
            }
            if (cur < 0) break;
            if (it % 20000 == 0) { printf("t=%.0f it=%ld evals=%ld cur=%ld gbest=%ld (raw %ld dup %ld)\n", el, it, evals, cur, gbest, best_raw, best_dup); fflush(stdout); }
            (void)reported;
        }
    } else {
        long c = cur;
        for (;;) {
            if ((it & 255) == 0) { clock_gettime(CLOCK_MONOTONIC, &t1); el = (t1.tv_sec - t0.tv_sec) + 1e-9 * (t1.tv_nsec - t0.tv_nsec); if (el > secs) break; }
            it++;
            double Tt = T0 * pow(T1 / T0, fmod(el, CYC) / CYC);
            Move m; random_move(&m);
            apply(&m); long c2 = eval(); evals++;
            if (c2 <= c || ur() < exp((c - c2) / Tt)) {
                c = c2;
                if (c < gbest) { gbest = c; best_raw = raw_last; best_dup = dup_last;
                    memcpy(bu, eu, sizeof eu); memcpy(bv, ev, sizeof ev); memcpy(ba2, ea, sizeof ea); since = 0; }
                if (dup_last == 0 && raw_last == 0) {
                    printf("FOUND cost 0 at t=%.1f it=%ld\n", el, it); fflush(stdout);
                    char fn[512]; snprintf(fn, sizeof fn, "%s_zero.edges", pre); write_edges(fn);
                    found0 = 1; break;
                }
            } else undo(&m);
            if (it % 2000000 == 0) { printf("t=%.0f it=%ld cur=%ld gbest=%ld (raw %ld dup %ld) T=%.3f\n", el, it, c, gbest, best_raw, best_dup, Tt); fflush(stdout); }
        }
    }
    clock_gettime(CLOCK_MONOTONIC, &t1); el = (t1.tv_sec - t0.tv_sec) + 1e-9 * (t1.tv_nsec - t0.tv_nsec);
    /* write global best state and its edge list */
    memcpy(eu, bu, sizeof eu); memcpy(ev, bv, sizeof ev); memcpy(ea, ba2, sizeof ea);
    eval();
    char fn[512]; snprintf(fn, sizeof fn, "%s_best.state", pre); write_state(fn, eu, ev, ea);
    snprintf(fn, sizeof fn, "%s_best.edges", pre); write_edges(fn);
    printf("restarts=%ld ", nrest);
    printf("END t=%.1f it=%ld evals=%ld gbest=%ld raw=%ld dup=%ld far=%ld (N*raw/2) evals/s=%.0f\n",
           el, it, evals, gbest, best_raw, best_dup, (long)N * best_raw / 2, evals / (el > 0 ? el : 1));
    return 0;
}
