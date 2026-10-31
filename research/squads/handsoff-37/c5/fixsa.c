/* fixsa: simulated annealing over quotients of cubic bipartite graphs with an automorphism s of order 3
   that has FA fixed vertices on side A and FB fixed vertices on side B (c5 card).

   Graph with m vertices per side (n = 2m). s preserves both sides. Regular orbits have 3 copies:
     A-orbit ao, copy i  -> vertex 3*ao + i          (ao < AR, AR = (m-FA)/3)
     A fixed k           -> vertex 3*AR + k          (k < FA)
     B-orbit bo, copy i  -> vertex m + 3*bo + i      (bo < BR, BR = (m-FB)/3)
     B fixed k           -> vertex m + 3*BR + k      (k < FB)
   Quotient edges (qa[e], qb[e], qt[e]) join (ao, i) to (bo, (i + t) mod 3) for i = 0,1,2.
   A fixed A-vertex k is adjacent to the three copies of B-orbit fa[k]; a fixed B-vertex k is adjacent to the three
   copies of A-orbit fb[k]. Slots: every regular orbit has 3 slots (quotient edges + fixed attachments).
   Only quotient-level moves are made, so the graph stays cubic, bipartite, s-invariant and simple.

   Cost = number of unordered vertex pairs at distance > 7 (= far of score37). Computed by a bit-parallel BFS
   from one representative per orbit (weight 3 for regular orbits, 1 for fixed vertices).

   usage: fixsa m FA FB seed secs T0 T1 steps [outprefix]
     runs SA from random starts (each run: steps moves, temperature T0 -> T1 geometrically) until secs elapse.
     When a graph with cost 0 is found it is written to outprefix_sol.edges and the program exits with status 0.
     The best graph of the whole run is written to outprefix_best.edges (edge list, score37 format). */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>
static double wall(void) { struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts); return ts.tv_sec + 1e-9 * ts.tv_nsec; }

typedef unsigned __int128 u128;

#define MAXE 400
#define MAXF 16
#define MAXV 512

static int m, FA, FB, AR, BR, E, n, R;
static int qa[MAXE], qb[MAXE], qt[MAXE];
static int fa[MAXF], fb[MAXF];
static int adj[MAXV][3], deg[MAXV];
static int repv[256];
static u128 regmask, fixmask, fullmask;
static u128 reach[MAXV], front[MAXV], nfr[MAXV];
/* witnesses: vertices with unreached representatives (of the last evaluated graph) */
static int wv_new[MAXV], nw_new, wv_cur[MAXV], nw_cur;
static u128 wm_new[MAXV], wm_cur[MAXV];
static double pfocus = 0.0;
static int have_init = 0;
static int focus_cands[4 * MAXE];

static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline int rndi(int k) { return (int)(rnd() % (uint64_t)k); }
static inline double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
static inline int pc128(u128 x) { return __builtin_popcountll((uint64_t)x) + __builtin_popcountll((uint64_t)(x >> 64)); }

typedef struct { int qa[MAXE], qb[MAXE], qt[MAXE], fa[MAXF], fb[MAXF]; } State;
static State cur_s, bak_s, best_s;

static void save(State *s) {
    memcpy(s->qa, qa, sizeof(int) * E); memcpy(s->qb, qb, sizeof(int) * E); memcpy(s->qt, qt, sizeof(int) * E);
    memcpy(s->fa, fa, sizeof(int) * FA); memcpy(s->fb, fb, sizeof(int) * FB);
}
static void load(const State *s) {
    memcpy(qa, s->qa, sizeof(int) * E); memcpy(qb, s->qb, sizeof(int) * E); memcpy(qt, s->qt, sizeof(int) * E);
    memcpy(fa, s->fa, sizeof(int) * FA); memcpy(fb, s->fb, sizeof(int) * FB);
}

/* builds adjacency from the state; returns 0 if some degree is not 3 */
static int build(void) {
    memset(deg, 0, sizeof(int) * n);
    int ok = 1;
#define ADD(u, v) do { int _u = (u), _v = (v); if (deg[_u] >= 3 || deg[_v] >= 3) ok = 0; else { \
        adj[_u][deg[_u]++] = _v; adj[_v][deg[_v]++] = _u; } } while (0)
    for (int e = 0; e < E; e++)
        for (int i = 0; i < 3; i++) ADD(3 * qa[e] + i, m + 3 * qb[e] + (i + qt[e]) % 3);
    for (int k = 0; k < FA; k++)
        for (int i = 0; i < 3; i++) ADD(3 * AR + k, m + 3 * fa[k] + i);
    for (int k = 0; k < FB; k++)
        for (int i = 0; i < 3; i++) ADD(m + 3 * BR + k, 3 * fb[k] + i);
#undef ADD
    return ok;
}

/* cost = number of unordered pairs at distance > 7; large if the graph is not cubic */
static long cost(void) {
    if (!build()) return 1L << 40;
    for (int x = 0; x < n; x++) { reach[x] = 0; front[x] = 0; }
    for (int r = 0; r < R; r++) { u128 b = ((u128)1) << r; reach[repv[r]] |= b; front[repv[r]] |= b; }
    for (int lev = 0; lev < 7; lev++) {
        for (int x = 0; x < n; x++) {
            u128 acc = front[adj[x][0]] | front[adj[x][1]] | front[adj[x][2]];
            nfr[x] = acc & ~reach[x];
        }
        for (int x = 0; x < n; x++) { reach[x] |= nfr[x]; front[x] = nfr[x]; }
    }
    long tot = 0;
    nw_new = 0;
    for (int x = 0; x < n; x++) {
        u128 un = ~reach[x] & fullmask;
        if (un) { wv_new[nw_new] = x; wm_new[nw_new] = un; nw_new++; }
        tot += 3L * pc128(un & regmask) + pc128(un & fixmask);
    }
    return tot / 2;
}

/* does the quotient edge triple (a,b,t) occur among Q-edges other than skip1, skip2? */
static int dup_triple(int a, int b, int t, int skip1, int skip2) {
    for (int e = 0; e < E; e++)
        if (e != skip1 && e != skip2 && qa[e] == a && qb[e] == b && qt[e] == t) return 1;
    return 0;
}

static int count_fa(int bo, int skip) {
    int c = 0;
    for (int k = 0; k < FA; k++) if (k != skip && fa[k] == bo) c++;
    return c;
}
static int count_fb(int ao, int skip) {
    int c = 0;
    for (int k = 0; k < FB; k++) if (k != skip && fb[k] == ao) c++;
    return c;
}

static int qq_swap(int i, int j) {
    if (E < 2 || i == j) return 0;
    if (qa[i] == qa[j] && qb[i] == qb[j]) return 0;
    int ti = rndi(3), tj = rndi(3);
    int na_i = qa[i], nb_i = qb[j], na_j = qa[j], nb_j = qb[i];
    if (dup_triple(na_i, nb_i, ti, i, j) || dup_triple(na_j, nb_j, tj, i, j)) return 0;
    if (na_i == na_j && nb_i == nb_j && ti == tj) return 0;
    qb[i] = nb_i; qt[i] = ti; qb[j] = nb_j; qt[j] = tj;
    return 1;
}

/* Q-edges touching the orbit(s) of vertex v (regular orbit, or the orbit a fixed vertex is attached to) */
static int touch_edges(int v, int *out) {
    int c = 0;
    if (v < m) {               /* A side */
        if (v < 3 * AR) { int ao = v / 3; for (int e = 0; e < E; e++) if (qa[e] == ao) out[c++] = e; }
        else { int bo = fa[v - 3 * AR]; for (int e = 0; e < E; e++) if (qb[e] == bo) out[c++] = e; }
    } else {                   /* B side */
        int w = v - m;
        if (w < 3 * BR) { int bo = w / 3; for (int e = 0; e < E; e++) if (qb[e] == bo) out[c++] = e; }
        else { int ao = fb[w - 3 * BR]; for (int e = 0; e < E; e++) if (qa[e] == ao) out[c++] = e; }
    }
    return c;
}

/* focused proposal: pick a witness (x, far from representative rv) and modify a quotient edge touching x or rv */
static int propose_focus(void) {
    if (nw_cur == 0) return 0;
    int k = rndi(nw_cur);
    int x = wv_cur[k];
    u128 mk = wm_cur[k];
    /* pick a random set bit = representative index */
    int cnt = pc128(mk), pick = rndi(cnt), r = -1;
    for (int b = 0; b < R; b++) if ((mk >> b) & 1) { if (pick == 0) { r = b; break; } pick--; }
    if (r < 0) return 0;
    int rv = repv[r];
    int c = touch_edges(x, focus_cands);
    c += touch_edges(rv, focus_cands + c);
    if (c == 0) return 0;
    int i = focus_cands[rndi(c)];
    if (rnd01() < 0.3) {       /* voltage change on a focus edge */
        int t = (qt[i] + 1 + rndi(2)) % 3;
        if (dup_triple(qa[i], qb[i], t, i, -1)) return 0;
        qt[i] = t;
        return 1;
    }
    int j = rndi(E);
    return qq_swap(i, j);
}

/* random legal move on the state; returns 0 if the proposal is illegal (state unchanged or invalid) */
static int propose(void) {
    if (pfocus > 0 && rnd01() < pfocus) return propose_focus();
    double r = rnd01();
    if (FA == 0 && FB == 0) r = (r < 0.7) ? 0.0 : 0.6;   /* free case: 70% swaps, 30% voltage changes */
    if (r < 0.50) {
        if (E < 2) return 0;
        int i = rndi(E), j = rndi(E);
        if (i == j) return 0;
        if (qa[i] == qa[j] && qb[i] == qb[j]) return 0;
        int ti = rndi(3), tj = rndi(3);
        int na_i = qa[i], nb_i = qb[j], na_j = qa[j], nb_j = qb[i];
        if (dup_triple(na_i, nb_i, ti, i, j) || dup_triple(na_j, nb_j, tj, i, j)) return 0;
        if (na_i == na_j && nb_i == nb_j && ti == tj) return 0;
        qb[i] = nb_i; qt[i] = ti; qb[j] = nb_j; qt[j] = tj;
        return 1;
    } else if (r < 0.70) {
        if (E < 1) return 0;
        int i = rndi(E);
        int t = (qt[i] + 1 + rndi(2)) % 3;
        if (dup_triple(qa[i], qb[i], t, i, -1)) return 0;
        qt[i] = t;
        return 1;
    } else if (r < 0.85 && FA > 0) {
        int k = rndi(FA), j = rndi(E);
        int bo1 = fa[k], bo2 = qb[j];
        if (bo1 == bo2) return 0;
        if (count_fa(bo2, k) >= 2) return 0;
        int t = rndi(3);
        if (dup_triple(qa[j], bo1, t, j, -1)) return 0;
        fa[k] = bo2; qb[j] = bo1; qt[j] = t;
        return 1;
    } else if (FB > 0) {
        int k = rndi(FB), j = rndi(E);
        int ao1 = fb[k], ao2 = qa[j];
        if (ao1 == ao2) return 0;
        if (count_fb(ao2, k) >= 2) return 0;
        int t = rndi(3);
        if (dup_triple(ao1, qb[j], t, j, -1)) return 0;
        fb[k] = ao2; qa[j] = ao1; qt[j] = t;
        return 1;
    }
    return 0;
}

/* random simple starting quotient */
static void random_init(void) {
    int Aslots[3 * 200], Bslots[3 * 200];
    for (int attempt = 0;; attempt++) {
        int na = 0, nbs = 0;
        for (int ao = 0; ao < AR; ao++) for (int i = 0; i < 3; i++) Aslots[na++] = ao;
        for (int bo = 0; bo < BR; bo++) for (int i = 0; i < 3; i++) Bslots[nbs++] = bo;
        for (int i = na - 1; i > 0; i--) { int j = rndi(i + 1); int t = Aslots[i]; Aslots[i] = Aslots[j]; Aslots[j] = t; }
        for (int i = nbs - 1; i > 0; i--) { int j = rndi(i + 1); int t = Bslots[i]; Bslots[i] = Bslots[j]; Bslots[j] = t; }
        /* first FB A-slots go to fixed B vertices, first FA B-slots to fixed A vertices */
        for (int k = 0; k < FB; k++) fb[k] = Aslots[k];
        for (int k = 0; k < FA; k++) fa[k] = Bslots[k];
        int *Aq = Aslots + FB, *Bq = Bslots + FA;
        for (int e = 0; e < E; e++) { qa[e] = Aq[e]; qb[e] = Bq[e]; qt[e] = rndi(3); }
        /* simple? */
        int ok = 1;
        for (int e = 0; e < E && ok; e++) if (dup_triple(qa[e], qb[e], qt[e], e, -1)) ok = 0;
        for (int k = 0; k < FA && ok; k++) if (count_fa(fa[k], k) >= 2) ok = 0;
        for (int k = 0; k < FB && ok; k++) if (count_fb(fb[k], k) >= 2) ok = 0;
        if (ok) break;
        if (attempt > 100000) { fprintf(stderr, "random_init failed\n"); exit(3); }
    }
}

/* state file: "FA FB" line, then E line, then E lines "qa qb qt", then FA values (fa), then FB values (fb).
   Loaded state must match the current m, FA, FB and E (dimensions are checked). */
static int load_file(const char *path) {
    FILE *f = fopen(path, "r");
    if (!f) { perror(path); exit(2); }
    int fa0, fb0, e0;
    if (fscanf(f, "%d %d", &fa0, &fb0) != 2 || fa0 != FA || fb0 != FB) { fprintf(stderr, "init: FA/FB mismatch\n"); exit(2); }
    if (fscanf(f, "%d", &e0) != 1 || e0 != E) { fprintf(stderr, "init: E mismatch (%d vs %d)\n", e0, E); exit(2); }
    for (int e = 0; e < E; e++) if (fscanf(f, "%d %d %d", &qa[e], &qb[e], &qt[e]) != 3) exit(2);
    for (int k = 0; k < FA; k++) if (fscanf(f, "%d", &fa[k]) != 1) exit(2);
    for (int k = 0; k < FB; k++) if (fscanf(f, "%d", &fb[k]) != 1) exit(2);
    fclose(f);
    return 1;
}

static void write_state(const char *path) {
    FILE *f = fopen(path, "w");
    if (!f) return;
    fprintf(f, "%d %d\n%d\n", FA, FB, E);
    for (int e = 0; e < E; e++) fprintf(f, "%d %d %d\n", qa[e], qb[e], qt[e]);
    for (int k = 0; k < FA; k++) fprintf(f, "%d\n", fa[k]);
    for (int k = 0; k < FB; k++) fprintf(f, "%d\n", fb[k]);
    fclose(f);
}

static const char *outp_eval_path(void) { static char b[512]; snprintf(b, sizeof b, "%s_eval.edges", getenv("OUTP") ? getenv("OUTP") : "out/eval"); return b; }

static int write_edges(const char *path) {
    if (!build()) return 0;
    FILE *f = fopen(path, "w");
    if (!f) return 0;
    fprintf(f, "%d\n", n);
    for (int v = 0; v < n; v++)
        for (int j = 0; j < 3; j++) if (adj[v][j] > v) fprintf(f, "%d %d\n", v, adj[v][j]);
    fclose(f);
    return 1;
}


/* full-neighbourhood tabu search from the current (INIT) state; env TABU=secs TENURE=k */
static void tabu_search(double secs, int tenure, const char *outp) {
    double w0 = wall();
    long c = cost();
    long best = c;
    State bestS; save(&bestS);
    static long tabu_until[MAXE];
    for (int e = 0; e < E; e++) tabu_until[e] = 0;
    char path[512];
    snprintf(path, sizeof path, "%s_tabu_best.edges", outp);
    write_edges(path);
    long step = 0;
    fprintf(stderr, "tabu start cost %ld\n", c);
    while (wall() - w0 < secs) {
        long bc = 1L << 40; int kind = -1, bi = -1, bj = -1, bti = 0, btj = 0, bk = -1;
        State st; save(&st);
        /* voltage changes */
        for (int i = 0; i < E; i++) for (int t = 0; t < 3; t++) {
            if (t == qt[i]) continue;
            if (dup_triple(qa[i], qb[i], t, i, -1)) continue;
            int old = qt[i]; qt[i] = t;
            long c2 = cost();
            qt[i] = old;
            int is_tabu = tabu_until[i] > step;
            if ((!is_tabu || c2 < best) && c2 < bc) { bc = c2; kind = 1; bi = i; bti = t; }
        }
        /* quotient 2-switches */
        for (int i = 0; i < E; i++) for (int j = i + 1; j < E; j++) {
            if (qa[i] == qa[j] && qb[i] == qb[j]) continue;
            int tabu_ij = (tabu_until[i] > step) || (tabu_until[j] > step);
            for (int ti = 0; ti < 3; ti++) for (int tj = 0; tj < 3; tj++) {
                int na_i = qa[i], nb_i = qb[j], na_j = qa[j], nb_j = qb[i];
                if (dup_triple(na_i, nb_i, ti, i, j) || dup_triple(na_j, nb_j, tj, i, j)) continue;
                if (na_i == na_j && nb_i == nb_j && ti == tj) continue;
                int oqb_i = qb[i], oqt_i = qt[i], oqb_j = qb[j], oqt_j = qt[j];
                qb[i] = nb_i; qt[i] = ti; qb[j] = nb_j; qt[j] = tj;
                long c2 = cost();
                qb[i] = oqb_i; qt[i] = oqt_i; qb[j] = oqb_j; qt[j] = oqt_j;
                if ((!tabu_ij || c2 < best) && c2 < bc) { bc = c2; kind = 0; bi = i; bj = j; bti = ti; btj = tj; }
            }
        }
        /* fixed-vertex moves */
        for (int k = 0; k < FA; k++) for (int j = 0; j < E; j++) {
            int bo1 = fa[k], bo2 = qb[j];
            if (bo1 == bo2 || count_fa(bo2, k) >= 2) continue;
            for (int t = 0; t < 3; t++) {
                if (dup_triple(qa[j], bo1, t, j, -1)) continue;
                int oq = qb[j], ot = qt[j], of = fa[k];
                fa[k] = bo2; qb[j] = bo1; qt[j] = t;
                long c2 = cost();
                fa[k] = of; qb[j] = oq; qt[j] = ot;
                int is_tabu = tabu_until[j] > step;
                if ((!is_tabu || c2 < best) && c2 < bc) { bc = c2; kind = 2; bi = k; bj = j; bti = t; }
            }
        }
        for (int k = 0; k < FB; k++) for (int j = 0; j < E; j++) {
            int ao1 = fb[k], ao2 = qa[j];
            if (ao1 == ao2 || count_fb(ao2, k) >= 2) continue;
            for (int t = 0; t < 3; t++) {
                if (dup_triple(ao1, qb[j], t, j, -1)) continue;
                int oq = qa[j], ot = qt[j], of = fb[k];
                fb[k] = ao2; qa[j] = ao1; qt[j] = t;
                long c2 = cost();
                fb[k] = of; qa[j] = oq; qt[j] = ot;
                int is_tabu = tabu_until[j] > step;
                if ((!is_tabu || c2 < best) && c2 < bc) { bc = c2; kind = 3; bi = k; bj = j; bti = t; }
            }
        }
        (void)bk;
        load(&st);
        if (kind < 0) { fprintf(stderr, "tabu: no move\n"); break; }
        if (kind == 1) { qt[bi] = bti; tabu_until[bi] = step + tenure + rndi(tenure); }
        else if (kind == 0) {
            int nb_i = qb[bj], nb_j = qb[bi];
            (void)nb_i; (void)nb_j;
            int na_i = qa[bi], na_j = qa[bj];
            int nbi = qb[bj], nbj = qb[bi];
            qb[bi] = nbi; qt[bi] = bti; qb[bj] = nbj; qt[bj] = btj;
            (void)na_i; (void)na_j;
            tabu_until[bi] = step + tenure + rndi(tenure); tabu_until[bj] = step + tenure + rndi(tenure);
        } else if (kind == 2) {
            int bo2 = qb[bj];
            fa[bi] = bo2; qb[bj] = fa[bi] == bo2 ? st.fa[bi] : qb[bj];
            /* recompute properly below */
        }
        if (kind == 2) {
            int bo1 = st.fa[bi], bo2 = st.qb[bj];
            fa[bi] = bo2; qb[bj] = bo1; qt[bj] = bti; tabu_until[bj] = step + tenure + rndi(tenure);
        } else if (kind == 3) {
            int ao1 = st.fb[bi], ao2 = st.qa[bj];
            fb[bi] = ao2; qa[bj] = ao1; qt[bj] = bti; tabu_until[bj] = step + tenure + rndi(tenure);
        }
        c = bc;
        if (c < best) {
            best = c; save(&bestS);
            write_edges(path);
            fprintf(stderr, "  tabu step %ld new best %ld t=%.1f\n", step, best, wall() - w0);
            if (best == 0) break;
        }
        step++;
        if (step % 50 == 0) fprintf(stderr, "tabu step %ld cur %ld best %ld t=%.1f\n", step, c, best, wall() - w0);
    }
    load(&bestS);
    { char sp[512]; snprintf(sp, sizeof sp, "%s_tabu_best.state", outp); write_state(sp); }
    printf("TABU DONE best_far=%ld steps=%ld\n", best, step);
}


/* iterated local search: kick (k random legal moves, unconditional), then SA at fixed low T for `steps` moves;
   accept the result if its cost is <= the current cost, otherwise go back. env ILS=secs KICK=k ILST=T ILSSTEPS=s */
static void ils_search(double secs, int kick, double T, long steps, const char *outp) {
    double w0 = wall();
    if (!have_init) random_init();
    long c = cost();
    long best = c;
    State cs, bs; save(&cs); save(&bs);
    char path[512];
    snprintf(path, sizeof path, "%s_ils_best.edges", outp);
    write_edges(path);
    long iters = 0, acc = 0;
    fprintf(stderr, "ils start cost %ld\n", c);
    while (wall() - w0 < secs) {
        load(&cs);
        long cc = c;
        int k = 0;
        while (k < kick) { if (propose()) k++; }
        long cur = cost();
        nw_cur = nw_new; memcpy(wv_cur, wv_new, sizeof(int) * nw_new); memcpy(wm_cur, wm_new, sizeof(u128) * nw_new);
        for (long st = 0; st < steps; st++) {
            save(&bak_s);
            if (!propose()) continue;
            long c2 = cost();
            if (c2 <= cur || rnd01() < exp(-(double)(c2 - cur) / T)) {
                cur = c2;
                nw_cur = nw_new; memcpy(wv_cur, wv_new, sizeof(int) * nw_new); memcpy(wm_cur, wm_new, sizeof(u128) * nw_new);
                if (cur < best) {
                    best = cur; save(&bs); write_edges(path);
                    fprintf(stderr, "  ils iter %ld new best %ld t=%.1f\n", iters, best, wall() - w0);
                    if (best == 0) break;
                }
            } else load(&bak_s);
        }
        iters++;
        if (cur <= cc) { c = cur; save(&cs); acc++; }
        if (best == 0) break;
        if (iters % 200 == 0) fprintf(stderr, "ils iter %ld cur %ld best %ld acc %ld t=%.1f\n", iters, c, best, acc, wall() - w0);
    }
    load(&bs);
    { char sp[512]; snprintf(sp, sizeof sp, "%s_ils_best.state", outp); write_state(sp); }
    printf("ILS DONE best_far=%ld iters=%ld\n", best, iters);
}

int main(int argc, char **argv) {
    if (argc < 9) { fprintf(stderr, "usage: fixsa m FA FB seed secs T0 T1 steps [outprefix]\n"); return 2; }
    m = atoi(argv[1]); FA = atoi(argv[2]); FB = atoi(argv[3]);
    uint64_t seed = strtoull(argv[4], 0, 10);
    double secs = atof(argv[5]), T0 = atof(argv[6]), T1 = atof(argv[7]);
    long steps = atol(argv[8]);
    const char *outp = argc > 9 ? argv[9] : "out/fix";
    if (getenv("PFOCUS")) pfocus = atof(getenv("PFOCUS"));
    if ((m - FA) % 3 || (m - FB) % 3 || FA > MAXF || FB > MAXF || FA < 0 || FB < 0) { fprintf(stderr, "bad FA/FB for m\n"); return 2; }
    AR = (m - FA) / 3; BR = (m - FB) / 3;
    E = 3 * AR - FB;
    if (E != 3 * BR - FA || E < 1 || E > MAXE) { fprintf(stderr, "bad E=%d\n", E); return 2; }
    n = 2 * m; R = AR + FA + BR + FB;
    if (R > 128 || n > MAXV) { fprintf(stderr, "too big R=%d n=%d\n", R, n); return 2; }
    rs ^= seed * 0x9E3779B97F4A7C15ULL; if (!rs) rs = 1;
    /* representatives: regular A (w 3), fixed A (w 1), regular B (w 3), fixed B (w 1) */
    int r = 0;
    regmask = 0; fixmask = 0;
    for (int ao = 0; ao < AR; ao++) { repv[r] = 3 * ao; regmask |= ((u128)1) << r; r++; }
    for (int k = 0; k < FA; k++) { repv[r] = 3 * AR + k; fixmask |= ((u128)1) << r; r++; }
    for (int bo = 0; bo < BR; bo++) { repv[r] = m + 3 * bo; regmask |= ((u128)1) << r; r++; }
    for (int k = 0; k < FB; k++) { repv[r] = m + 3 * BR + k; fixmask |= ((u128)1) << r; r++; }
    fullmask = (R == 128) ? ~(u128)0 : ((((u128)1) << R) - 1);

    fprintf(stderr, "m=%d n=%d FA=%d FB=%d AR=%d BR=%d E=%d reps=%d\n", m, n, FA, FB, AR, BR, E, R);
    const char *initf = getenv("INIT");
    if (initf) { load_file(initf); have_init = 1; }
    if (getenv("ILS")) {
        ils_search(atof(getenv("ILS")), getenv("KICK") ? atoi(getenv("KICK")) : 4,
                   getenv("ILST") ? atof(getenv("ILST")) : 1.0, getenv("ILSSTEPS") ? atol(getenv("ILSSTEPS")) : 20000, outp);
        return 0;
    }
    if (getenv("TABU")) {
        if (!have_init) { random_init(); }
        tabu_search(atof(getenv("TABU")), getenv("TENURE") ? atoi(getenv("TENURE")) : 10, outp);
        return 0;
    }
    if (getenv("EVAL")) {
        long c0 = cost();
        printf("EVAL cost=%ld\n", c0);
        if (c0 == 0) write_edges(outp_eval_path());
        return 0;
    }
    double w0 = wall();
    long best = 1L << 40;
    long total_moves = 0, runs = 0;
    double elapsed = 0;
    while (elapsed < secs) {
        if (have_init && (runs == 0 || getenv("INIT_EVERY"))) { /* start from INIT */ } else random_init();
        long c = cost();
        nw_cur = nw_new; memcpy(wv_cur, wv_new, sizeof(int) * nw_new); memcpy(wm_cur, wm_new, sizeof(u128) * nw_new);
        long run_best = c;
        double lr = log(T1 / T0);
        for (long s = 0; s < steps; s++) {
            double T = T0 * exp(lr * (double)s / (double)steps);
            save(&bak_s);
            if (!propose()) continue;
            total_moves++;
            long c2 = cost();
            if (c2 <= c || rnd01() < exp(-(double)(c2 - c) / T)) {
                c = c2;
                nw_cur = nw_new; memcpy(wv_cur, wv_new, sizeof(int) * nw_new); memcpy(wm_cur, wm_new, sizeof(u128) * nw_new);
                if (c < run_best) run_best = c;
                if (c < best) {
                    best = c; save(&best_s);
                    char path[512]; snprintf(path, sizeof path, "%s_best.edges", outp);
                    cost(); write_edges(path);
                    elapsed = wall() - w0;
                    fprintf(stderr, "  new best %ld at run %ld step %ld t=%.1fs\n", best, runs, s, elapsed);
                }
                if (c == 0) {
                    char path[512]; snprintf(path, sizeof path, "%s_sol.edges", outp);
                    cost(); write_edges(path);
                    printf("SOLUTION m=%d FA=%d FB=%d n=%d written %s\n", m, FA, FB, n, path);
                    return 0;
                }
            } else {
                load(&bak_s);
            }
        }
        runs++;
        elapsed = wall() - w0;
        fprintf(stderr, "run %ld: run_best %ld final %ld (best so far %ld) t=%.1fs\n", runs, run_best, c, best, elapsed);
    }
    { char path[512]; snprintf(path, sizeof path, "%s_best.state", outp); load(&best_s); write_state(path); }
    printf("DONE m=%d FA=%d FB=%d n=%d best_far=%ld runs=%ld moves=%ld\n", m, FA, FB, n, best, runs, total_moves);
    return 1;
}
