/* c20 dsa.c: DOWNWARD surgery. Start from a bipartite graph (max degree 6) on n0 vertices, delete DELA vertices of
 * side A and DELB vertices of side B (greedy by exact cost, or random), add edges between deficient opposite-side
 * vertices, then simulated annealing with moves: 2-switch (degree-preserving), deficit move (move one edge end to a
 * deficient vertex), and greedy ADD (never increases cost). Cost = unordered pairs at distance > 5 (bit-parallel BFS).
 * env: INFILE, DELA (0), DELB (0), DELMODE (greedy|rand, greedy), SAMPLE (60: candidates per greedy step),
 *      SEED (1), T0 (1.0), T1 (0.2), SECS (120), OUT (dsa_best.edges), TARGET (0 = stop at cost 0)
 * Writes OUT on every improvement of the best cost. Edge list format as check.sh: "n" then "u v" lines (0-based). */
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 1024
#define W 16
#define MAXE (6 * MAXN)
typedef uint64_t u64;

static int n, nw, ne;
static int side[MAXN];
static int adj[MAXN][6], deg[MAXN];
static int EA[MAXE], EB[MAXE];
static u64 LA[MAXN][W], LB[MAXN][W];
static uint64_t rs = 88172645463325252ULL;

static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline double urand(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }

static int has_edge(int a, int b) {
    for (int k = 0; k < deg[a]; k++) if (adj[a][k] == b) return 1;
    return 0;
}
static void rep(int v, int old, int nv) {
    for (int k = 0; k < deg[v]; k++) if (adj[v][k] == old) { adj[v][k] = nv; return; }
    fprintf(stderr, "rep failed\n"); exit(1);
}
static void rebuild_adj(void) {
    memset(deg, 0, sizeof deg);
    for (int i = 0; i < ne; i++) { adj[EA[i]][deg[EA[i]]++] = EB[i]; adj[EB[i]][deg[EB[i]]++] = EA[i]; }
}
static long cost(void) {
    static u64 (*cur)[W], (*nxt)[W];
    nw = (n + 63) >> 6;
    cur = LA; nxt = LB;
    for (int v = 0; v < n; v++) {
        memset(cur[v], 0, nw * 8);
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int k = 0; k < 5; k++) {
        for (int v = 0; v < n; v++) {
            u64 *d = nxt[v];
            memcpy(d, cur[v], nw * 8);
            for (int t = 0; t < deg[v]; t++) {
                u64 *s = cur[adj[v][t]];
                for (int w = 0; w < nw; w++) d[w] |= s[w];
            }
        }
        u64 (*tmp)[W] = cur; cur = nxt; nxt = tmp;
    }
    long bad = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < nw; w++) c += __builtin_popcountll(cur[v][w]);
        bad += n - c;
    }
    return bad / 2;
}
static void write_edges(const char *fn) {
    FILE *f = fopen(fn, "w"); if (!f) return;
    fprintf(f, "%d\n", n);
    for (int i = 0; i < ne; i++) fprintf(f, "%d %d\n", EA[i], EB[i]);
    fclose(f);
}
/* load edge list, 2-colour */
static void load(const char *fn) {
    FILE *f = fopen(fn, "r"); if (!f) { perror(fn); exit(1); }
    int m; if (fscanf(f, "%d", &n) != 1) exit(1);
    static int U[MAXE], V[MAXE]; m = 0;
    while (fscanf(f, "%d %d", &U[m], &V[m]) == 2) m++;
    fclose(f);
    static int col[MAXN], q[MAXN];
    for (int v = 0; v < n; v++) col[v] = -1;
    static int st[MAXN + 1], al[2 * MAXE], fill[MAXN];
    memset(st, 0, sizeof st); memset(fill, 0, sizeof fill);
    for (int i = 0; i < m; i++) { st[U[i] + 1]++; st[V[i] + 1]++; }
    for (int v = 0; v < n; v++) st[v + 1] += st[v];
    for (int i = 0; i < m; i++) { al[st[U[i]] + fill[U[i]]++] = V[i]; al[st[V[i]] + fill[V[i]]++] = U[i]; }
    int h = 0, t = 0;
    for (int s = 0; s < n; s++) if (col[s] < 0) {
        col[s] = 0; q[t++] = s;
        while (h < t) { int x = q[h++]; for (int k = st[x]; k < st[x + 1]; k++) { int y = al[k]; if (col[y] < 0) { col[y] = 1 - col[x]; q[t++] = y; } else if (col[y] == col[x]) { fprintf(stderr, "not bipartite\n"); exit(1); } } }
    }
    for (int v = 0; v < n; v++) side[v] = col[v];
    ne = 0;
    for (int i = 0; i < m; i++) {
        int a = U[i], b = V[i];
        if (side[a] == 1) { int tmp = a; a = b; b = tmp; }
        EA[ne] = a; EB[ne] = b; ne++;
    }
    rebuild_adj();
}
/* delete vertex x: drop its edges, renumber others, rebuild */
static void delete_vertex(int x) {
    int k = 0;
    for (int i = 0; i < ne; i++) {
        if (EA[i] == x || EB[i] == x) continue;
        EA[k] = EA[i] - (EA[i] > x); EB[k] = EB[i] - (EB[i] > x); k++;
    }
    ne = k;
    for (int v = x; v + 1 < n; v++) side[v] = side[v + 1];
    n--;
    rebuild_adj();
}
static int adj_free(int v) { return deg[v] < 6; }
/* add edges between deficient opposite-side pairs, random order, up to `tries` attempts */
static int add_pass(int tries) {
    int added = 0;
    static int DA[MAXN], DB[MAXN];
    for (int it = 0; it < tries; it++) {
        int na = 0, nb = 0;
        for (int v = 0; v < n; v++) if (adj_free(v)) { if (side[v] == 0) DA[na++] = v; else DB[nb++] = v; }
        if (!na || !nb) break;
        int a = DA[rnd() % na], b = DB[rnd() % nb];
        if (has_edge(a, b)) continue;
        EA[ne] = a; EB[ne] = b; ne++;
        adj[a][deg[a]++] = b; adj[b][deg[b]++] = a;
        added++;
    }
    return added;
}
static void swap_edges(int i, int j) {
    int a1 = EA[i], b1 = EB[i], a2 = EA[j], b2 = EB[j];
    rep(a1, b1, b2); rep(b1, a1, a2); rep(a2, b2, b1); rep(b2, a2, a1);
    EB[i] = b2; EB[j] = b1;
}
/* greedy fill: repeatedly add the deficient opposite-side pair (sampled) with the lowest exact cost */
static long greedy_fill(int samples) {
    static int DA[MAXN], DB[MAXN];
    long c = cost();
    for (;;) {
        int na = 0, nb = 0;
        for (int v = 0; v < n; v++) if (adj_free(v)) { if (side[v] == 0) DA[na++] = v; else DB[nb++] = v; }
        if (!na || !nb) break;
        long bc = 1L << 60; int ba = -1, bb = -1;
        for (int s_ = 0; s_ < samples; s_++) {
            int a = DA[rnd() % na], b = DB[rnd() % nb];
            if (has_edge(a, b)) continue;
            EA[ne] = a; EB[ne] = b; ne++;
            adj[a][deg[a]++] = b; adj[b][deg[b]++] = a;
            long cc = cost();
            deg[a]--; deg[b]--; ne--;
            if (cc < bc) { bc = cc; ba = a; bb = b; }
        }
        if (ba < 0) { /* fall back to any non-adjacent pair */
            int added = add_pass(100000); (void)added; c = cost(); break;
        }
        EA[ne] = ba; EB[ne] = bb; ne++;
        adj[ba][deg[ba]++] = bb; adj[bb][deg[bb]++] = ba;
        c = bc;
    }
    return c;
}

/* deficit move: deficient d (side s) takes a new neighbour p (full, opposite side, not adjacent to d) in place of one of
 * p's neighbours q: edge (p,q) becomes (p,d); q loses 1 degree, d gains 1. Returns 0 if no move was possible. */
static int defmove_pick(int d, int *pp, int *pq, int *pi) {
    int opp = 1 - side[d];
    for (int tries = 0; tries < 50; tries++) {
        int p = -1;
        /* random full vertex on opposite side */
        int v = rnd() % n;
        if (side[v] != opp || deg[v] < 6 || has_edge(v, d)) continue;
        p = v;
        int q = adj[p][rnd() % deg[p]];
        int idx = -1;
        for (int i = 0; i < ne; i++) if ((EA[i] == p && EB[i] == q) || (EA[i] == q && EB[i] == p)) { idx = i; break; }
        if (idx < 0) continue;
        *pp = p; *pq = q; *pi = idx; return 1;
    }
    return 0;
}
/* set the endpoint of edge i that is not p to nq (p keeps its place) */
static void set_other(int i, int p, int nq) {
    int q = (EA[i] == p) ? EB[i] : EA[i];
    rep(p, q, nq);
    /* remove p from q's list */
    for (int k = 0; k < deg[q]; k++) if (adj[q][k] == p) { adj[q][k] = adj[q][deg[q] - 1]; deg[q]--; break; }
    adj[nq][deg[nq]++] = p;
    if (EA[i] == p) EB[i] = nq; else EA[i] = nq;
}
static int find_deficient(void) {
    int cnt = 0; static int D[MAXN];
    for (int v = 0; v < n; v++) if (deg[v] < 6) D[cnt++] = v;
    return cnt ? D[rnd() % cnt] : -1;
}
int main(void) {
    const char *in = getenv("INFILE"); if (!in) { fprintf(stderr, "INFILE\n"); return 1; }
    int DELA = getenv("DELA") ? atoi(getenv("DELA")) : 0;
    int DELB = getenv("DELB") ? atoi(getenv("DELB")) : 0;
    const char *mode = getenv("DELMODE") ? getenv("DELMODE") : "greedy";
    int SAMPLE = getenv("SAMPLE") ? atoi(getenv("SAMPLE")) : 60;
    rs ^= (getenv("SEED") ? (uint64_t)atoll(getenv("SEED")) : 1ULL) * 0x9E3779B97F4A7C15ULL;
    for (int i = 0; i < 10; i++) rnd();
    double T0 = getenv("T0") ? atof(getenv("T0")) : 1.0;
    double T1 = getenv("T1") ? atof(getenv("T1")) : 0.2;
    double SECS = getenv("SECS") ? atof(getenv("SECS")) : 120;
    const char *out = getenv("OUT") ? getenv("OUT") : "dsa_best.edges";
    long TARGET = getenv("TARGET") ? atol(getenv("TARGET")) : 0;
    double DEFP = getenv("DEFP") ? atof(getenv("DEFP")) : 0.0;
    load(in);
    int n0 = n;
    /* deletions */
    int dels = DELA + DELB;
    for (int d = 0; d < dels; d++) {
        int wantside = (d < DELA) ? 0 : 1;   /* do A first then B; counts per side */
        if (d >= DELA) wantside = 1;
        int best = -1; long bestc = 1L << 60;
        int cnt = 0;
        int cand[MAXN];
        for (int v = 0; v < n; v++) if (side[v] == wantside) cand[cnt++] = v;
        if (!strcmp(mode, "rand")) {
            best = cand[rnd() % cnt];
        } else {
            /* sample candidates; exact cost after deleting each (copy state) */
            static int SA_[MAXE], SB_[MAXE], sn; sn = ne;
            static int ssd[MAXN]; int sn_ = n; memcpy(ssd, side, sizeof side);
            memcpy(SA_, EA, sizeof(int) * ne); memcpy(SB_, EB, sizeof(int) * ne);
            int S = SAMPLE < cnt ? SAMPLE : cnt;
            for (int s = 0; s < S; s++) {
                int v = (S == cnt) ? cand[s] : cand[rnd() % cnt];
                /* save */
                static int TA[MAXE], TB[MAXE]; int tn = ne; int tn_n = n; static int tside[MAXN];
                memcpy(TA, EA, sizeof(int) * ne); memcpy(TB, EB, sizeof(int) * ne); memcpy(tside, side, sizeof side);
                delete_vertex(v);
                long c = cost() ;
                /* restore */
                ne = tn; n = tn_n; memcpy(EA, TA, sizeof(int) * ne); memcpy(EB, TB, sizeof(int) * ne); memcpy(side, tside, sizeof side);
                rebuild_adj();
                if (c < bestc) { bestc = c; best = v; }
            }
            (void)sn; (void)sn_; (void)ssd; (void)SA_; (void)SB_;
        }
        delete_vertex(best);
        /* best is an index in the pre-delete numbering; after deleting, indices above it shift: fine since each step recomputes */
        fprintf(stderr, "deleted side %d -> n=%d edges=%d\n", wantside, n, ne);
    }
    int FILLS = getenv("FILLS") ? atoi(getenv("FILLS")) : 0;
    int added = 0;
    if (FILLS > 0) { greedy_fill(FILLS); } else added = add_pass(100000);
    long cur = cost();
    long best = cur;
    fprintf(stderr, "start n0=%d n=%d ne=%d added=%d cost=%ld\n", n0, n, ne, added, cur);
    write_edges(out);
    double t0 = now();
    long iter = 0;
    int nA = 0, nB = 0; for (int v = 0; v < n; v++) { if (side[v]==0) nA++; else nB++; }
    while (1) {
        iter++;
        if ((iter & 255) == 0) {
            double el = now() - t0; if (el > SECS) break;
            double T = T0 * pow(T1 / T0, el / SECS);
            if ((iter & 0xFFFF) == 0) fprintf(stderr, "t %.0f T %.3f cur %ld best %ld\n", el, T, cur, best);
            (void)T;
        }
        double el = now() - t0;
        double T = T0 * pow(T1 / T0, el / SECS);
        /* greedy add first */
        if (add_pass(4)) { cur = cost(); }
        /* deficit move with probability DEFP when deficient vertices exist */
        if (DEFP > 0 && urand() < DEFP) {
            int d = find_deficient();
            if (d >= 0) {
                int p, q, idx;
                if (defmove_pick(d, &p, &q, &idx)) {
                    set_other(idx, p, d);
                    long c = cost();
                    if (c <= cur || urand() < exp(-(c - cur) / T)) {
                        cur = c;
                        if (cur < best) { best = cur; write_edges(out); fprintf(stderr, "NEW BEST %ld n=%d ne=%d iter %ld t %.1f (def)\n", best, n, ne, iter, el); if (best <= TARGET) break; }
                    } else {
                        set_other(idx, p, q);  /* undo */
                    }
                }
                continue;
            }
        }
        /* pick move */
        int i = rnd() % ne, j = rnd() % ne;
        if (i == j) continue;
        int a1 = EA[i], b1 = EB[i], a2 = EA[j], b2 = EB[j];
        if (a1 == a2 || b1 == b2 || has_edge(a1, b2) || has_edge(a2, b1)) continue;
        swap_edges(i, j);
        long c = cost();
        if (c <= cur || urand() < exp(-(c - cur) / T)) {
            cur = c;
            if (cur < best) {
                best = cur;
                write_edges(out);
                fprintf(stderr, "NEW BEST %ld n=%d ne=%d iter %ld t %.1f\n", best, n, ne, iter, el);
                if (best <= TARGET) break;
            }
        } else {
            swap_edges(i, j);  /* undo: after swap, edge i = (a1,b2), j = (a2,b1); swapping again restores */
        }
    }
    printf("RESULT n=%d edges=%d best=%ld cur=%ld iters=%ld\n", n, ne, best, cur, iter);
    return 0;
}
