/* surg.c (card a3): delete-and-rematch surgery annealer for bipartite cubic graphs, cost = far pairs at D.
   usage: surg IN.edges D target seconds seed OUT.edges [T0 T1 fracdel greedy_s pdel]
   State: cubic bipartite graph on the live subset of the input vertices (ids fixed, live flags).
   Moves: 2-switch (degree preserving), delete-pair-and-rematch (delete live a in A and b in B, rewire the
   2-3 deficient neighbours on each side by a simple perfect matching avoiding existing edges; live size -2).
   Schedule: live size is pushed from n0 down to target by forced greedy deletions (best of greedy_s guided
   candidates), SA over the rest. Cost: exact far-pair count by bitset ball recurrence (single thread). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>
#include <limits.h>

#define NMAX 1024
#define WMAX 16

typedef struct {
    int adj[NMAX][3];
    int live[NMAX];
    int lst[2][NMAX];
    int cnt[2];
} State;

static State S0, S1, SB;
static State *cur, *cand;
static uint64_t BUF0[NMAX][WMAX], BUF1[NMAX][WMAX];
static int side[NMAX];
static int farlist[NMAX], nfar;
static int curfar[NMAX], ncurfar;
static int n, D, W;
static int dummy_ = 0;
static uint64_t rs = 88172645463325252ULL;

static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline int rndi(int m) { return (int)(rnd() % (uint64_t)m); }
static inline double rndu(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) { struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts); return ts.tv_sec + 1e-9 * ts.tv_nsec; }

static int perms[4][6][3]; static int nperm[4];

static void kill_v(State *c, int v) {
    int s = side[v], k;
    for (k = 0; k < c->cnt[s]; k++) if (c->lst[s][k] == v) break;
    c->lst[s][k] = c->lst[s][c->cnt[s] - 1];
    c->cnt[s]--;
    c->live[v] = 0;
}

/* exact far-pair count for state s; fills farlist with live vertices that have far partners */
static long eval(const State *s) {
    int L = s->cnt[0] + s->cnt[1], k, v, w, t, s2;
    uint64_t (*c)[WMAX] = BUF0, (*x)[WMAX] = BUF1, (*tmp)[WMAX];
    for (s2 = 0; s2 < 2; s2++)
        for (k = 0; k < s->cnt[s2]; k++) {
            v = s->lst[s2][k];
            memset(c[v], 0, sizeof(uint64_t) * W);
            c[v][v >> 6] |= 1ULL << (v & 63);
        }
    for (t = 0; t < D; t++) {
        for (s2 = 0; s2 < 2; s2++)
            for (k = 0; k < s->cnt[s2]; k++) {
                v = s->lst[s2][k];
                const int *a = s->adj[v];
                const uint64_t *p0 = c[a[0]], *p1 = c[a[1]], *p2 = c[a[2]], *p = c[v];
                for (w = 0; w < W; w++) x[v][w] = p[w] | p0[w] | p1[w] | p2[w];
            }
        tmp = c; c = x; x = tmp;
    }
    long tot = 0; nfar = 0;
    for (s2 = 0; s2 < 2; s2++)
        for (k = 0; k < s->cnt[s2]; k++) {
            v = s->lst[s2][k];
            int pc = 0;
            for (w = 0; w < W; w++) pc += __builtin_popcountll(c[v][w]);
            int f = L - pc;
            tot += f;
            if (f > 0) farlist[nfar++] = v;
        }
    return tot / 2;
}

static int contains(const int *arr, int v) { return arr[0] == v || arr[1] == v || arr[2] == v; }
static void repl(int *arr, int oldv, int newv) { int k; for (k = 0; k < 3; k++) if (arr[k] == oldv) { arr[k] = newv; return; } }
static void fill(int *arr, int v) { int k; for (k = 0; k < 3; k++) if (arr[k] < 0) { arr[k] = v; return; } }

/* degree-preserving 2-switch on live graph */
static int twoswitch(State *c) {
    int a1 = c->lst[0][rndi(c->cnt[0])], a2 = c->lst[0][rndi(c->cnt[0])];
    if (a1 == a2) return 0;
    int b1 = c->adj[a1][rndi(3)], b2 = c->adj[a2][rndi(3)];
    if (b1 == b2) return 0;
    if (contains(c->adj[a1], b2) || contains(c->adj[a2], b1)) return 0;
    repl(c->adj[a1], b1, b2); repl(c->adj[a2], b2, b1);
    repl(c->adj[b1], a1, a2); repl(c->adj[b2], a2, a1);
    return 1;
}

/* delete live y (side A) and z (side B), rewire deficient neighbours by a random valid perfect matching */
static int dr_move(State *c, int y, int z) {
    int Ny[3], Nz[3], p = 0, q = 0, i, j, k, a, b, nv = 0, valid[6], pick;
    for (k = 0; k < 3; k++) { b = c->adj[y][k]; if (b != z) Ny[p++] = b; }
    for (k = 0; k < 3; k++) { a = c->adj[z][k]; if (a != y) Nz[q++] = a; }
    if (p != q) return 0;
    for (i = 0; i < p; i++) { b = Ny[i]; for (k = 0; k < 3; k++) if (c->adj[b][k] == y) { c->adj[b][k] = -1; break; } }
    for (i = 0; i < p; i++) { a = Nz[i]; for (k = 0; k < 3; k++) if (c->adj[a][k] == z) { c->adj[a][k] = -1; break; } }
    kill_v(c, y); kill_v(c, z);
    for (k = 0; k < nperm[p]; k++) {
        int ok = 1;
        for (i = 0; i < p && ok; i++) {
            a = Nz[i]; b = Ny[perms[p][k][i]];
            if (contains(c->adj[a], b)) ok = 0;
        }
        if (ok) valid[nv++] = k;
    }
    if (!nv) return 0;
    pick = valid[rndi(nv)];
    for (i = 0; i < p; i++) {
        a = Nz[i]; b = Ny[perms[p][pick][i]];
        fill(c->adj[a], b); fill(c->adj[b], a);
    }
    return 1;
}

static void pick_pair(const State *c, int *y, int *z) {
    if (ncurfar > 0 && rndu() < 0.5) {
        int w = curfar[rndi(ncurfar)];
        if (side[w] == 0) { *y = w; *z = c->lst[1][rndi(c->cnt[1])]; }
        else { *z = w; *y = c->lst[0][rndi(c->cnt[0])]; }
    } else {
        *y = c->lst[0][rndi(c->cnt[0])]; *z = c->lst[1][rndi(c->cnt[1])];
    }
}

static void write_out(const State *c, const char *path) {
    static int id[NMAX]; int L = 0, s2, k, i;
    for (s2 = 0; s2 < 2; s2++) for (k = 0; k < c->cnt[s2]; k++) id[c->lst[s2][k]] = L++;
    FILE *f = fopen(path, "w"); if (!f) { perror(path); exit(1); }
    fprintf(f, "%d\n", L);
    for (k = 0; k < c->cnt[0]; k++) {
        int a = c->lst[0][k];
        for (i = 0; i < 3; i++) fprintf(f, "%d %d\n", id[a], id[c->adj[a][i]]);
    }
    fclose(f);
}

int main(int argc, char **argv) {
    if (argc < 7) { fprintf(stderr, "usage: surg IN D target seconds seed OUT [T0 T1 fracdel greedy_s pdel]\n"); return 2; }
    const char *in = argv[1]; D = atoi(argv[2]); int target = atoi(argv[3]);
    double secs = atof(argv[4]); rs ^= (uint64_t)atoll(argv[5]) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 10; i++) rnd();
    const char *out = argv[6];
    double T0 = argc > 7 ? atof(argv[7]) : 2.0, T1 = argc > 8 ? atof(argv[8]) : 0.2;
    double fracdel = argc > 9 ? atof(argv[9]) : 0.8; int gs = argc > 10 ? atoi(argv[10]) : 30;
    double pdel = argc > 11 ? atof(argv[11]) : 0.02;
    long dthr = argc > 12 ? atol(argv[12]) : 1000000000L; long dwait = argc > 13 ? atol(argv[13]) : 3000;
    long lastdel = -dwait;
    perms[1][0][0] = 0; nperm[1] = 1;
    nperm[2] = 2; perms[2][0][0] = 0; perms[2][0][1] = 1; perms[2][1][0] = 1; perms[2][1][1] = 0;
    { int pp[6][3] = {{0,1,2},{0,2,1},{1,0,2},{1,2,0},{2,0,1},{2,1,0}};
      nperm[3] = 6; memcpy(perms[3], pp, sizeof(pp)); }
    FILE *f = fopen(in, "r"); if (!f) { perror(in); return 2; }
    if (fscanf(f, "%d", &n) != 1) return 2;
    if (n > NMAX) { fprintf(stderr, "n too big\n"); return 2; }
    W = (n + 63) / 64;
    static int deg[NMAX];
    State *st0 = &S0; memset(st0, 0, sizeof(State));
    int u, v; long m = 0;
    while (fscanf(f, "%d %d", &u, &v) == 2) {
        if (deg[u] >= 3 || deg[v] >= 3) { fprintf(stderr, "not cubic\n"); return 2; }
        st0->adj[u][deg[u]++] = v; st0->adj[v][deg[v]++] = u; m++;
    }
    fclose(f);
    for (v = 0; v < n; v++) if (deg[v] != 3) { fprintf(stderr, "not cubic at %d\n", v); return 2; }
    /* 2-colour */
    for (v = 0; v < n; v++) side[v] = -1;
    { static int q[NMAX]; int qh = 0, qt = 0; side[0] = 0; q[qt++] = 0;
      while (qh < qt) { int x = q[qh++]; for (int k = 0; k < 3; k++) { int y = st0->adj[x][k];
          if (side[y] < 0) { side[y] = 1 - side[x]; q[qt++] = y; }
          else if (side[y] == side[x]) { fprintf(stderr, "not bipartite\n"); return 2; } } }
      if (qt != n) { fprintf(stderr, "not connected\n"); return 2; } }
    for (v = 0; v < n; v++) { st0->live[v] = 1; st0->lst[side[v]][st0->cnt[side[v]]++] = v; }
    cur = &S1; cand = &S0; /* S0 holds the input state; copy it */
    memcpy(cur, st0, sizeof(State)); cand = &S0;
    long curc = eval(cur);
    ncurfar = nfar; memcpy(curfar, farlist, sizeof(int) * nfar);
    int L0 = cur->cnt[0] + cur->cnt[1];
    int ND = (L0 - target) / 2;
    fprintf(stderr, "loaded n=%d m=%ld D=%d target=%d cost=%ld far-vertices=%d T0=%g T1=%g\n", n, m, D, target, curc, ncurfar, T0, T1);
    double t0 = now(), el = 0, f_ = 0, lastprint = 0;
    long iter = 0, acc = 0, tried = 0; long bestAtL[NMAX]; for (int i = 0; i < NMAX; i++) bestAtL[i] = LONG_MAX;
    int done = 0;
    while (!done) {
        if ((iter & 63) == 0) {
            el = now() - t0;
            if (el >= secs) break;
            f_ = el / secs;
            if (el - lastprint > 15) {
                lastprint = el;
                fprintf(stderr, "t=%.0f L=%d cost=%ld best@L=%ld acc=%.3f\n", el, cur->cnt[0] + cur->cnt[1], curc,
                        bestAtL[cur->cnt[0] + cur->cnt[1]] == LONG_MAX ? -1L : bestAtL[cur->cnt[0] + cur->cnt[1]],
                        tried ? (double)acc / tried : 0.0);
            }
        }
        iter++;
        int L = cur->cnt[0] + cur->cnt[1];
        if (curc < bestAtL[L]) bestAtL[L] = curc;
        if (L > target && curc <= dthr && iter - lastdel >= dwait) {
            lastdel = iter;
            /* forced greedy deletion */
            long bc = LONG_MAX; int got = 0;
            for (int g = 0; g < gs; g++) {
                memcpy(cand, cur, sizeof(State));
                int y, z; pick_pair(cand, &y, &z);
                if (!dr_move(cand, y, z)) continue;
                long cc = eval(cand);
                if (cc < bc || (cc == bc && rndi(2))) { bc = cc; memcpy(&SB, cand, sizeof(State)); got = 1; }
            }
            if (!got) continue;
            memcpy(cur, &SB, sizeof(State));
            curc = eval(cur); ncurfar = nfar; memcpy(curfar, farlist, sizeof(int) * nfar);
            L = cur->cnt[0] + cur->cnt[1];
            fprintf(stderr, "del t=%.1f L=%d cost=%ld T=%.3f\n", el, L, curc, T0 * pow(T1 / T0, f_));
            if (curc < bestAtL[L]) bestAtL[L] = curc;
            if (curc == 0 && L >= target) { write_out(cur, out); fprintf(stderr, "VALID-CANDIDATE L=%d written\n", L); if (L == target) done = 1; }
            continue;
        }
        double T = T0 * pow(T1 / T0, f_);
        memcpy(cand, cur, sizeof(State));
        int ok;
        if (L > target && rndu() < pdel) { int y, z; pick_pair(cand, &y, &z); ok = dr_move(cand, y, z); }
        else ok = twoswitch(cand);
        if (!ok) continue;
        tried++;
        long cc = eval(cand);
        long delta = cc - curc;
        if (delta <= 0 || rndu() < exp(-(double)delta / T)) {
            State *tmp = cur; cur = cand; cand = tmp; curc = cc; acc++;
            ncurfar = nfar; memcpy(curfar, farlist, sizeof(int) * nfar);
            int L2 = cur->cnt[0] + cur->cnt[1];
            if (curc < bestAtL[L2]) bestAtL[L2] = curc;
            if (curc == 0 && L2 >= target) {
                write_out(cur, out); fprintf(stderr, "VALID-CANDIDATE L=%d written\n", L2);
                if (L2 == target) done = 1;
            }
        }
    }
    fprintf(stderr, "end t=%.1f iters=%ld L=%d cost=%ld\n", now() - t0, iter, cur->cnt[0] + cur->cnt[1], curc);
    char endp[4096]; snprintf(endp, sizeof endp, "%s.end", out);
    write_out(cur, endp);
    printf("RESULT L=%d cost=%ld\n", cur->cnt[0] + cur->cnt[1], curc);
    return 0;
}
