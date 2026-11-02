/* bcub: anneal cubic bipartite graphs under bipartiteness-preserving 2-switches.
   usage: bcub n D secs seed T0 T1 OUT [INIT_EDGE_LIST]
   vertices A = 0..h-1, B = h..n-1 (h = n/2). cost = #ordered pairs at distance > D (exact, bit-parallel).
   writes OUT (edge list, first line n) when cost 0 is reached, and OUT.best with the best state seen. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

static int n, h, W, D, m;
static int *adj;        /* adj[3*v+k] */
static int *ea, *eb;    /* edge i = (ea[i] in A, eb[i] in B) */
static uint64_t *R0, *R1;
static uint64_t rs = 88172645463325252ull;
static int *blist, *blist2, nb, nb2; static int target = 0;

static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static double urand(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }

static void repl(int v, int oldv, int newv) {
    for (int k = 0; k < 3; k++) if (adj[3 * v + k] == oldv) { adj[3 * v + k] = newv; return; }
    fprintf(stderr, "bug: repl\n"); exit(1);
}
static int isadj(int a, int b) { for (int k = 0; k < 3; k++) if (adj[3 * a + k] == b) return 1; return 0; }

/* edge i = (a1,b1), j = (a2,b2)  ->  i = (a1,b2), j = (a2,b1). Calling it again on (i,j) undoes it. */
static void doswitch(int i, int j) {
    int a1 = ea[i], b1 = eb[i], a2 = ea[j], b2 = eb[j];
    repl(a1, b1, b2); repl(a2, b2, b1); repl(b1, a1, a2); repl(b2, a2, a1);
    eb[i] = b2; eb[j] = b1;
}

static long cost(void) {
    uint64_t *P = R0, *Q = R1;
    memset(P, 0, sizeof(uint64_t) * (size_t)n * W);
    for (int v = 0; v < n; v++) P[(size_t)v * W + v / 64] |= 1ull << (v % 64);
    for (int k = 0; k < D; k++) {
        for (int v = 0; v < n; v++) {
            uint64_t *q = Q + (size_t)v * W;
            const uint64_t *p = P + (size_t)v * W;
            const uint64_t *p0 = P + (size_t)adj[3 * v] * W;
            const uint64_t *p1 = P + (size_t)adj[3 * v + 1] * W;
            const uint64_t *p2 = P + (size_t)adj[3 * v + 2] * W;
            for (int w = 0; w < W; w++) q[w] = p[w] | p0[w] | p1[w] | p2[w];
        }
        uint64_t *t = P; P = Q; Q = t;
    }
    long bad = 0; nb2 = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += __builtin_popcountll(P[(size_t)v * W + w]);
        bad += n - c;
        if (c < n) blist2[nb2++] = v;
    }
    return bad;
}

static void write_edges(const char *fn, const int *A, const int *B) {
    FILE *f = fopen(fn, "w");
    if (!f) { perror(fn); return; }
    fprintf(f, "%d\n", n);
    for (int i = 0; i < m; i++) fprintf(f, "%d %d\n", A[i], B[i]);
    fclose(f);
}

int main(int argc, char **argv) {
    if (argc < 8) { fprintf(stderr, "usage: bcub n D secs seed T0 T1 OUT [INIT]\n"); return 1; }
    n = atoi(argv[1]); D = atoi(argv[2]); double secs = atof(argv[3]);
    rs ^= (uint64_t)atoll(argv[4]) * 0x9E3779B97F4A7C15ull; for (int i = 0; i < 10; i++) rnd();
    double T0 = atof(argv[5]), T1 = atof(argv[6]); const char *OUT = argv[7];
    h = n / 2; m = 3 * h; W = (n + 63) / 64;
    adj = malloc(sizeof(int) * 3 * n); ea = malloc(sizeof(int) * m); eb = malloc(sizeof(int) * m);
    blist = malloc(sizeof(int) * n); blist2 = malloc(sizeof(int) * n);
    target = getenv("TARGET") ? atoi(getenv("TARGET")) : 0;
    R0 = malloc(sizeof(uint64_t) * (size_t)n * W); R1 = malloc(sizeof(uint64_t) * (size_t)n * W);
    int *bestA = malloc(sizeof(int) * m), *bestB = malloc(sizeof(int) * m);
    if (argc > 8) {
        FILE *f = fopen(argv[8], "r"); int nn; if (!f || fscanf(f, "%d", &nn) != 1 || nn != n) { fprintf(stderr, "bad init\n"); return 1; }
        int cnt[n]; memset(cnt, 0, sizeof cnt);
        int ec = 0, u, v;
        while (fscanf(f, "%d %d", &u, &v) == 2) {
            int a = u < h ? u : v, b = u < h ? v : u;
            if (ec >= m) { fprintf(stderr, "too many edges\n"); return 1; }
            ea[ec] = a; eb[ec] = b; ec++;
            adj[3 * a + cnt[a]++] = b; adj[3 * b + cnt[b]++] = a;
        }
        fclose(f);
        for (int x = 0; x < n; x++) if (cnt[x] != 3) { fprintf(stderr, "not cubic\n"); return 1; }
    } else {
        int c[n]; memset(c, 0, sizeof c);
        for (int a = 0; a < h; a++) {
            int offs[3] = {0, 1, 3};
            for (int k = 0; k < 3; k++) {
                int b = h + (a + offs[k]) % h;
                adj[3 * a + k] = b; adj[3 * b + c[b]++] = a;
                ea[3 * a + k] = a; eb[3 * a + k] = b;
            }
        }
        /* randomize: accepted random 2-switches */
        int done = 0;
        while (done < 40 * m) {
            int i = rnd() % m, j = rnd() % m; if (i == j) continue;
            int a1 = ea[i], b1 = eb[i], a2 = ea[j], b2 = eb[j];
            if (a1 == a2 || b1 == b2 || isadj(a1, b2) || isadj(a2, b1)) continue;
            doswitch(i, j); done++;
        }
    }
    long cur = cost(), best = cur;
    { int *t = blist; blist = blist2; blist2 = t; nb = nb2; }
    memcpy(bestA, ea, sizeof(int) * m); memcpy(bestB, eb, sizeof(int) * m);
    fprintf(stderr, "n=%d D=%d init cost %ld\n", n, D, cur);
    double t0 = now(), T = T0, lastp = t0; long iter = 0, acc = 0;
    while (cur > 0) {
        if ((iter & 7) == 0) {
            double el = now() - t0;
            if (el > secs) break;
            T = T0 * pow(T1 / T0, el / secs);
            if (now() - lastp > 10) { lastp = now(); fprintf(stderr, "  t=%.0f it=%ld cur=%ld best=%ld T=%.3f acc=%ld\n", el, iter, cur, best, T, acc); }
        }
        int i, j;
        if (target && nb > 0 && rnd() % 4) {
            int u = blist[rnd() % nb];
            int x = (rnd() & 1) ? u : adj[3 * u + rnd() % 3];
            int cand[8], nc = 0;
            for (int e = 0; e < m; e++) if ((ea[e] == x || eb[e] == x) && nc < 8) cand[nc++] = e;
            i = cand[rnd() % nc];
        } else i = rnd() % m;
        j = rnd() % m; if (i == j) continue;
        int a1 = ea[i], b1 = eb[i], a2 = ea[j], b2 = eb[j];
        if (a1 == a2 || b1 == b2 || isadj(a1, b2) || isadj(a2, b1)) continue;
        doswitch(i, j);
        long c = cost();
        if (c <= cur || urand() < exp(-(double)(c - cur) / T)) {
            cur = c; acc++;
            { int *t = blist; blist = blist2; blist2 = t; nb = nb2; }
            if (cur < best) { best = cur; memcpy(bestA, ea, sizeof(int) * m); memcpy(bestB, eb, sizeof(int) * m); }
        } else doswitch(i, j);
        iter++;
    }
    fprintf(stderr, "done it=%ld cur=%ld best=%ld evals/s=%.1f\n", iter, cur, best, iter / (now() - t0));
    char fn[512]; snprintf(fn, sizeof fn, "%s.best", OUT);
    /* best snapshot: vertices of B are already h..n-1 */
    int *A2 = bestA, *B2 = bestB;
    write_edges(fn, A2, B2);
    if (best == 0) write_edges(OUT, A2, B2);
    printf("n=%d D=%d best=%ld\n", n, D, best);
    return 0;
}
