/* fixp.c: annealer over Z_5-symmetric bipartite (5,5) graphs WITH FIXED VERTICES (non-free group action).
 *
 * Idea (not a lift in the usual sense): Z_5 acts on both sides. Side A has bA free orbits (5 vertices each) and fA
 * fixed vertices; side B has bB free orbits and fB fixed vertices. Free-free base edges (a,b,s) give the lift edges
 * (A,a,h) ~ (B,b,h+s). Every fixed vertex has exactly one "star": a fixed A-vertex x attached to B-orbit j is adjacent
 * to all five vertices (B,j,h) (degree 5); fixed B-vertex y attached to A-orbit i likewise. Free vertices get degree 5
 * from ff edges plus stars. Vertex count = 5(bA+bB) + fA + fB. Degree preserving moves: voltage change, 2-switch of
 * two ff edges (swap B ends), star <-> ff-edge exchange (fixed vertex takes over an ff slot of another orbit).
 * Cost = sum over ALL vertices of the number of vertices at distance > 5, computed from one representative per orbit
 * (free orbit reps counted 5 times). Cost 0 <=> diameter <= 5.
 * usage: fixp bA fA bB fB SECS SEED OUT      (need 5*bA - fB == 5*bB - fA)
 * env: T0 (1.5), T1 (0.15). OUT gets the state (text) and OUT.edges (edge list, written at the end).
 */
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define M 5
#define DEG 5
#define D 5
#define MAXE 1024
#define MAXV 1024
#define MAXF 64

static int bA, fA, bB, fB, NE, NV;
static int ea[MAXE], eb[MAXE], es[MAXE];
static int starA[MAXF], starB[MAXF];
typedef struct { int ea[MAXE], eb[MAXE], es[MAXE], starA[MAXF], starB[MAXF]; } State;
static int adj[MAXV][DEG], dg[MAXV];
static int stamp_[MAXV], st_ = 0, q_[MAXV], dist_[MAXV];

static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline int rint_(int n) { return (int)(rnd() % (uint64_t)n); }
static inline double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }

static inline int VA(int i, int h) { return i * M + h; }
static inline int FA(int x) { return M * bA + x; }
static inline int VB(int j, int h) { return M * bA + fA + j * M + h; }
static inline int FB(int y) { return M * bA + fA + M * bB + y; }

static void addE(int u, int v) {
    if (dg[u] >= DEG || dg[v] >= DEG) { fprintf(stderr, "degree overflow\n"); exit(1); }
    adj[u][dg[u]++] = v; adj[v][dg[v]++] = u;
}

static void build(void) {
    memset(dg, 0, sizeof(int) * NV);
    for (int e = 0; e < NE; e++)
        for (int h = 0; h < M; h++) addE(VA(ea[e], h), VB(eb[e], (h + es[e]) % M));
    for (int x = 0; x < fA; x++)
        for (int h = 0; h < M; h++) addE(FA(x), VB(starA[x], h));
    for (int y = 0; y < fB; y++)
        for (int h = 0; h < M; h++) addE(VA(starB[y], h), FB(y));
}

/* number of vertices within distance D of s */
static int reached(int s) {
    st_++;
    int head = 0, tail = 0, cnt = 0;
    q_[tail++] = s; stamp_[s] = st_; dist_[s] = 0; cnt = 1;
    while (head < tail) {
        int v = q_[head++];
        if (dist_[v] == D) continue;
        for (int i = 0; i < dg[v]; i++) {
            int w = adj[v][i];
            if (stamp_[w] != st_) { stamp_[w] = st_; dist_[w] = dist_[v] + 1; q_[tail++] = w; cnt++; }
        }
    }
    return cnt;
}

static long cost(void) {
    build();
    long c = 0;
    for (int i = 0; i < bA; i++) c += (long)M * (NV - reached(VA(i, 0)));
    for (int j = 0; j < bB; j++) c += (long)M * (NV - reached(VB(j, 0)));
    for (int x = 0; x < fA; x++) c += NV - reached(FA(x));
    for (int y = 0; y < fB; y++) c += NV - reached(FB(y));
    return c;
}

static void save_state(State *s) {
    memcpy(s->ea, ea, sizeof(ea)); memcpy(s->eb, eb, sizeof(eb)); memcpy(s->es, es, sizeof(es));
    memcpy(s->starA, starA, sizeof(starA)); memcpy(s->starB, starB, sizeof(starB));
}
static void load_state(const State *s) {
    memcpy(ea, s->ea, sizeof(ea)); memcpy(eb, s->eb, sizeof(eb)); memcpy(es, s->es, sizeof(es));
    memcpy(starA, s->starA, sizeof(starA)); memcpy(starB, s->starB, sizeof(starB));
}

static void write_edges(const char *fn) {
    build();
    FILE *f = fopen(fn, "w");
    fprintf(f, "%d\n", NV);
    for (int u = 0; u < NV; u++)
        for (int i = 0; i < dg[u]; i++) if (u < adj[u][i]) fprintf(f, "%d %d\n", u, adj[u][i]);
    fclose(f);
}

static void write_state(const char *fn, long best) {
    FILE *f = fopen(fn, "w");
    fprintf(f, "# fixp bA=%d fA=%d bB=%d fB=%d cost=%ld\n", bA, fA, bB, fB, best);
    fprintf(f, "NE %d\n", NE);
    for (int e = 0; e < NE; e++) fprintf(f, "%d %d %d\n", ea[e], eb[e], es[e]);
    for (int x = 0; x < fA; x++) fprintf(f, "starA %d %d\n", x, starA[x]);
    for (int y = 0; y < fB; y++) fprintf(f, "starB %d %d\n", y, starB[y]);
    fclose(f);
}

int main(int argc, char **argv) {
    if (argc < 8) { fprintf(stderr, "usage: fixp bA fA bB fB SECS SEED OUT\n"); return 1; }
    bA = atoi(argv[1]); fA = atoi(argv[2]); bB = atoi(argv[3]); fB = atoi(argv[4]);
    double secs = atof(argv[5]);
    rs ^= (uint64_t)atoll(argv[6]) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 10; i++) rnd();
    const char *out = argv[7];
    double T0 = getenv("T0") ? atof(getenv("T0")) : 1.5, T1 = getenv("T1") ? atof(getenv("T1")) : 0.15;
    NE = M * bA - fB;
    if (NE != M * bB - fA || NE < 0 || fA > MAXF || fB > MAXF || NE > MAXE) { fprintf(stderr, "bad sizes\n"); return 1; }
    NV = M * (bA + bB) + fA + fB;
    if (NV > MAXV) { fprintf(stderr, "too many vertices\n"); return 1; }

    /* random initial stars: fixed B-vertices take A-orbit slots, fixed A-vertices take B-orbit slots */
    int *stA = malloc(sizeof(int) * M * bA), *stB = malloc(sizeof(int) * M * bB);
    int nA = 0, nB = 0;
    for (int i = 0; i < bA; i++) for (int k = 0; k < M; k++) stA[nA++] = i;
    for (int j = 0; j < bB; j++) for (int k = 0; k < M; k++) stB[nB++] = j;
    for (int y = 0; y < fB; y++) { int k = rint_(nA); starB[y] = stA[k]; stA[k] = stA[--nA]; }
    for (int x = 0; x < fA; x++) { int k = rint_(nB); starA[x] = stB[k]; stB[k] = stB[--nB]; }
    /* random matching of the remaining stubs */
    for (int i = nB - 1; i > 0; i--) { int k = rint_(i + 1); int t = stB[i]; stB[i] = stB[k]; stB[k] = t; }
    for (int e = 0; e < NE; e++) { ea[e] = stA[e]; eb[e] = stB[e]; es[e] = rint_(M); }

    long cur = cost(), best = cur;
    State bestS, curS;
    save_state(&bestS);
    double t0 = now(), T = T0;
    long it = 0;
    printf("start cost %ld NV %d NE %d\n", cur, NV, NE);
    while (1) {
        double el = now() - t0;
        if (el > secs) break;
        if ((it & 255) == 0) T = T0 * pow(T1 / T0, el / secs);
        it++;
        save_state(&curS);
        int mv = rint_(10);
        if (mv < 4) { /* voltage change */
            int e = rint_(NE); es[e] = (es[e] + 1 + rint_(M - 1)) % M;
        } else if (mv < 7) { /* 2-switch of two ff edges (swap B ends) */
            if (NE < 2) continue;
            int e = rint_(NE), f = rint_(NE);
            if (e == f) continue;
            int t = eb[e]; eb[e] = eb[f]; eb[f] = t;
            if (rnd() & 1) es[e] = rint_(M);
        } else { /* star <-> ff exchange on a random side */
            if (rnd() & 1) {
                if (fA == 0 || NE == 0) continue;
                int x = rint_(fA), e = rint_(NE);
                int t = starA[x]; starA[x] = eb[e]; eb[e] = t;
            } else {
                if (fB == 0 || NE == 0) continue;
                int y = rint_(fB), e = rint_(NE);
                int t = starB[y]; starB[y] = ea[e]; ea[e] = t;
            }
        }
        long nc = cost();
        long d = nc - cur;
        if (d <= 0 || rnd01() < exp(-(double)d / T)) {
            cur = nc;
            if (cur < best) {
                best = cur; save_state(&bestS);
                printf("  t=%.1f it=%ld best %ld\n", el, it, best); fflush(stdout);
                if (best == 0) break;
            }
        } else {
            load_state(&curS);
        }
    }
    load_state(&bestS);
    long fin = cost();
    write_state(out, fin);
    char fn[1024]; snprintf(fn, sizeof fn, "%s.edges", out);
    write_edges(fn);
    printf("RESULT best %ld iters %ld vertices %d%s\n", fin, it, NV, fin == 0 ? " [DIAMETER_OK]" : "");
    return 0;
}
