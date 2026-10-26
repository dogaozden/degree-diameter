/* sym_anneal2.c (lead, from round r1 card c6's sym_anneal.c, plus an exhaustive polish): simulated annealing over cubic bipartite graphs with a free cyclic automorphism.
   n = b*c. Vertex (o,i) has id o*c+i, i in Z_c, o in 0..b-1. Orbits 0..h-1 form side A, h..b-1 side B, h=b/2.
   State: 3-regular bipartite multigraph H on the b orbits, given as E=3h edge orbits (ea[e], eb[e], et[e]) meaning
   (ea,i) ~ (eb,i+et) for all i.  Simple graph iff no two edge orbits share (a,b,t).
   Moves: change one shift; swap the B-endpoints of two edge orbits (2-switch, keeps 3-regularity), new shifts random or kept.
   cost = sum over orbit representatives (o,0) of #vertices at distance > D (BFS). cost 0 => diameter <= D.
   Usage: sym_anneal b c D seconds seed OUT [T0 T1 cycle_iters]
   Writes the edge list ("n" then "u v", 0-based) to OUT on the first cost-0 state, then exits with status 0. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXE 512
#ifndef POLISH
#define POLISH 4
#endif
#define MAXN 2048

static int b, c, n, h, E, D;
static int ea[MAXE], eb[MAXE], et[MAXE];
static int adj[MAXN * 3];
static int deg[MAXN];
static int stmp[MAXN];
static int stampv = 0;
static int q[MAXN];

static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline int rndi(int m) { return (int)(rnd() % (uint64_t)m); }
static inline double rndu(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

/* 1 if (a,bb,t) differs from every set edge orbit except skip1, skip2 */
static int ok_edge(int a, int bb, int t, int skip1, int skip2) {
    for (int e = 0; e < E; e++) {
        if (e == skip1 || e == skip2) continue;
        if (ea[e] == a && eb[e] == bb && et[e] == t) return 0;
    }
    return 1;
}

static void build(void) {
    memset(deg, 0, sizeof(int) * n);
    for (int e = 0; e < E; e++)
        for (int i = 0; i < c; i++) {
            int u = ea[e] * c + i;
            int v = eb[e] * c + (i + et[e]) % c;
            adj[u * 3 + deg[u]++] = v;
            adj[v * 3 + deg[v]++] = u;
        }
}

/* number of (source, vertex) pairs with distance > D over sources (o,0), o=0..b-1 */
static int cost(void) {
    build();
    int bad = 0;
    for (int o = 0; o < b; o++) {
        int s = o * c;
        stampv++;
        q[0] = s; stmp[s] = stampv;
        int qh = 0, qt = 1;
        for (int lev = 0; lev < D; lev++) {
            int qe = qt;
            for (; qh < qe; qh++) {
                int u = q[qh];
                for (int k = 0; k < 3; k++) {
                    int v = adj[u * 3 + k];
                    if (stmp[v] != stampv) { stmp[v] = stampv; q[qt++] = v; }
                }
            }
            if (qh == qt) break;
        }
        bad += n - qt;
    }
    return bad;
}

static void init_state(void) {
    static int sa[MAXE], sb[MAXE];
    int k = 0;
    for (int a = 0; a < h; a++) for (int r = 0; r < 3; r++) sa[k++] = a;
    k = 0;
    for (int bb = h; bb < b; bb++) for (int r = 0; r < 3; r++) sb[k++] = bb;
    for (int i = E - 1; i > 0; i--) { int j = rndi(i + 1); int t = sb[i]; sb[i] = sb[j]; sb[j] = t; }
    for (int e = 0; e < E; e++) { ea[e] = sa[e]; eb[e] = sb[e]; et[e] = -1; }
    for (int e = 0; e < E; e++) {
        int tries = 0;
        do { et[e] = rndi(c); tries++; } while (!ok_edge(ea[e], eb[e], et[e], e, -1) && tries < 100000);
        if (tries >= 100000) { fprintf(stderr, "init failed\n"); exit(2); }
    }
}

static void write_graph(const char *out) {
    FILE *f = fopen(out, "w");
    if (!f) { perror("fopen"); exit(3); }
    fprintf(f, "%d\n", n);
    for (int e = 0; e < E; e++)
        for (int i = 0; i < c; i++) {
            int u = ea[e] * c + i;
            int v = eb[e] * c + (i + et[e]) % c;
            fprintf(f, "%d %d\n", u, v);
        }
    fclose(f);
}


/* polish (lead's addition): exhaustive search over one and two shift changes from the current state */
static int polish(void) {
    int cur = cost();
    for (int e = 0; e < E; e++) {
        int old = et[e];
        for (int t = 0; t < c; t++) {
            if (t == old || !ok_edge(ea[e], eb[e], t, e, -1)) continue;
            et[e] = t; if (cost() == 0) return 0;
        }
        et[e] = old;
    }
    for (int e1 = 0; e1 < E; e1++) for (int e2 = e1 + 1; e2 < E; e2++) {
        int o1 = et[e1], o2 = et[e2];
        for (int t1 = 0; t1 < c; t1++) {
            if (t1 == o1) continue;
            et[e1] = t1; if (!ok_edge(ea[e1], eb[e1], t1, e1, -1)) continue;
            for (int t2 = 0; t2 < c; t2++) {
                if (t2 == o2) continue;
                et[e2] = t2; if (!ok_edge(ea[e2], eb[e2], t2, e2, -1)) continue;
                if (cost() == 0) return 0;
            }
            et[e2] = o2;
        }
        et[e1] = o1; et[e2] = o2;
    }
    cost();
    return cur;
}

int main(int argc, char **argv) {
    if (argc < 7) { fprintf(stderr, "usage: sym_anneal b c D seconds seed OUT [T0 T1 cycle_iters]\n"); return 1; }
    b = atoi(argv[1]); c = atoi(argv[2]); D = atoi(argv[3]);
    double secs = atof(argv[4]);
    rs ^= (uint64_t)atoll(argv[5]) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 10; i++) rnd();
    const char *out = argv[6];
    double T0 = argc > 7 ? atof(argv[7]) : 3.0;
    double T1 = argc > 8 ? atof(argv[8]) : 0.1;
    long cyc = argc > 9 ? atol(argv[9]) : 2000000L;
    if (b % 2 || b < 4 || b > 64) { fprintf(stderr, "b must be even, 4..64\n"); return 1; }
    h = b / 2; E = 3 * h; n = b * c;
    if (n > MAXN) { fprintf(stderr, "n too big\n"); return 1; }

    init_state();
    int cur = cost(), best = cur;
    fprintf(stderr, "start n=%d b=%d c=%d D=%d cost=%d\n", n, b, c, D, cur);
    clock_t t0 = clock();
    long it = 0, cycles = 0;
    int sea[MAXE], seb[MAXE], set_[MAXE];
    while (cur > 0) {
        if ((it & 4095) == 0 && (double)(clock() - t0) / CLOCKS_PER_SEC > secs) break;
        double frac = (double)(it % cyc) / cyc;
        double T = T0 * pow(T1 / T0, frac);
        if (it > 0 && it % cyc == 0) { cycles++; }
        it++;
        int mv = rndi(10) < 4 ? 0 : 1;  /* 0: shift change, 1: 2-switch */
        if (mv == 0) {
            int e = rndi(E);
            int tn = rndi(c);
            if (tn == et[e] || !ok_edge(ea[e], eb[e], tn, e, -1)) continue;
            int old = et[e];
            et[e] = tn;
            int nc = cost();
            int dl = nc - cur;
            if (dl <= 0 || rndu() < exp(-dl / T)) { cur = nc; }
            else et[e] = old;
        } else {
            int e1 = rndi(E), e2 = rndi(E);
            if (e1 == e2 || eb[e1] == eb[e2]) continue;
            int t1 = rndu() < 0.5 ? rndi(c) : et[e1];
            int t2 = rndu() < 0.5 ? rndi(c) : et[e2];
            /* new edges: (ea[e1], eb[e2], t1) and (ea[e2], eb[e1], t2) */
            if (!ok_edge(ea[e1], eb[e2], t1, e1, e2)) continue;
            if (!ok_edge(ea[e2], eb[e1], t2, e1, e2)) continue;
            /* ensure the two new edges are not identical to each other (cannot happen as eb differ) */
            sea[0] = ea[e1]; seb[0] = eb[e1]; set_[0] = et[e1];
            sea[1] = ea[e2]; seb[1] = eb[e2]; set_[1] = et[e2];
            eb[e1] = seb[1]; et[e1] = t1;
            eb[e2] = seb[0]; et[e2] = t2;
            int nc = cost();
            int dl = nc - cur;
            if (dl <= 0 || rndu() < exp(-dl / T)) { cur = nc; }
            else {
                eb[e1] = seb[0]; et[e1] = set_[0];
                eb[e2] = seb[1]; et[e2] = set_[1];
            }
        }
        if (cur < best) {
            best = cur;
            if (best <= POLISH) {
                fprintf(stderr, "polish at cost %d, it=%ld\n", best, it);
                if (polish() == 0) { cur = 0; break; }
                cur = cost();
                fprintf(stderr, "polish done, no cost-0 neighbour\n");
            }
        }
        if (cur == 0) break;
        if (it % 2000000 == 0) {
            fprintf(stderr, "it=%ld T=%.3f cur=%d best=%d t=%.1fs\n", it, T, cur, best,
                    (double)(clock() - t0) / CLOCKS_PER_SEC);
        }
    }
    double el = (double)(clock() - t0) / CLOCKS_PER_SEC;
    if (cur == 0) {
        write_graph(out);
        printf("FOUND n=%d b=%d c=%d D=%d iters=%ld time=%.1fs out=%s\n", n, b, c, D, it, el, out);
        printf("shifts:");
        for (int e = 0; e < E; e++) printf(" (%d,%d,%d)", ea[e], eb[e], et[e]);
        printf("\n");
        return 0;
    }
    printf("NOTFOUND n=%d b=%d c=%d D=%d best=%d iters=%ld time=%.1fs\n", n, b, c, D, best, it, el);
    return 0;
}
