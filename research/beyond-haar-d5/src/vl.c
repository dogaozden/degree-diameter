/* vl.c: simulated annealing over voltage lifts of a small bipartite base multigraph by a finite group.
 *
 * Lift of base B by G (voltages alpha on edges, oriented side 0 -> side 1): vertices (v, h), h in G, and for each
 * base edge e = (a, b) the lift edges (a, h) ~ (b, h * alpha(e)). Left multiplication by G is an automorphism, so the
 * lift has diameter <= D iff, for every base vertex s, every (v, h) is within distance D of (s, 1).
 * Within distance D (bipartite): same side by a walk of even length <= D-1, other side by odd length <= D.
 * Every walk reduces to a non-backtracking one (same end, same product, length lower by an even number), so it is
 * enough to enumerate non-backtracking walks (a parallel edge is a different edge, so a->b->a along two parallel
 * edges is allowed).
 * Pairs are symmetric (W(u->s) = W(s->u)^-1), so side-1 sources only need their same-side targets.
 * Cost = sum over sources of the number of uncovered (v, h). Cost 0 <=> diameter <= D (lift connected).
 *
 * usage: vl BASE GROUP
 *   BASE:  "b E" / b side bits / E lines "u w [volt]" (u on side 0, w on side 1). Voltages default to 0 (identity).
 *   GROUP: m, then the m x m multiplication table (element 0 = identity).
 * env: D (5), ITERS (annealing steps per run, 200000), SECS (60), SEED (1), T0 (3), T1 (0.2),
 *      SWAP (probability of a base 2-switch move, 0), FIXTREE (1 if SWAP=0: spanning-tree voltages stay 1),
 *      OUT (solution file, written whenever a new best is found), EVAL=1 (just print the cost of the input),
 *      MAXDEG (refuse inputs with a larger base degree, default 64)
 * Output: "RESULT best <cost> ..." on stdout; OUT gets the base with voltages.
 */
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXB 512
#define MAXE 4096
#define MAXDEG 64

static int b, E, m, D = 5, W;
static int side[MAXB];
static int eu[MAXE], ew[MAXE], volt[MAXE], fixed_[MAXE];
static int deg[MAXB], dn[MAXB][MAXDEG], de[MAXB][MAXDEG], dd[MAXB][MAXDEG]; /* neighbour, edge, dir (0: u->w) */
static uint16_t *mul;
static int *inv_;
static uint64_t *cov;     /* b x W words */

static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }

static void build_adj(void) {
    memset(deg, 0, sizeof(deg));
    for (int e = 0; e < E; e++) {
        int u = eu[e], w = ew[e];
        dn[u][deg[u]] = w; de[u][deg[u]] = e; dd[u][deg[u]] = 0; deg[u]++;
        dn[w][deg[w]] = u; de[w][deg[w]] = e; dd[w][deg[w]] = 1; deg[w]++;
    }
}

static inline int dvolt(int v, int i) { int g = volt[de[v][i]]; return dd[v][i] ? inv_[g] : g; }

static int maxlen;
static void dfs(int v, int laste, int h, int len) {
    cov[(size_t)v * W + (h >> 6)] |= 1ULL << (h & 63);
    if (len == maxlen) return;
    for (int i = 0; i < deg[v]; i++) {
        int e = de[v][i];
        if (e == laste) continue;
        dfs(dn[v][i], e, mul[(size_t)h * m + dvolt(v, i)], len + 1);
    }
}

/* uncovered count for source s */
static long src_cost(int s) {
    memset(cov, 0, sizeof(uint64_t) * b * W);
    maxlen = side[s] == 0 ? D : D - 1;
    dfs(s, -1, 0, 0);
    long c = 0;
    for (int v = 0; v < b; v++) {
        if (side[s] == 1 && side[v] == 0) continue;
        int par = (side[v] != side[s]);           /* needed parity of the walk */
        if (!par && D % 2 == 0 && 0) continue;
        long k = 0;
        for (int w = 0; w < W; w++) k += __builtin_popcountll(cov[(size_t)v * W + w]);
        c += m - k;
    }
    return c;
}

/* total cost; abort (return > limit) once the partial sum exceeds limit */
static int order[MAXB];
static long total_cost(long limit) {
    long c = 0;
    for (int i = 0; i < b; i++) {
        c += src_cost(order[i]);
        if (c > limit) return c;
    }
    return c;
}


/* ---------- incremental mode: cnt[s][v][h] = number of counted walks from (s,1) to (v,h) ---------- */
static uint16_t *cnt; static signed char *bdist; static long inc_delta;
static int ie_a, ie_c, ie_e, ie_old, ie_new, ie_s, ie_L;
static inline int relevant(int s, int v) { return side[s] == 0 || side[v] == 1; }
static void base_dist(void) {
    bdist = malloc((size_t)b * b);
    for (int s = 0; s < b; s++) {
        signed char *d = bdist + (size_t)s * b; for (int v = 0; v < b; v++) d[v] = 100;
        int q[MAXB], h = 0, t = 0; d[s] = 0; q[t++] = s;
        while (h < t) { int x = q[h++]; for (int i = 0; i < deg[x]; i++) { int y = dn[x][i]; if (d[y] == 100) { d[y] = d[x] + 1; q[t++] = y; } } }
    }
}
static void fill_dfs(int s, int v, int laste, int h, int len, int L) {
    if (relevant(s, v)) cnt[((size_t)s * b + v) * m + h]++;
    if (len == L) return;
    for (int i = 0; i < deg[v]; i++) { int e = de[v][i]; if (e == laste) continue;
        fill_dfs(s, dn[v][i], e, mul[(size_t)h * m + dvolt(v, i)], len + 1, L); }
}
static long inc_init(void) {
    size_t sz = (size_t)b * b * m; if (!cnt) cnt = malloc(sizeof(uint16_t) * sz);
    memset(cnt, 0, sizeof(uint16_t) * sz);
    for (int s = 0; s < b; s++) fill_dfs(s, s, -1, 0, 0, side[s] == 0 ? D : D - 1);
    long c = 0;
    for (int s = 0; s < b; s++) for (int v = 0; v < b; v++) if (relevant(s, v))
        for (int h = 0; h < m; h++) if (!cnt[((size_t)s * b + v) * m + h]) c++;
    return c;
}
static void inc_dfs(int v, int laste, int ho, int hn, int len, int used) {
    if (used && ho != hn && relevant(ie_s, v)) {
        uint16_t *p = cnt + ((size_t)ie_s * b + v) * m;
        if (--p[ho] == 0) inc_delta++;
        if (p[hn]++ == 0) inc_delta--;
    }
    if (len == ie_L) return;
    for (int i = 0; i < deg[v]; i++) {
        int e = de[v][i]; if (e == laste) continue;
        int y = dn[v][i], go, gn, u2 = used;
        if (e == ie_e) { go = dd[v][i] ? inv_[ie_old] : ie_old; gn = dd[v][i] ? inv_[ie_new] : ie_new; u2 = 1; }
        else { go = gn = dvolt(v, i);
            if (!used) { int dmin = bdist[(size_t)y * b + ie_a] < bdist[(size_t)y * b + ie_c] ? bdist[(size_t)y * b + ie_a] : bdist[(size_t)y * b + ie_c];
                if (dmin + 1 > ie_L - (len + 1)) continue; } }
        inc_dfs(y, e, mul[(size_t)ho * m + go], mul[(size_t)hn * m + gn], len + 1, u2);
    }
}
/* change volt[e] to g, return the cost change */
static long inc_move(int e, int g) {
    ie_e = e; ie_a = eu[e]; ie_c = ew[e]; ie_old = volt[e]; ie_new = g; inc_delta = 0;
    for (int s = 0; s < b; s++) {
        ie_s = s; ie_L = side[s] == 0 ? D : D - 1;
        int dmin = bdist[(size_t)s * b + ie_a] < bdist[(size_t)s * b + ie_c] ? bdist[(size_t)s * b + ie_a] : bdist[(size_t)s * b + ie_c];
        if (dmin + 1 > ie_L) continue;
        inc_dfs(s, -1, 0, 0, 0, 0);
    }
    volt[e] = g;
    return inc_delta;
}

static void write_sol(const char *path, long cost, const char *gname) {
    if (!path) return;
    char tmp[1024]; snprintf(tmp, sizeof tmp, "%s.tmp", path);
    FILE *f = fopen(tmp, "w"); if (!f) return;
    fprintf(f, "%d %d\n", b, E);
    for (int v = 0; v < b; v++) fprintf(f, "%d%c", side[v], v == b - 1 ? '\n' : ' ');
    for (int e = 0; e < E; e++) fprintf(f, "%d %d %d\n", eu[e], ew[e], volt[e]);
    fprintf(f, "# group %s m %d D %d cost %ld\n", gname, m, D, cost);
    fclose(f); rename(tmp, path);
}

static int connected(void) {
    int seen[MAXB] = {0}, q[MAXB], h = 0, t = 0; seen[0] = 1; q[t++] = 0;
    while (h < t) { int v = q[h++]; for (int i = 0; i < deg[v]; i++) if (!seen[dn[v][i]]) { seen[dn[v][i]] = 1; q[t++] = dn[v][i]; } }
    return t == b;
}

static void mark_tree(void) {
    int seen[MAXB] = {0}, q[MAXB], h = 0, t = 0; seen[0] = 1; q[t++] = 0;
    for (int e = 0; e < E; e++) fixed_[e] = 0;
    while (h < t) { int v = q[h++]; for (int i = 0; i < deg[v]; i++) if (!seen[dn[v][i]]) {
        seen[dn[v][i]] = 1; q[t++] = dn[v][i]; fixed_[de[v][i]] = 1; volt[de[v][i]] = 0; } }
}

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: vl BASE GROUP\n"); return 2; }
    const char *gs;
    if ((gs = getenv("D"))) D = atoi(gs);
    long ITERS = getenv("ITERS") ? atol(getenv("ITERS")) : 200000;
    double SECS = getenv("SECS") ? atof(getenv("SECS")) : 60;
    rs ^= getenv("SEED") ? (uint64_t)atoll(getenv("SEED")) * 0x9E3779B97F4A7C15ULL : 0; for (int i = 0; i < 20; i++) rnd();
    double T0 = getenv("T0") ? atof(getenv("T0")) : 3, T1 = getenv("T1") ? atof(getenv("T1")) : 0.2;
    double SWAP = getenv("SWAP") ? atof(getenv("SWAP")) : 0;
    int FIXTREE = getenv("FIXTREE") ? atoi(getenv("FIXTREE")) : (SWAP == 0);
    int EVAL = getenv("EVAL") ? atoi(getenv("EVAL")) : 0;
    int maxdeg = getenv("MAXDEG") ? atoi(getenv("MAXDEG")) : MAXDEG;
    const char *OUT = getenv("OUT");

    FILE *f = fopen(argv[1], "r"); if (!f) { perror("base"); return 2; }
    if (fscanf(f, "%d %d", &b, &E) != 2 || b > MAXB || E > MAXE) { fprintf(stderr, "bad base\n"); return 2; }
    for (int v = 0; v < b; v++) if (fscanf(f, "%d", &side[v]) != 1) return 2;
    int hasv = 0;
    {   char line[256]; fgets(line, sizeof line, f);
        for (int e = 0; e < E; e++) {
            if (!fgets(line, sizeof line, f)) { fprintf(stderr, "short base\n"); return 2; }
            int a, c, g; int k = sscanf(line, "%d %d %d", &a, &c, &g);
            if (k < 2) { e--; continue; }
            if (side[a] == side[c]) { fprintf(stderr, "edge %d not bipartite\n", e); return 2; }
            if (side[a] == 1) { int t = a; a = c; c = t; }
            eu[e] = a; ew[e] = c; volt[e] = (k == 3) ? g : 0; if (k == 3) hasv = 1;
        }
    }
    fclose(f);
    f = fopen(argv[2], "r"); if (!f || fscanf(f, "%d", &m) != 1) { fprintf(stderr, "bad group\n"); return 2; }
    mul = malloc(sizeof(uint16_t) * m * m); inv_ = malloc(sizeof(int) * m);
    for (long i = 0; i < (long)m * m; i++) { int x; if (fscanf(f, "%d", &x) != 1) return 2; mul[i] = x; }
    fclose(f);
    for (int x = 0; x < m; x++) { inv_[x] = -1; for (int y = 0; y < m; y++) if (mul[(size_t)x * m + y] == 0) inv_[x] = y; }
    W = (m + 63) / 64;
    cov = malloc(sizeof(uint64_t) * b * W);
    build_adj();
    for (int v = 0; v < b; v++) if (deg[v] > maxdeg) { fprintf(stderr, "degree %d > %d\n", deg[v], maxdeg); return 2; }
    if (!connected()) { fprintf(stderr, "base disconnected\n"); }
    for (int i = 0; i < b; i++) order[i] = i;
    const char *gname = argv[2];

    long cur = total_cost(1L << 60);
    if (EVAL) { printf("RESULT cost %ld b %d m %d vertices %ld\n", cur, b, m, (long)b * m); return 0; }
    if (FIXTREE) { mark_tree(); }
    int nfree = 0, freee[MAXE]; for (int e = 0; e < E; e++) if (!fixed_[e]) freee[nfree++] = e;
    if (!hasv) for (int i = 0; i < nfree; i++) volt[freee[i]] = rnd() % m;
    cur = total_cost(1L << 60);
    long best = cur; write_sol(OUT, best, gname);
    double t_start = now(), t_end = t_start + SECS;
    long it_total = 0; int run = 0;
    int bvolt[MAXE], beu[MAXE], bew[MAXE];
    memcpy(bvolt, volt, sizeof(int) * E); memcpy(beu, eu, sizeof(int) * E); memcpy(bew, ew, sizeof(int) * E);
    int INC = getenv("INC") ? atoi(getenv("INC")) : 0;
    if (INC) {
        if (SWAP > 0) { fprintf(stderr, "INC mode has no swap moves\n"); return 2; }
        base_dist();
        cur = inc_init();
        long chk = total_cost(1L << 60);
        if (chk != cur) { fprintf(stderr, "inc init mismatch %ld vs %ld\n", cur, chk); return 3; }
        best = cur;
        for (run = 1; best > 0 && now() < t_end; run++) {
            if (run > 1) { memcpy(volt, bvolt, sizeof(int) * E);
                for (int k = 0; k < 1 + nfree / 20; k++) { int e = freee[rnd() % nfree]; volt[e] = rnd() % m; }
                cur = inc_init(); }
            for (long it = 0; it < ITERS && best > 0; it++) {
                if ((it & 255) == 0 && now() > t_end) break;
                double T = T0 * pow(T1 / T0, (double)it / ITERS);
                int e = freee[rnd() % nfree], old = volt[e], g = rnd() % m; if (g == old) continue;
                long dlt = inc_move(e, g);
                if (dlt <= 0 || rnd01() < exp(-dlt / T)) cur += dlt; else inc_move(e, old);
                it_total++;
                if (cur < best) { best = cur; memcpy(bvolt, volt, sizeof(int) * E); write_sol(OUT, best, gname);
                    if (best < 50 || (it_total % 64) == 0) fprintf(stderr, "  t=%.1fs run %d it %ld best %ld\n", now() - t_start, run, it, best); }
            }
        }
        memcpy(volt, bvolt, sizeof(int) * E);
        long fin = total_cost(1L << 60);
        printf("RESULT best %ld check %ld b %d m %d vertices %ld iters %ld runs %d secs %.1f%s\n", best, fin, b, m,
               (long)b * m, it_total, run - 1, now() - t_start, fin == 0 ? " DIAMETER_OK" : "");
        return 0;
    }
    int TABU = getenv("TABU") ? atoi(getenv("TABU")) : 0;      /* tabu tenure (in steps) on edges; 0 = annealing */
    int SAMPLE = getenv("SAMPLE") ? atoi(getenv("SAMPLE")) : 0; /* moves sampled per tabu step; 0 = all */
    if (TABU > 0) {
        static long tabu_until[MAXE];
        long step = 0, since = 0;
        while (best > 0 && now() < t_end) {
            step++;
            long bc = 1L << 60; int be = -1, bg = -1, nties = 0;
            long nm = SAMPLE > 0 ? SAMPLE : (long)nfree * (m - 1);
            for (long k = 0; k < nm; k++) {
                int e, g;
                if (SAMPLE > 0) { e = freee[rnd() % nfree]; g = rnd() % m; if (g == volt[e]) continue; }
                else { e = freee[k / (m - 1)]; g = (int)(k % (m - 1)); if (g >= volt[e]) g++; }
                int old = volt[e]; volt[e] = g;
                long c = total_cost(bc);
                volt[e] = old;
                int ok = tabu_until[e] < step || c < best;
                if (!ok) continue;
                if (c < bc) { bc = c; be = e; bg = g; nties = 1; }
                else if (c == bc && (rnd() % (++nties)) == 0) { be = e; bg = g; }
            }
            if (be < 0) continue;
            volt[be] = bg; cur = bc; tabu_until[be] = step + TABU + rnd() % (TABU + 1);
            it_total++; since++;
            if (cur < best) { best = cur; since = 0; memcpy(bvolt, volt, sizeof(int) * E); write_sol(OUT, best, gname);
                fprintf(stderr, "  t=%.1fs step %ld best %ld\n", now() - t_start, step, best); }
            if (since > ITERS) {   /* restart from a perturbed best */
                memcpy(volt, bvolt, sizeof(int) * E);
                for (int k = 0; k < 1 + nfree / 5; k++) { int e = freee[rnd() % nfree]; volt[e] = rnd() % m; }
                cur = total_cost(1L << 60); since = 0; run++;
            }
        }
    }
    while (best > 0 && now() < t_end) {
        run++;
        if (run > 1) {   /* restart from best with a kick */
            memcpy(volt, bvolt, sizeof(int) * E); memcpy(eu, beu, sizeof(int) * E); memcpy(ew, bew, sizeof(int) * E);
            build_adj();
            int kick = 1 + nfree / 10;
            for (int k = 0; k < kick; k++) { int e = freee[rnd() % nfree]; volt[e] = rnd() % m; }
            cur = total_cost(1L << 60);
        }
        for (long it = 0; it < ITERS && best > 0; it++) {
            if ((it & 255) == 0 && now() > t_end) break;
            double T = T0 * pow(T1 / T0, (double)it / ITERS);
            double r = rnd01(); if (r < 1e-300) r = 1e-300;
            long limit = cur + (long)floor(-T * log(r));
            if (SWAP > 0 && rnd01() < SWAP) {
                int e1 = rnd() % E, e2 = rnd() % E;
                if (e1 == e2 || eu[e1] == eu[e2] || ew[e1] == ew[e2]) continue;
                int t = ew[e1]; ew[e1] = ew[e2]; ew[e2] = t; build_adj();
                if (!connected()) { t = ew[e1]; ew[e1] = ew[e2]; ew[e2] = t; build_adj(); continue; }
                long c = total_cost(limit);
                if (c <= limit) cur = c; else { t = ew[e1]; ew[e1] = ew[e2]; ew[e2] = t; build_adj(); }
            } else {
                int e = freee[rnd() % nfree], old = volt[e];
                int g = rnd() % m; if (g == old) continue;
                volt[e] = g;
                long c = total_cost(limit);
                if (c <= limit) cur = c; else volt[e] = old;
            }
            it_total++;
            if (cur < best) {
                best = cur;
                memcpy(bvolt, volt, sizeof(int) * E); memcpy(beu, eu, sizeof(int) * E); memcpy(bew, ew, sizeof(int) * E);
                write_sol(OUT, best, gname);
                fprintf(stderr, "  t=%.1fs run %d it %ld best %ld\n", now() - t_start, run, it, best);
            }
        }
    }
    memcpy(volt, bvolt, sizeof(int) * E); memcpy(eu, beu, sizeof(int) * E); memcpy(ew, bew, sizeof(int) * E); build_adj();
    long fin = total_cost(1L << 60);
    printf("RESULT best %ld check %ld b %d m %d vertices %ld iters %ld runs %d secs %.1f%s\n", best, fin, b, m,
           (long)b * m, it_total, run, now() - t_start, fin == 0 ? " DIAMETER_OK" : "");
    return 0;
}
