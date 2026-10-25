/* qtabu.c: maximum-weight independent set on a quotient graph by feasible-space tabu search (card c3, round 3).
 *
 * usage: qtabu GRAPH SEED OUT CPU_SECONDS RNG_SEED [STALL_ITERS]
 *   GRAPH: "n" then per vertex "w deg nbr1 ... nbr_deg" (w = number of orbit-graph vertices it stands for).
 *   SEED:  quotient vertex ids, one per line ("-" for none). Ids that conflict with earlier ones are skipped.
 *   OUT:   quotient vertex ids of the best set; rewritten (atomic rename) whenever its weight improves.
 *
 * S is always independent. A move inserts a vertex v outside S and removes its S-neighbours; its gain is
 * w(v) - w(S cap N(v)) (ADD when there are none, 1-1 swap, or general (omega,1) insertion). Each iteration takes the
 * non-tabu move of largest gain (ties random); a tabu move is allowed when it gives a new best weight (aspiration).
 * A removed vertex may not re-enter for TT0 + rand(TT1) iterations. wS[v] and cS[v] (weight and number of S-neighbours
 * of v) are maintained incrementally.
 * Stall: after STALL_ITERS iterations without a new best, S is restored to the best set and 3..10 gentle
 * insertions are made (each: the least-conflicting of 30 random outside vertices).
 * CPU time is measured with CLOCK_PROCESS_CPUTIME_ID.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define TT0 7
#define TT1 10

static int n;
static int *w, *deg, **nb;
static char *inS, *bestS;
static long long *wS;          /* total weight of S-neighbours of v */
static int *cS;                /* number of S-neighbours of v */
static long long cur, best;    /* weight of S, best weight so far */
static long long *tabuUntil;   /* v may not re-enter S before this iteration */
static long long it;
static int *remb;              /* scratch: S-neighbours of the inserted vertex */
static const char *outf;
static uint64_t rs = 88172645463325252ULL;

static inline uint64_t rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline int rndint(int m) { return (int)(rnd64() % (uint64_t)m); }

static double cpu_now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &ts);
    return ts.tv_sec + 1e-9 * ts.tv_nsec;
}

static void add_v(int v) {
    inS[v] = 1; cur += w[v];
    for (int j = 0; j < deg[v]; j++) { int x = nb[v][j]; wS[x] += w[v]; cS[x]++; }
}

static void rem_v(int u) {
    inS[u] = 0; cur -= w[u];
    for (int j = 0; j < deg[u]; j++) { int x = nb[u][j]; wS[x] -= w[u]; cS[x]--; }
}

/* insert v, removing its S-neighbours; each removed vertex becomes tabu for tt iterations */
static void insert_move(int v, long long tt) {
    int nr = 0;
    for (int j = 0; j < deg[v]; j++) { int x = nb[v][j]; if (inS[x]) remb[nr++] = x; }
    for (int k = 0; k < nr; k++) { rem_v(remb[k]); tabuUntil[remb[k]] = it + tt; }
    add_v(v);
}

/* best insertion: largest gain w(v) - wS[v] over v outside S; tabu vertices only by aspiration unless allow_tabu */
static int best_move(int allow_tabu, int *pv, long long *pg) {
    long long bg = -(1LL << 60);
    int bv = -1, cnt = 0;
    for (int v = 0; v < n; v++) {
        if (inS[v]) continue;
        long long g = (long long)w[v] - wS[v];
        if (g < bg) continue;
        if (!allow_tabu && tabuUntil[v] > it && cur + g <= best) continue;
        if (g > bg) { bg = g; bv = v; cnt = 1; }
        else { cnt++; if (rndint(cnt) == 0) bv = v; }
    }
    if (bv < 0) return 0;
    *pv = bv; *pg = bg;
    return 1;
}

static void save_sol(void) {
    char tmp[1024];
    snprintf(tmp, sizeof tmp, "%s.tmp", outf);
    FILE *o = fopen(tmp, "w");
    if (!o) { perror(tmp); exit(4); }
    for (int v = 0; v < n; v++) if (bestS[v]) fprintf(o, "%d\n", v);
    fclose(o);
    rename(tmp, outf);
}

/* full recomputation: independence, weight, wS and cS */
static int check_state(void) {
    long long tot = 0;
    for (int v = 0; v < n; v++) {
        long long ws = 0; int cs = 0;
        for (int j = 0; j < deg[v]; j++) { int x = nb[v][j]; if (inS[x]) { ws += w[x]; cs++; } }
        if (ws != wS[v] || cs != cS[v]) return 0;
        if (inS[v]) { if (cs) return 0; tot += w[v]; }
    }
    return tot == cur;
}

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: qtabu GRAPH SEED OUT CPU_SECONDS RNG_SEED [STALL_ITERS]\n");
        return 1;
    }
    const char *gf = argv[1], *sf = argv[2];
    outf = argv[3];
    double budget = atof(argv[4]);
    rs ^= (uint64_t)strtoull(argv[5], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 50; i++) rnd64();
    long long STALL = argc > 6 ? atoll(argv[6]) : 1000000LL;

    FILE *fp = fopen(gf, "r");
    if (!fp) { perror(gf); return 1; }
    if (fscanf(fp, "%d", &n) != 1) return 1;
    w = malloc(sizeof(int) * n); deg = malloc(sizeof(int) * n); nb = malloc(sizeof(int *) * n);
    for (int i = 0; i < n; i++) {
        if (fscanf(fp, "%d %d", &w[i], &deg[i]) != 2) { fprintf(stderr, "bad line %d\n", i); return 1; }
        nb[i] = malloc(sizeof(int) * (deg[i] + 1));
        for (int k = 0; k < deg[i]; k++) if (fscanf(fp, "%d", &nb[i][k]) != 1) return 1;
    }
    fclose(fp);

    inS = calloc(n, 1); bestS = calloc(n, 1);
    wS = calloc(n, sizeof(long long)); cS = calloc(n, sizeof(int));
    tabuUntil = calloc(n, sizeof(long long)); remb = malloc(sizeof(int) * n);
    cur = 0; it = 0;

    if (strcmp(sf, "-") != 0) {
        FILE *sp = fopen(sf, "r");
        if (!sp) { perror(sf); return 1; }
        int v;
        while (fscanf(sp, "%d", &v) == 1)
            if (v >= 0 && v < n && !inS[v] && cS[v] == 0) add_v(v);
        fclose(sp);
    }
    fprintf(stderr, "seed weight %lld\n", cur);
    int *perm = malloc(sizeof(int) * n);
    for (int i = 0; i < n; i++) perm[i] = i;
    for (int i = n - 1; i > 0; i--) { int j = rndint(i + 1), t = perm[i]; perm[i] = perm[j]; perm[j] = t; }
    for (int i = 0; i < n; i++) { int v = perm[i]; if (!inS[v] && cS[v] == 0) add_v(v); }
    best = cur;
    memcpy(bestS, inS, n);
    save_sol();
    fprintf(stderr, "start weight %lld\n", cur);

    double t0 = cpu_now(), next_log = 30.0;
    long long lastImp = 0, nrest = 0;
    for (;;) {
        it++;
        if ((it & 1023) == 0) {
            double el = cpu_now() - t0;
            if (el >= budget) break;
            if (el >= next_log) {
                next_log += 30.0;
                if (!check_state()) { fprintf(stderr, "INTERNAL STATE ERROR\n"); return 3; }
                fprintf(stderr, "t=%.0f cur=%lld best=%lld it=%lld restarts=%lld\n", el, cur, best, it, nrest);
            }
        }
        int v = -1; long long g = 0;
        if (!best_move(0, &v, &g) && !best_move(1, &v, &g)) break;
        insert_move(v, TT0 + rndint(TT1));
        if (cur > best) {
            best = cur;
            memcpy(bestS, inS, n);
            save_sol();
            lastImp = it;
            fprintf(stderr, "best %lld at t=%.1f it=%lld\n", best, cpu_now() - t0, it);
        }
        if (it - lastImp > STALL) {
            for (int u = 0; u < n; u++) if (inS[u]) rem_v(u);
            for (int u = 0; u < n; u++) if (bestS[u]) add_v(u);
            int P = 3 + rndint(8);
            for (int p = 0; p < P; p++) {
                int bx = -1; long long bw = 0;
                for (int s = 0; s < 30; s++) {
                    int x = rndint(n);
                    if (inS[x]) continue;
                    if (bx < 0 || wS[x] < bw) { bx = x; bw = wS[x]; }
                }
                if (bx >= 0) insert_move(bx, TT0 + rndint(TT1));
            }
            lastImp = it;
            nrest++;
        }
    }
    double el = cpu_now() - t0;
    int c1 = 0, c3 = 0, cn = 0;
    for (int v = 0; v < n; v++) if (bestS[v]) { cn++; if (w[v] == 1) c1++; else if (w[v] == 3) c3++; }
    fprintf(stderr, "END t=%.1f best=%lld quotient_vertices=%d (w1=%d w3=%d) it=%lld restarts=%lld\n",
            el, best, cn, c1, c3, it, nrest);
    printf("best %lld\n", best);
    return 0;
}
