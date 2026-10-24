/* tabu_k.c (card c2, squad d14D7-r3): fixed-size tabu search for k pairwise non-orthogonal points of E (E11 graph).
   Usage: tabu_k GRAPH MAP SECONDS SEED K0 OUTPREFIX [SEEDFLAGS|-]
     GRAPH = E11.graph ("n m", then m edges "i j"), MAP = E11.map (line i: point id, spread line id, 7 coords).
     SEEDFLAGS (optional): a flags file "p l"; its points (all in E) form the initial independent set, padded with
     min-inside-degree vertices to K0. Without it the start is a uniformly random K0-subset.
   State: S = k vertices, cost = number of edges inside S. tau[x] = number of neighbours of x inside S (incremental).
   Move: u in S (largest tau, non-tabu) out, v outside in (min tau[v] - A(u,v), non-tabu or aspiration: new cost
   below the best cost seen at this k). Swap delta = tau[v] - A(u,v) - tau[u].
   Tabu: u may not re-enter and v may not leave for tt = 0.6 * (#conflicting S vertices) + rand(10) + 1 iterations.
   Cost 0: recount edges from scratch, write OUTPREFIX_k<k>.flags (flags "point spread_line"), then k++ (add the
   min-tau vertex). Kick: after PERT iterations without a new best cost at this k, KICK random swaps.
   Stall fallback (only while no valid set has been found): if no success for STALL seconds, k-- (remove max-tau vertex).
   Env: STALL (default 200), PERT (default 200000), KICK (default 5).
   Build: gcc -O3 -march=native -o tabu_k tabu_k.c */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline int rndi(int n) { return (int)(rnd64() % (uint64_t)n); }
static double now(void) { struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts); return ts.tv_sec + ts.tv_nsec * 1e-9; }

static char *buf; static size_t blen, bpos;
static long nextint(void) {
    while (bpos < blen && (buf[bpos] < '0' || buf[bpos] > '9')) bpos++;
    long x = 0;
    while (bpos < blen && buf[bpos] >= '0' && buf[bpos] <= '9') x = x * 10 + (buf[bpos++] - '0');
    return x;
}

static int n; static long m;
static int *off, *adj;
static int *inS, *tau, *tabu, *Sl, *spos, *mark, *flagP, *flagL;
static int ns = 0;
static long cost = 0;
static const char *outp;

static void addv(int x) {
    inS[x] = 1; spos[x] = ns; Sl[ns++] = x;
    cost += tau[x];
    for (int e = off[x]; e < off[x + 1]; e++) tau[adj[e]]++;
}
static void remv(int x) {
    inS[x] = 0; int p = spos[x]; int last = Sl[--ns]; Sl[p] = last; spos[last] = p; spos[x] = -1;
    for (int e = off[x]; e < off[x + 1]; e++) tau[adj[e]]--;
    cost -= tau[x];   /* tau[x] counts S-neighbours of x; x is not its own neighbour, so this is unchanged by its removal */
}
static int add_min_tau(void) {
    int best = -1, bt = 1 << 30, cnt = 0;
    for (int x = 0; x < n; x++) {
        if (inS[x]) continue;
        int t = tau[x];
        if (t < bt) { bt = t; best = x; cnt = 1; }
        else if (t == bt && rndi(++cnt) == 0) best = x;
    }
    addv(best); return best;
}
static void remove_max_tau(void) {
    int best = -1, bt = -1, cnt = 0;
    for (int i = 0; i < ns; i++) {
        int x = Sl[i], t = tau[x];
        if (t > bt) { bt = t; best = x; cnt = 1; }
        else if (t == bt && rndi(++cnt) == 0) best = x;
    }
    remv(best);
}
static long edges_inside(void) {   /* recount from scratch: each inside edge is seen from both ends */
    long c = 0;
    for (int i = 0; i < ns; i++) { int x = Sl[i]; for (int e = off[x]; e < off[x + 1]; e++) if (inS[adj[e]]) c++; }
    return c / 2;
}
static void save(void) {
    char fn[700]; snprintf(fn, sizeof fn, "%s_k%d.flags", outp, ns);
    FILE *g = fopen(fn, "w"); if (!g) return;
    for (int i = 0; i < ns; i++) fprintf(g, "%d %d\n", flagP[Sl[i]], flagL[Sl[i]]);
    fclose(g);
}

int main(int argc, char **argv) {
    if (argc < 7) { fprintf(stderr, "usage: tabu_k GRAPH MAP SECONDS SEED K0 OUTPREFIX [SEEDFLAGS|-]\n"); return 2; }
    FILE *f = fopen(argv[1], "rb"); if (!f) { perror(argv[1]); return 2; }
    fseek(f, 0, SEEK_END); blen = (size_t)ftell(f); fseek(f, 0, SEEK_SET);
    buf = malloc(blen + 1); if (!buf || fread(buf, 1, blen, f) != blen) { fprintf(stderr, "read fail\n"); return 2; }
    fclose(f);
    bpos = 0; n = (int)nextint(); m = nextint(); size_t hdr = bpos;
    int *deg = calloc(n, sizeof(int));
    for (long e = 0; e < m; e++) { long a = nextint(), b = nextint(); deg[a]++; deg[b]++; }
    off = malloc(sizeof(int) * (n + 1)); off[0] = 0;
    for (int i = 0; i < n; i++) off[i + 1] = off[i] + deg[i];
    adj = malloc(sizeof(int) * (size_t)off[n]);
    int *fp = calloc(n, sizeof(int));
    bpos = hdr;
    for (long e = 0; e < m; e++) { long a = nextint(), b = nextint(); adj[off[a] + fp[a]++] = (int)b; adj[off[b] + fp[b]++] = (int)a; }
    free(fp); free(deg); free(buf); buf = NULL;
    fprintf(stderr, "graph: n=%d m=%ld\n", n, m);

    flagP = malloc(sizeof(int) * n); flagL = malloc(sizeof(int) * n);
    f = fopen(argv[2], "r"); if (!f) { perror(argv[2]); return 2; }
    int maxp = 0;
    for (int i = 0; i < n; i++) {
        int a, b; if (fscanf(f, "%d %d", &a, &b) != 2) { fprintf(stderr, "map read fail\n"); return 2; }
        flagP[i] = a; flagL[i] = b; if (a > maxp) maxp = a;
        for (int k = 0; k < 7; k++) { int c; if (fscanf(f, "%d", &c) != 1) { fprintf(stderr, "map read fail\n"); return 2; } }
    }
    fclose(f);
    int *pv = malloc(sizeof(int) * (maxp + 1)); for (int p = 0; p <= maxp; p++) pv[p] = -1;
    for (int i = 0; i < n; i++) pv[flagP[i]] = i;

    inS = calloc(n, sizeof(int)); tau = calloc(n, sizeof(int)); tabu = calloc(n, sizeof(int));
    Sl = malloc(sizeof(int) * n); spos = malloc(sizeof(int) * n); mark = calloc(n, sizeof(int));
    for (int i = 0; i < n; i++) spos[i] = -1;

    rs ^= (uint64_t)strtoull(argv[4], 0, 10) * 0x9E3779B97F4A7C15ULL; if (!rs) rs = 1;
    double secs = atof(argv[3]); int K0 = atoi(argv[5]); outp = argv[6];
    const char *seedf = argc > 7 ? argv[7] : "-";
    double STALL = getenv("STALL") ? atof(getenv("STALL")) : 200.0;
    long PERT = getenv("PERT") ? atol(getenv("PERT")) : 200000;
    int KICK = getenv("KICK") ? atoi(getenv("KICK")) : 5;

    int nseed = 0;
    if (strcmp(seedf, "-") != 0) {
        FILE *g = fopen(seedf, "r"); if (!g) { perror(seedf); return 2; }
        int p, l;
        while (fscanf(g, "%d %d", &p, &l) == 2) {
            int v = (p >= 0 && p <= maxp) ? pv[p] : -1;
            if (v < 0) { fprintf(stderr, "seed point %d not in E, skipped\n", p); continue; }
            if (inS[v] || ns >= K0) continue;
            addv(v); nseed++;
        }
        fclose(g);
        fprintf(stderr, "seed: %d vertices from %s, cost %ld\n", nseed, seedf, cost);
    }
    long kbest = 0;
    if (cost == 0 && ns > 0) { save(); kbest = ns; fprintf(stderr, "seed is valid: k=%d saved\n", ns); }
    while (ns < K0) {
        if (nseed > 0) add_min_tau();
        else { int x; do x = rndi(n); while (inS[x]); addv(x); }
    }
    double t0 = now(), lastSucc = t0;
    if (cost == 0) { save(); kbest = ns; }
    long bestCostK = cost, lastImpIt = 0, it = 0;
    fprintf(stderr, "start k=%d cost=%ld\n", ns, cost);

    while (now() - t0 < secs) {
        it++;
        /* u: most conflicting non-tabu vertex of S (random tie-break) */
        int u = -1, ut = -1, cnt = 0, nconf = 0;
        for (int i = 0; i < ns; i++) {
            int x = Sl[i], t = tau[x];
            if (t > 0) nconf++;
            if (tabu[x] > it) continue;
            if (t > ut) { ut = t; u = x; cnt = 1; }
            else if (t == ut && rndi(++cnt) == 0) u = x;
        }
        if (u < 0) { u = Sl[rndi(ns)]; ut = tau[u]; }
        /* v: outside vertex minimising tau[v] - A(u,v); tabu only if aspiration (new cost < best at this k) */
        for (int e = off[u]; e < off[u + 1]; e++) mark[adj[e]] = 1;
        int v = -1, vb = 1 << 30; cnt = 0;
        for (int x = 0; x < n; x++) {
            if (inS[x]) continue;
            int val = tau[x] - mark[x];
            if (val > vb) continue;
            if (tabu[x] > it && cost - ut + val >= bestCostK) continue;
            if (val < vb) { vb = val; v = x; cnt = 1; }
            else if (rndi(++cnt) == 0) v = x;
        }
        for (int e = off[u]; e < off[u + 1]; e++) mark[adj[e]] = 0;
        if (v < 0) { do v = rndi(n); while (inS[v]); }
        remv(u); addv(v);
        int tt = (int)(0.6 * nconf) + rndi(10) + 1;
        tabu[u] = (int)(it + tt); tabu[v] = (int)(it + tt);

        if (cost < bestCostK) { bestCostK = cost; lastImpIt = it; }
        if (cost == 0) {
            long chk = edges_inside();
            if (chk != 0) { fprintf(stderr, "BUG: recount %ld\n", chk); return 1; }
            save(); kbest = ns; lastSucc = now();
            fprintf(stderr, "%.1fs it %ld: VALID k=%d (saved)\n", now() - t0, it, ns);
            add_min_tau();
            bestCostK = cost; lastImpIt = it;
        }
        if (it - lastImpIt > PERT) {
            for (int r = 0; r < KICK; r++) { int a = Sl[rndi(ns)], b; do b = rndi(n); while (inS[b]); remv(a); addv(b); }
            bestCostK = cost; lastImpIt = it;
        }
        if (kbest == 0 && now() - lastSucc > STALL && ns > 1) {
            remove_max_tau(); lastSucc = now(); bestCostK = cost; lastImpIt = it;
            fprintf(stderr, "%.1fs: no valid set yet, stepping down to k=%d\n", now() - t0, ns);
        }
        if (it % 1000000 == 0) fprintf(stderr, "%.1fs it %ld k=%d cost=%ld best=%ld\n", now() - t0, it, ns, cost, bestCostK);
    }
    fprintf(stderr, "done: %ld iterations, largest valid k=%ld (file %s_k%ld.flags), final k=%d cost=%ld\n",
            it, kbest, outp, kbest, ns, cost);
    return 0;
}
