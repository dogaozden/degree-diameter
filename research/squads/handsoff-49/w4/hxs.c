/* hxs.c (w4, handsoff-49): symmetric version of hx. The base (H(3) incidence graph, 728 vertices) has a
   fixed-point-free automorphism s of prime order m (read from AUTS, line AUTIDX). Voltages are chosen invariant:
   a(s e) = a(e) (edge orbits of <s>). The lift over G then has the automorphism (v,x) -> (s v, x), so only roots
   that are representatives of the vertex orbits are needed; full cost = m * (cost over representatives).
   Gauge: edge orbits of a BFS spanning tree of the quotient graph are fixed to voltage 0 (WLOG).
   Usage: hxs GROUP AUTS AUTIDX seconds seed T0 T1 OUTPREFIX
     GROUP: cyc:k or file.bin (groups.py format, T[x*k+g] = x*g). Cost is the full-lift cost (m * reps cost).
   Writes OUTPREFIX.best ("e g" per base edge) and, if the full cost is 0 or WRITE_EDGES is set, OUTPREFIX.edges. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>

#define NB 728
#define NE 1456
#define MAXK 64
#define D 9

static int k;
static uint16_t *T;
static int inv_[MAXK];
static int ea[NE], eb[NE], ev[NE];
static int perm[NB];
static int vorb[NB], nvorb, reps[NB], nreps; /* vertex orbit id, reps (vertex ids) */
static int eorb[NE], neorb;                  /* edge orbit id per base edge */
static int eo_first[NE];                     /* edge orbit -> representative edge index */
static int eo_size[NE];
static int eo_edges[NE][16];                 /* members (<= m) */
static int tree_o[NE];
static int freeo[NE], nfree;
static int val[NE];
static int m_order;
static int ninc[NB], incw[NB][4], incg[NB][4];
static uint64_t SA_[NB][MAXK], SB_[NB][MAXK];

static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static double urand(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static void load_group(const char *spec) {
    if (strncmp(spec, "cyc:", 4) == 0) {
        k = atoi(spec + 4);
        T = malloc(sizeof(uint16_t) * k * k);
        for (int x = 0; x < k; x++) for (int g = 0; g < k; g++) T[x * k + g] = (uint16_t)((x + g) % k);
    } else {
        FILE *f = fopen(spec, "rb");
        if (!f) { perror("group"); exit(1); }
        int32_t N; if (fread(&N, 4, 1, f) != 1) exit(1);
        k = N; T = malloc(sizeof(uint16_t) * k * k);
        if (fread(T, 2, (size_t)k * k, f) != (size_t)k * k) exit(1);
        fclose(f);
    }
    for (int g = 0; g < k; g++) for (int h = 0; h < k; h++) if (T[g * k + h] == 0) { inv_[g] = h; break; }
}

static void load_base(void) {
    FILE *f = fopen("base.txt", "r");
    int nb, m; if (!f || fscanf(f, "%d %d", &nb, &m) != 2) exit(1);
    for (int e = 0; e < NE; e++) {
        int u, v; if (fscanf(f, "%d %d", &u, &v) != 2) exit(1);
        if (u > v) { int t = u; u = v; v = t; }
        ea[e] = u; eb[e] = v;
    }
    fclose(f);
}

static void load_aut(const char *path, int idx) {
    FILE *f = fopen(path, "r");
    if (!f) { perror("auts"); exit(1); }
    char line[20000];
    for (int i = 0; i <= idx; i++) if (!fgets(line, sizeof line, f)) { fprintf(stderr, "no such aut line\n"); exit(1); }
    fclose(f);
    char *p = line;
    for (int v = 0; v < NB; v++) { perm[v] = (int)strtol(p, &p, 10); }
}

/* build orbits of <perm>, the edge orbits, and the gauge tree */
static void build_orbits(void) {
    /* order of perm */
    int seen[NB]; memset(seen, 0, sizeof seen);
    int o = 1;
    for (int s = 0; s < NB; s++) {
        if (seen[s]) continue;
        int L = 0, x = s;
        while (!seen[x]) { seen[x] = 1; x = perm[x]; L++; }
        int a = o, b = L; while (b) { int t = a % b; a = b; b = t; }
        o = o / a * L;
    }
    m_order = o;
    /* vertex orbits */
    for (int v = 0; v < NB; v++) vorb[v] = -1;
    nvorb = 0; nreps = 0;
    for (int v = 0; v < NB; v++) {
        if (vorb[v] >= 0) continue;
        int x = v;
        for (int i = 0; i < o; i++) { vorb[x] = nvorb; x = perm[x]; }
        reps[nreps++] = v; nvorb++;
    }
    /* edge orbits: key = canonical min over images of the edge */
    int E_ = NE;
    for (int e = 0; e < E_; e++) eorb[e] = -1;
    neorb = 0;
    for (int e = 0; e < E_; e++) {
        if (eorb[e] >= 0) continue;
        int a = ea[e], b = eb[e];
        int cnt = 0;
        for (int i = 0; i < o; i++) {
            /* find edge index equal to {a,b} */
            int f = -1;
            int u = a, v2 = b;
            if (u > v2) { int t = u; u = v2; v2 = t; }
            /* linear search is fine (1456 edges, few orbits) */
            for (int j = 0; j < E_; j++) if (ea[j] == u && eb[j] == v2) { f = j; break; }
            eorb[f] = neorb; if (cnt < 16) eo_edges[neorb][cnt] = f; cnt++;
            a = perm[a]; b = perm[b];
        }
        eo_first[neorb] = e; eo_size[neorb] = cnt; neorb++;
    }
    /* gauge: BFS spanning tree on quotient graph (vertex orbits joined by edge orbits) */
    int qseen[NB]; memset(qseen, 0, sizeof qseen);
    for (int i = 0; i < neorb; i++) tree_o[i] = 0;
    int q[NB], qh = 0, qt = 0; q[qt++] = vorb[0]; qseen[vorb[0]] = 1;
    while (qh < qt) {
        int c = q[qh++];
        for (int eo = 0; eo < neorb; eo++) {
            int e = eo_first[eo];
            int x = vorb[ea[e]], y = vorb[eb[e]];
            int other = -1;
            if (x == c) other = y; else if (y == c) other = x;
            if (other < 0 || qseen[other]) continue;
            qseen[other] = 1; tree_o[eo] = 1; q[qt++] = other;
        }
    }
    nfree = 0;
    for (int eo = 0; eo < neorb; eo++) if (!tree_o[eo]) freeo[nfree++] = eo;
}

static void set_voltages(void) {
    for (int e = 0; e < NE; e++) ev[e] = val[eorb[e]];
}

static void build_inc(void) {
    memset(ninc, 0, sizeof ninc);
    for (int e = 0; e < NE; e++) {
        int a = ea[e], b = eb[e], g = ev[e];
        incw[b][ninc[b]] = a; incg[b][ninc[b]] = g; ninc[b]++;
        incw[a][ninc[a]] = b; incg[a][ninc[a]] = inv_[g]; ninc[a]++;
    }
}

/* cost over the representative roots (uint64 bitsets) */
static int eval_reps(void) {
    build_inc();
    memset(SA_, 0, sizeof SA_);
    for (int i = 0; i < nreps; i++) SA_[reps[i]][0] |= 1ULL << i;
    uint64_t (*cur)[MAXK] = SA_, (*nxt)[MAXK] = SB_;
    for (int step = 1; step <= D; step++) {
        memcpy(nxt, cur, sizeof SA_);
        for (int v = 0; v < NB; v++) {
            for (int i = 0; i < ninc[v]; i++) {
                int w = incw[v][i], g = incg[v][i];
                for (int x = 0; x < k; x++) nxt[v][T[x * k + g]] |= cur[w][x];
            }
        }
        uint64_t (*t)[MAXK] = cur; cur = nxt; nxt = t;
    }
    int cost = 0;
    for (int v = 0; v < NB; v++)
        for (int x = 0; x < k; x++) cost += nreps - __builtin_popcountll(cur[v][x]);
    /* leave final state in SA_ for nothing else */
    return cost;
}

static void write_sol(const char *path) {
    FILE *f = fopen(path, "w");
    for (int e = 0; e < NE; e++) fprintf(f, "%d %d\n", e, ev[e]);
    fclose(f);
}

static void write_edges(const char *path) {
    FILE *f = fopen(path, "w");
    fprintf(f, "%d\n", NB * k);
    for (int e = 0; e < NE; e++)
        for (int x = 0; x < k; x++)
            fprintf(f, "%d %d\n", ea[e] * k + x, eb[e] * k + T[x * k + ev[e]]);
    fclose(f);
}

int main(int argc, char **argv) {
    if (argc < 9) { fprintf(stderr, "usage: hxs GROUP AUTS AUTIDX seconds seed T0 T1 OUTPREFIX\n"); return 1; }
    load_group(argv[1]);
    load_base();
    load_aut(argv[2], atoi(argv[3]));
    build_orbits();
    double secs = atof(argv[4]);
    rs ^= (uint64_t)atoll(argv[5]) * 0x9E3779B97F4A7C15ULL; if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();
    double T0 = atof(argv[6]), T1 = atof(argv[7]);
    const char *outp = argv[8];
    if (nreps > 64) { fprintf(stderr, "too many reps %d\n", nreps); return 1; }
    for (int eo = 0; eo < neorb; eo++) val[eo] = 0;
    for (int i = 0; i < nfree; i++) val[freeo[i]] = (int)(rnd() % k);
    set_voltages();
    int cur = eval_reps(), best = cur;
    int bestval[NE]; memcpy(bestval, val, sizeof val);
    fprintf(stderr, "order m=%d vorbits=%d reps=%d eorbits=%d free=%d start full cost %d\n",
            m_order, nvorb, nreps, neorb, nfree, cur * m_order);
    clock_t t0 = clock();
    double T = T0;
    long it = 0, acc = 0;
    while (1) {
        if ((it & 63) == 0) {
            double el = (double)(clock() - t0) / CLOCKS_PER_SEC;
            if (el >= secs) break;
            T = T0 * pow(T1 / T0, el / secs);
            if ((it & 16383) == 0) fprintf(stderr, "P it=%ld t=%.0f T=%.3f cur=%d best=%d\n", it, el, T, cur * m_order, best * m_order);
        }
        it++;
        int eo = freeo[rnd() % nfree];
        int old = val[eo];
        int ng = (int)(rnd() % (k - 1)); if (ng >= old) ng++;
        val[eo] = ng;
        for (int j = 0; j < eo_size[eo]; j++) ev[eo_edges[eo][j]] = ng;
        int nc = eval_reps();
        int dlt = nc - cur;
        if (dlt <= 0 || urand() < exp(-dlt / T)) {
            cur = nc; acc++;
            if (cur < best) {
                best = cur; memcpy(bestval, val, sizeof val);
                fprintf(stderr, "NEWBEST full=%d it=%ld\n", best * m_order, it);
                if (best == 0) break;
            }
        } else {
            val[eo] = old;
            for (int j = 0; j < eo_size[eo]; j++) ev[eo_edges[eo][j]] = old;
        }
    }
    memcpy(val, bestval, sizeof val);
    set_voltages();
    int chk = eval_reps();
    char path[512];
    snprintf(path, sizeof path, "%s.best", outp); write_sol(path);
    if (chk == 0 || getenv("WRITE_EDGES")) { snprintf(path, sizeof path, "%s.edges", outp); write_edges(path); }
    printf("RESULT full_cost=%d reps_cost=%d m=%d k=%d n=%d it=%ld acc=%ld check=%d\n",
           chk * m_order, chk, m_order, k, NB * k, it, acc, chk);
    return 0;
}
