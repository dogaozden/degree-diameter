/* c4 (squad d16D7_r2): randomized dynamic min-degree greedy constructions + (1,2)-swap local search, restarted until a
 * CPU budget is spent. Independent sets of an orbit graph (vertex = orbit, edge = two orbits with collinear members).
 *
 * Constructions. Restarts are dealt round-robin to 8 configurations, so every variant gets the same number of restarts:
 *   kind 0, r = 1      (A) plain dynamic min-degree greedy, ties broken at random
 *   kind 0, r = 2..5   (B) GRASP: pick uniformly among the r lowest-degree remaining vertices (ties random)
 *   kind 1, sigma      (C) pick the vertex minimising (remaining vertices it would delete = deg+1) - U[0,sigma)
 * The greedy takes v and deletes v and its remaining neighbours; degrees are kept in bucket lists (O(1) updates).
 *
 * Local search. (1,2)-swap: remove x from the set, insert two non-adjacent vertices u,w whose only solution neighbour is
 * x, then insert every free vertex (no solution neighbour). Applied until a full pass finds no move.
 *
 * The best set is checked for independence against the adjacency bitsets and written to OUT (one index per line) each
 * time it improves, so an interrupted run still leaves a valid file.
 *
 * usage: mdg GRAPH OUT SEED CPU_BUDGET_SECONDS      (the budget is total process CPU time as reported by clock())
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/types.h>
#include <time.h>

#define MAXD 256   /* bucket count: remaining degrees are below this */
#define MAXDEG 512 /* largest vertex degree accepted */
#define NCFG 8

typedef struct {
    int kind, r;
    double sigma;
    const char *name;
} cfg_t;

static const cfg_t cfg[NCFG] = {
    {0, 1, 0.0, "A-mindeg"},  {0, 2, 0.0, "B-grasp-r2"}, {0, 3, 0.0, "B-grasp-r3"}, {0, 4, 0.0, "B-grasp-r4"},
    {0, 5, 0.0, "B-grasp-r5"}, {1, 0, 0.5, "C-noise0.5"}, {1, 0, 1.0, "C-noise1.0"}, {1, 0, 2.0, "C-noise2.0"},
};

static int M, E, W;
static int *gdeg, *gstart, *adj; /* CSR-like: neighbours of v are adj[gstart[v] .. gstart[v]+gdeg[v]) */
static uint64_t *bits;           /* adjacency bitset, W words per row */
#define ADJ(a, b) ((int)((bits[(size_t)(a) * W + ((b) >> 6)] >> ((b) & 63)) & 1u))

/* ---- PRNG: xoshiro256** seeded by splitmix64 ---- */
static uint64_t rs[4];
static uint64_t splitmix(uint64_t *x) {
    uint64_t z = (*x += 0x9e3779b97f4a7c15ULL);
    z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
    z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
    return z ^ (z >> 31);
}
static inline uint64_t rotl(uint64_t x, int k) { return (x << k) | (x >> (64 - k)); }
static inline uint64_t rnd64(void) {
    uint64_t result = rotl(rs[1] * 5, 7) * 9;
    uint64_t t = rs[1] << 17;
    rs[2] ^= rs[0];
    rs[3] ^= rs[1];
    rs[1] ^= rs[2];
    rs[0] ^= rs[3];
    rs[2] ^= t;
    rs[3] = rotl(rs[3], 45);
    return result;
}
static inline uint32_t rndint(uint32_t n) { return (uint32_t)(((rnd64() >> 32) * (uint64_t)n) >> 32); } /* [0,n) */
static inline double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static void die(const char *msg, const char *arg) {
    fprintf(stderr, "mdg: %s %s\n", msg, arg ? arg : "");
    exit(1);
}

static void load_graph(const char *path) {
    FILE *f = fopen(path, "r");
    if (!f) die("cannot open", path);
    char *line = NULL;
    size_t cap = 0;
    ssize_t len = getline(&line, &cap, f);
    if (len < 0 || sscanf(line, "%d %d", &M, &E) != 2 || M <= 0) die("bad header in", path);
    gdeg = malloc(sizeof(int) * M);
    gstart = malloc(sizeof(int) * M);
    size_t acap = 2 * (size_t)E + 1024, alen = 0;
    adj = malloc(sizeof(int) * acap);
    int nread = 0;
    while ((len = getline(&line, &cap, f)) >= 0) {
        char *p = line, *end;
        long idx = strtol(p, &end, 10);
        if (end == p) continue; /* blank line */
        p = end;
        strtol(p, &end, 10); /* rep: ignored */
        p = end;
        long d = strtol(p, &end, 10);
        p = end;
        if (idx < 0 || idx >= M || d < 0 || d > MAXDEG) die("bad vertex line in", path);
        if (alen + (size_t)d > acap) {
            acap = 2 * (alen + (size_t)d);
            adj = realloc(adj, sizeof(int) * acap);
        }
        gstart[idx] = (int)alen;
        gdeg[idx] = (int)d;
        for (long i = 0; i < d; i++) {
            long v = strtol(p, &end, 10);
            if (end == p) die("short line in", path);
            p = end;
            adj[alen++] = (int)v;
        }
        nread++;
    }
    fclose(f);
    free(line);
    if (nread != M) die("wrong number of vertex lines in", path);
    W = (M + 63) / 64;
    bits = calloc((size_t)M * W, sizeof(uint64_t));
    if (!bits) die("out of memory", NULL);
    for (int v = 0; v < M; v++)
        for (int i = 0; i < gdeg[v]; i++) {
            int u = adj[gstart[v] + i];
            if (u < 0 || u >= M || u == v) die("bad neighbour in", path);
            bits[(size_t)v * W + (u >> 6)] |= 1ULL << (u & 63);
        }
    for (int v = 0; v < M; v++)
        for (int i = 0; i < gdeg[v]; i++)
            if (!ADJ(adj[gstart[v] + i], v)) die("asymmetric adjacency in", path);
}

/* ---- construction state ---- */
static int *bkt;   /* bucket d holds bkt[d*M .. d*M+bsz[d]) : alive vertices with remaining degree d */
static int bsz[MAXD];
static int *bpos, *dg; /* position in its bucket, current remaining degree */
static unsigned char *alive;
static int dmin, nrem, Slen;
static int *Sc, *closedbuf;

static inline void bk_add(int v, int d) {
    bpos[v] = bsz[d];
    bkt[(size_t)d * M + bsz[d]++] = v;
}
static inline void bk_del(int v, int d) {
    int p = bpos[v];
    int last = bkt[(size_t)d * M + --bsz[d]];
    bkt[(size_t)d * M + p] = last;
    bpos[last] = p;
}
static inline void dec_deg(int z) {
    int d = dg[z];
    bk_del(z, d);
    dg[z] = d - 1;
    bk_add(z, d - 1);
    if (d - 1 < dmin) dmin = d - 1;
}

static void construct_reset(void) {
    memset(bsz, 0, sizeof bsz);
    dmin = MAXD;
    for (int v = 0; v < M; v++) {
        alive[v] = 1;
        dg[v] = gdeg[v];
        if (dg[v] < dmin) dmin = dg[v];
        bk_add(v, dg[v]);
    }
    nrem = M;
    Slen = 0;
}

/* put v into the set: delete v and its remaining neighbours, updating remaining degrees */
static void greedy_take(int v) {
    int nc = 0;
    closedbuf[nc++] = v;
    for (int i = 0; i < gdeg[v]; i++) {
        int w = adj[gstart[v] + i];
        if (alive[w]) closedbuf[nc++] = w;
    }
    for (int i = 0; i < nc; i++) {
        int u = closedbuf[i];
        alive[u] = 0;
        bk_del(u, dg[u]);
    }
    for (int i = 0; i < nc; i++) {
        int u = closedbuf[i];
        for (int j = 0; j < gdeg[u]; j++) {
            int z = adj[gstart[u] + j];
            if (alive[z]) dec_deg(z);
        }
    }
    nrem -= nc;
    Sc[Slen++] = v;
}

/* (A/B) uniform among the r lowest-degree remaining vertices (ties at random); r = 1 is plain min-degree */
static int pick_grasp(int r) {
    while (bsz[dmin] == 0) dmin++;
    if (r <= 1) return bkt[(size_t)dmin * M + rndint((uint32_t)bsz[dmin])];
    int cand[8], nc = 0;
    for (int d = dmin; d < MAXD && nc < r; d++) {
        int k = bsz[d];
        if (k == 0) continue;
        int need = r - nc;
        if (need > k) need = k;
        if (need == k) {
            for (int i = 0; i < k; i++) cand[nc++] = bkt[(size_t)d * M + i];
        } else {
            int idx[8], ni = 0;
            while (ni < need) {
                int t = (int)rndint((uint32_t)k), dup = 0;
                for (int j = 0; j < ni; j++)
                    if (idx[j] == t) dup = 1;
                if (!dup) idx[ni++] = t;
            }
            for (int i = 0; i < need; i++) cand[nc++] = bkt[(size_t)d * M + idx[i]];
        }
    }
    return cand[rndint((uint32_t)nc)];
}

/* (C) minimise (deg+1) - U[0,sigma) over the remaining vertices */
static int pick_noisy(double sigma) {
    while (bsz[dmin] == 0) dmin++;
    int best = -1;
    double bs = 1e300;
    for (int d = dmin; d < MAXD; d++) {
        if ((double)(d + 1) - sigma > bs) break; /* no vertex of this or a higher bucket can win */
        for (int i = 0; i < bsz[d]; i++) {
            int v = bkt[(size_t)d * M + i];
            double sc = (double)(d + 1) - sigma * rnd01();
            if (sc < bs) {
                bs = sc;
                best = v;
            }
        }
    }
    return best;
}

/* ---- solution and (1,2)-swap local search ---- */
static unsigned char *inS;
static int *tight; /* number of solution neighbours */
static int ns;
static int *ord, *solbuf;

static inline void ls_insert(int v) {
    inS[v] = 1;
    ns++;
    for (int i = 0; i < gdeg[v]; i++) tight[adj[gstart[v] + i]]++;
}
static inline void ls_remove(int v) {
    inS[v] = 0;
    ns--;
    for (int i = 0; i < gdeg[v]; i++) tight[adj[gstart[v] + i]]--;
}

static void ls_from_construction(void) {
    memset(inS, 0, M);
    memset(tight, 0, sizeof(int) * M);
    ns = 0;
    for (int i = 0; i < Slen; i++) ls_insert(Sc[i]);
}

/* one (1,2)-swap around solution vertex x, if one exists; returns 1 if applied */
static int try_swap(int x) {
    int L[MAXDEG], nl = 0;
    for (int i = 0; i < gdeg[x]; i++) {
        int w = adj[gstart[x] + i];
        if (!inS[w] && tight[w] == 1) L[nl++] = w; /* x is the only solution neighbour of w */
    }
    if (nl < 2) return 0;
    for (int i = nl - 1; i > 0; i--) {
        int j = (int)rndint((uint32_t)(i + 1)), t = L[i];
        L[i] = L[j];
        L[j] = t;
    }
    for (int i = 0; i < nl; i++)
        for (int j = i + 1; j < nl; j++) {
            int u = L[i], w = L[j];
            if (ADJ(u, w)) continue;
            ls_remove(x);
            ls_insert(u);
            ls_insert(w);
            for (int k = 0; k < nl; k++) {
                int z = L[k];
                if (!inS[z] && tight[z] == 0) ls_insert(z);
            }
            return 1;
        }
    return 0;
}

static void local_search(void) {
    int changed = 1;
    while (changed) {
        changed = 0;
        int n = 0;
        for (int v = 0; v < M; v++)
            if (inS[v]) ord[n++] = v;
        for (int i = n - 1; i > 0; i--) {
            int j = (int)rndint((uint32_t)(i + 1)), t = ord[i];
            ord[i] = ord[j];
            ord[j] = t;
        }
        for (int i = 0; i < n; i++) {
            int x = ord[i];
            if (inS[x] && try_swap(x)) changed = 1;
        }
    }
}

static int collect_solution(void) {
    int n = 0;
    for (int v = 0; v < M; v++)
        if (inS[v]) solbuf[n++] = v;
    return n;
}

/* verify independence of the first n entries of solbuf, then write them (tmp file + rename) */
static int write_solution(const char *path, int n) {
    for (int i = 0; i < n; i++)
        for (int j = i + 1; j < n; j++)
            if (ADJ(solbuf[i], solbuf[j])) return 0;
    char tmp[4096];
    snprintf(tmp, sizeof tmp, "%s.tmp", path);
    FILE *f = fopen(tmp, "w");
    if (!f) return 0;
    for (int i = 0; i < n; i++) fprintf(f, "%d\n", solbuf[i]);
    if (fclose(f) != 0) return 0;
    return rename(tmp, path) == 0;
}

static uint64_t splitmix_seed(uint64_t s) { return splitmix(&s); }

int main(int argc, char **argv) {
    if (argc != 5) {
        fprintf(stderr, "usage: %s GRAPH OUT SEED CPU_BUDGET_SECONDS\n", argv[0]);
        return 2;
    }
    load_graph(argv[1]);
    const char *out = argv[2];
    uint64_t sx = (uint64_t)strtoull(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    sx = splitmix_seed(sx * 0x2545F4914F6CDD1DULL + 7);
    for (int i = 0; i < 4; i++) rs[i] = splitmix(&sx);

    bkt = malloc(sizeof(int) * (size_t)MAXD * M);
    bpos = malloc(sizeof(int) * M);
    dg = malloc(sizeof(int) * M);
    alive = malloc(M);
    Sc = malloc(sizeof(int) * M);
    closedbuf = malloc(sizeof(int) * (MAXDEG + 1));
    inS = malloc(M);
    tight = malloc(sizeof(int) * M);
    ord = malloc(sizeof(int) * M);
    solbuf = malloc(sizeof(int) * M);
    if (!bkt || !bpos || !dg || !alive || !Sc || !closedbuf || !inS || !tight || !ord || !solbuf)
        die("out of memory", NULL);

    long it = 0, runs[NCFG] = {0}, sum[NCFG] = {0};
    int mx[NCFG] = {0}, best = 0, bestcfg = -1;
    while ((double)clock() / CLOCKS_PER_SEC < budget) {
        int c = (int)(it % NCFG);
        it++;
        construct_reset();
        while (nrem > 0) {
            int v = cfg[c].kind == 0 ? pick_grasp(cfg[c].r) : pick_noisy(cfg[c].sigma);
            greedy_take(v);
        }
        ls_from_construction();
        local_search();
        int sz = ns;
        runs[c]++;
        sum[c] += sz;
        if (sz > mx[c]) mx[c] = sz;
        if (sz > best) {
            best = sz;
            bestcfg = c;
            int n = collect_solution();
            if (!write_solution(out, n)) die("best set is not independent or cannot be written:", out);
            printf("restart %ld cpu %.1fs best %d (%s)\n", it, (double)clock() / CLOCKS_PER_SEC, best, cfg[c].name);
            fflush(stdout);
        }
    }
    printf("done: restarts %ld best %d found by %s\n", it, best, bestcfg >= 0 ? cfg[bestcfg].name : "-");
    for (int c = 0; c < NCFG; c++)
        printf("variant %-13s runs %6ld mean %.2f max %d\n", cfg[c].name, runs[c],
               runs[c] ? (double)sum[c] / (double)runs[c] : 0.0, mx[c]);
    return 0;
}
