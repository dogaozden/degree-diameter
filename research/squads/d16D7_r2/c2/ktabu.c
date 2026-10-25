/* ktabu.c: k-fixed penalty tabu search for a maximum independent set of an orbit graph (card c2, squad d16D7_r2).
 *
 * usage: ktabu GRAPH SEED OUT CPU_SECONDS RNG_SEED [STALL_ITERS]
 *
 * S is a k-subset; f(S) = number of edges with both ends in S (the penalty).
 * Move = swap: remove u in S (a member with the most conflicts, non-tabu), add v outside S (a vertex with the
 * fewest neighbours in S, non-tabu). delta = conf[v] - [u ~ v] - conf[u]; a pair with u ~ v is preferred.
 * conf[x] = |N(x) cap S| is maintained incrementally for all x (O(deg) per move), and vertices are kept in
 * buckets by (group, conf) so the extreme levels are found without scanning all vertices.
 * Tabu: a removed u may not re-enter for tt = 7 + rand(0..#conflicting) iterations; an added v may not leave
 * for 2..5 iterations. Aspiration: a tabu move is taken if it reaches a new best f at this k.
 * f == 0: S is an independent set of size k; it is written to OUT (atomic rename), then the outside vertex with
 * the fewest conflicts is added and the search continues with k+1.
 * Stall: after STALL_ITERS iterations without a new best f at this k, the elite set (best f at this k) is restored
 * and 3..10 random swaps are applied.
 * CPU time is measured with CLOCK_PROCESS_CPUTIME_ID.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

static int n, D;
static int *deg, **nb;
static int *conf, *inS, *nxt, *prv;
static int *headv[2];          /* headv[g][c]: first vertex of group g (0 outside, 1 in S) with conf == c */
static int *Sl, *Spos, K;      /* members of S, their positions in Sl, and |S| */
static int f;                  /* number of edges inside S */
static long long it;
static long long *tabuE, *tabuL;   /* tabuE[x] > it: x may not enter S; tabuL[x] > it: x may not leave S */
static int *Ul, *Vl;           /* candidate buffers */
static uint64_t rs = 88172645463325252ULL;

static inline uint64_t rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline int rndint(int m) { return (int)(rnd64() % (uint64_t)m); }

static double cpu_now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &ts);
    return ts.tv_sec + 1e-9 * ts.tv_nsec;
}

static inline void bl_remove(int x) {
    int g = inS[x], c = conf[x];
    if (prv[x] >= 0) nxt[prv[x]] = nxt[x];
    else headv[g][c] = nxt[x];
    if (nxt[x] >= 0) prv[nxt[x]] = prv[x];
}

static inline void bl_insert(int x) {
    int g = inS[x], c = conf[x];
    prv[x] = -1;
    nxt[x] = headv[g][c];
    if (nxt[x] >= 0) prv[nxt[x]] = x;
    headv[g][c] = x;
}

static void add_v(int v) {
    bl_remove(v);
    inS[v] = 1;
    bl_insert(v);
    Spos[v] = K;
    Sl[K++] = v;
    f += conf[v];                       /* edges from v to the current S (v not yet in it) */
    for (int j = 0; j < deg[v]; j++) {
        int w = nb[v][j];
        bl_remove(w); conf[w]++; bl_insert(w);
    }
}

static void rem_v(int u) {
    bl_remove(u);
    inS[u] = 0;
    bl_insert(u);
    int p = Spos[u], last = Sl[--K];
    Sl[p] = last; Spos[last] = p;
    f -= conf[u];                       /* edges from u to the rest of S */
    for (int j = 0; j < deg[u]; j++) {
        int w = nb[u][j];
        bl_remove(w); conf[w]--; bl_insert(w);
    }
}

/* outside vertex with the fewest neighbours in S (random among ties, tabu ignored) */
static int pick_min_outside(void) {
    int cnt = 0;
    for (int c = 0; c < D && cnt == 0; c++)
        for (int x = headv[0][c]; x >= 0; x = nxt[x]) Vl[cnt++] = x;
    return Vl[rndint(cnt)];
}

/* best swap among non-tabu candidates (allow != 0: tabu ignored). Returns 0 if no swap exists. */
static int pick_move(int allow, int *pu, int *pv, int *pd) {
    int nU = 0, nV = 0, cs = -1, co = -1;
    for (int c = D - 1; c >= 0 && nU == 0; c--) {
        for (int x = headv[1][c]; x >= 0; x = nxt[x])
            if (allow || tabuL[x] <= it) Ul[nU++] = x;
        if (nU) cs = c;
    }
    if (nU == 0) return 0;
    for (int c = 0; c < D && nV == 0; c++) {
        for (int x = headv[0][c]; x >= 0; x = nxt[x])
            if (allow || tabuE[x] <= it) Vl[nV++] = x;
        if (nV) co = c;
    }
    if (nV == 0) return 0;
    /* a pair u ~ v gives delta = co - 1 - cs (v loses u as a conflict): take one if it exists */
    int start = rndint(nU);
    for (int i = 0; i < nU; i++) {
        int u = Ul[(start + i) % nU];
        int dg = deg[u];
        if (dg == 0) continue;
        int off = rndint(dg);
        for (int j = 0; j < dg; j++) {
            int v = nb[u][(off + j) % dg];
            if (!inS[v] && conf[v] == co && (allow || tabuE[v] <= it)) {
                *pu = u; *pv = v; *pd = co - 1 - cs;
                return 1;
            }
        }
    }
    *pu = Ul[rndint(nU)];
    *pv = Vl[rndint(nV)];
    *pd = co - cs;
    return 1;
}

static int verify_indep(void) {
    for (int i = 0; i < K; i++) {
        int u = Sl[i];
        if (!inS[u]) return 0;
        for (int j = 0; j < deg[u]; j++) if (inS[nb[u][j]]) return 0;
    }
    return 1;
}

/* full recomputation of conf and f: returns 1 if the incremental state is consistent */
static int check_state(void) {
    long long tot = 0;
    for (int x = 0; x < n; x++) {
        int c = 0;
        for (int j = 0; j < deg[x]; j++) c += inS[nb[x][j]];
        if (c != conf[x]) return 0;
        if (inS[x]) tot += c;
    }
    return tot == 2LL * f;
}

static void save_sol(const char *of, const int *S, int k) {
    char tmp[1024];
    snprintf(tmp, sizeof tmp, "%s.tmp", of);
    FILE *o = fopen(tmp, "w");
    if (!o) { perror(tmp); exit(4); }
    for (int i = 0; i < k; i++) fprintf(o, "%d\n", S[i]);
    fclose(o);
    rename(tmp, of);
}

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: ktabu GRAPH SEED OUT CPU_SECONDS RNG_SEED [STALL_ITERS]\n");
        return 1;
    }
    const char *gf = argv[1], *sf = argv[2], *of = argv[3];
    double budget = atof(argv[4]);
    rs ^= (uint64_t)strtoull(argv[5], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 50; i++) rnd64();
    long long STALL = argc > 6 ? atoll(argv[6]) : 3000000LL;

    /* graph: "M E", then per vertex "idx rep deg n1 ... n_deg" */
    FILE *fp = fopen(gf, "r");
    if (!fp) { perror(gf); return 1; }
    int M, E;
    if (fscanf(fp, "%d %d", &M, &E) != 2) return 1;
    n = M;
    deg = calloc(n, sizeof(int));
    nb = calloc(n, sizeof(int *));
    for (int i = 0; i < n; i++) {
        int idx, rep, dg;
        if (fscanf(fp, "%d %d %d", &idx, &rep, &dg) != 3) { fprintf(stderr, "bad graph line %d\n", i); return 1; }
        deg[idx] = dg;
        nb[idx] = malloc(sizeof(int) * (dg > 0 ? dg : 1));
        for (int j = 0; j < dg; j++) if (fscanf(fp, "%d", &nb[idx][j]) != 1) return 1;
    }
    fclose(fp);
    int maxdeg = 0;
    for (int i = 0; i < n; i++) if (deg[i] > maxdeg) maxdeg = deg[i];
    D = maxdeg + 2;

    conf = calloc(n, sizeof(int));
    inS = calloc(n, sizeof(int));
    nxt = malloc(sizeof(int) * n);
    prv = malloc(sizeof(int) * n);
    headv[0] = malloc(sizeof(int) * D);
    headv[1] = malloc(sizeof(int) * D);
    for (int c = 0; c < D; c++) headv[0][c] = headv[1][c] = -1;
    Sl = malloc(sizeof(int) * n);
    Spos = malloc(sizeof(int) * n);
    tabuE = calloc(n, sizeof(long long));
    tabuL = calloc(n, sizeof(long long));
    Ul = malloc(sizeof(int) * n);
    Vl = malloc(sizeof(int) * n);
    K = 0; f = 0; it = 0;
    for (int x = 0; x < n; x++) bl_insert(x);

    /* seed + best extra vertex */
    FILE *sp = fopen(sf, "r");
    if (!sp) { perror(sf); return 1; }
    int *seed = malloc(sizeof(int) * n), s0 = 0, v;
    while (fscanf(sp, "%d", &v) == 1) {
        if (v >= 0 && v < n && !inS[v]) { add_v(v); seed[s0++] = v; }
    }
    fclose(sp);
    fprintf(stderr, "seed size %d f(seed)=%d\n", K, f);
    add_v(pick_min_outside());
    fprintf(stderr, "start k=%d f=%d\n", K, f);

    int *elite = malloc(sizeof(int) * n);
    int eliteK = K;
    memcpy(elite, Sl, sizeof(int) * K);
    int bestf = f;
    long long last_improve = 0, nrest = 0;
    int kbest = 0;
    double t0 = cpu_now(), next_log = 30.0;

    for (;;) {
        it++;
        if ((it & 1023) == 0) {
            double el = cpu_now() - t0;
            if (el >= budget) break;
            if (el >= next_log) {
                next_log += 30.0;
                if (!check_state()) { fprintf(stderr, "INTERNAL STATE ERROR\n"); return 3; }
                fprintf(stderr, "t=%.0f k=%d f=%d bestf=%d it=%lld restarts=%lld\n", el, K, f, bestf, it, nrest);
            }
        }
        if (f == 0) {
            if (!verify_indep()) { fprintf(stderr, "INTERNAL: S not independent\n"); return 2; }
            if (K > kbest) { save_sol(of, Sl, K); kbest = K; }
            fprintf(stderr, "FOUND independent set k=%d t=%.1f it=%lld\n", K, cpu_now() - t0, it);
            add_v(pick_min_outside());
            bestf = f;
            eliteK = K;
            memcpy(elite, Sl, sizeof(int) * K);
            last_improve = it;
            continue;
        }

        int cs_all = -1, co_all = -1;
        for (int c = D - 1; c >= 0; c--) if (headv[1][c] >= 0) { cs_all = c; break; }
        for (int c = 0; c < D; c++) if (headv[0][c] >= 0) { co_all = c; break; }
        int u = -1, w = -1, d = 0, asp = 0;
        if (f + (co_all - cs_all - 1) < bestf) {          /* a tabu move might reach a new best */
            if (pick_move(1, &u, &w, &d) && f + d < bestf) asp = 1;
        }
        if (!asp && !pick_move(0, &u, &w, &d)) pick_move(1, &u, &w, &d);
        if (u < 0 || w < 0) { fprintf(stderr, "no move\n"); return 5; }

        int nc = 0;
        for (int i = 0; i < K; i++) if (conf[Sl[i]] > 0) nc++;
        tabuE[u] = it + 7 + rndint(nc + 1);
        rem_v(u);
        add_v(w);
        tabuL[w] = it + 2 + rndint(4);

        if (f < bestf) {
            bestf = f;
            eliteK = K;
            memcpy(elite, Sl, sizeof(int) * K);
            last_improve = it;
        } else if (it - last_improve > STALL) {
            while (K > 0) rem_v(Sl[0]);
            for (int i = 0; i < eliteK; i++) add_v(elite[i]);
            int P = 3 + rndint(8);
            for (int p = 0; p < P; p++) {
                int uu = Sl[rndint(K)], vv;
                do vv = rndint(n); while (inS[vv]);
                rem_v(uu);
                add_v(vv);
            }
            last_improve = it;
            nrest++;
        }
    }
    double el = cpu_now() - t0;
    fprintf(stderr, "END t=%.1f kbest=%d last_k=%d bestf(k)=%d it=%lld restarts=%lld\n",
            el, kbest, K, bestf, it, nrest);
    printf("kbest %d\n", kbest);
    return 0;
}
