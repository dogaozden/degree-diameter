/* ils.c (card c1, squad c157b-r1): ARW-style iterated local search for non-collinear point sets of H(11).
   Elements = points, cells = lines.  tight[p] = number of chosen points collinear with p (at most one chosen
   point per line); owner[l] = chosen point on line l, or -1.
   Moves:
     (1,k)-swap, improving for k >= 2: remove chosen x, insert one 1-tight point from each of k lines through x.
     plateau (1,1)-swap on random chosen points; the removed point is tabu for TABU iterations (no re-entry as a pick).
     greedy refill of points that became free.
   Perturbation, PMODE 0: force-insert a cluster of K points (KMIN..KMAX), pairwise non-collinear, each within
     incidence distance 4 of a random earlier member; their chosen neighbours are removed and made tabu.
   Perturbation, PMODE 1: ruin: remove the R (KMIN..KMAX) chosen points nearest to a random point (BFS in the
     collinearity graph), made tabu, then recreate by local search.
   After the perturbation: local search, refill of removed points that are free again, PSTEPS plateau steps.
   Acceptance (ARW): a worse set (deficit d below the current, d* below the best) is kept with probability
     1/(1+d*d*); otherwise the whole iteration is undone with an undo log.
   usage: ils HEXBIN SEED SECONDS START|- OUT PMODE KMIN KMAX PSTEPS TABU RESTART FRAC
     START: point ids one per line, or '-' for a random greedy start.
     FRAC:  fraction of START removed at random before a random greedy refill (0 = none).
     RESTART: reset the walk to the best set after this many iterations without a new best (0 = never).
   OUT receives the best set (ids one per line) during the run and at the end.
   build: gcc -O2 -Wall -o ils ils.c */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>

static int q, N, Q1, TABU;
static int *EC, *CE;                       /* point -> its lines (EC), line -> its points (CE), Q1 each */
static int *owner, *tight, *sol, *pos, ns;
static char *in;
static uint64_t rs;
static long curit;
static long *tabu_until;

static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) { struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts); return ts.tv_sec + 1e-9 * ts.tv_nsec; }

static int *queue, nq; static char *qflag;   /* chosen points to try an improving swap at */
static int *freeq, nf; static char *fflag;   /* points that may have become free */
static int *ulog; static long nlog, ulogmax; static int logging, ulog_overflow;

static inline void logop(int v) { if (!logging) return; if (nlog < ulogmax) ulog[nlog++] = v; else ulog_overflow = 1; }
static inline void pushq(int e) { if (!qflag[e]) { qflag[e] = 1; queue[nq++] = e; } }
static inline void pushf(int e) { if (!fflag[e]) { fflag[e] = 1; freeq[nf++] = e; } }

static void add_raw(int e) {
    in[e] = 1; pos[e] = ns; sol[ns++] = e;
    for (int i = 0; i < Q1; i++) {
        int c = EC[e * Q1 + i]; owner[c] = e;
        for (int t = 0; t < Q1; t++) { int f = CE[c * Q1 + t]; if (f != e) tight[f]++; }
    }
}
static void rem_raw(int e) {
    in[e] = 0; int p = pos[e]; sol[p] = sol[--ns]; pos[sol[p]] = p;
    for (int i = 0; i < Q1; i++) {
        int c = EC[e * Q1 + i]; owner[c] = -1;
        for (int t = 0; t < Q1; t++) {
            int f = CE[c * Q1 + t]; if (f == e) continue;
            if (--tight[f] <= 1) {
                for (int i2 = 0; i2 < Q1; i2++) { int o = owner[EC[f * Q1 + i2]]; if (o >= 0) pushq(o); }
                if (tight[f] == 0 && !in[f]) pushf(f);
            }
        }
    }
}
static void add_op(int e) { add_raw(e); logop(e); }
static void rem_op(int e) { rem_raw(e); logop(~e); }
static void clear_queues(void) {
    for (int i = 0; i < nq; i++) qflag[queue[i]] = 0;
    nq = 0;
    for (int i = 0; i < nf; i++) fflag[freeq[i]] = 0;
    nf = 0;
}
static void undo_log(void) {
    for (long i = nlog - 1; i >= 0; i--) { int v = ulog[i]; if (v >= 0) rem_raw(v); else add_raw(~v); }
    nlog = 0; clear_queues();
}
static void rebuild(const int *ids, int n) {
    for (int i = 0; i < N; i++) { owner[i] = -1; tight[i] = 0; in[i] = 0; }
    ns = 0; nlog = 0; clear_queues();
    for (int i = 0; i < n; i++) add_raw(ids[i]);
}

static int pick[32];
/* swap at chosen x: one 1-tight point from each line of x that has one. Performs it when gain >= 1, or gain 0
   if allow_zero (plateau move; the removed x becomes tabu). Returns gain, or -1 when nothing was done. */
static int try_swap(int x, int allow_zero) {
    int ncell = 0;
    for (int i = 0; i < Q1; i++) {
        int c = EC[x * Q1 + i], k = 0, chosen = -1;
        for (int t = 0; t < Q1; t++) {
            int f = CE[c * Q1 + t];
            if (!in[f] && tight[f] == 1 && tabu_until[f] <= curit) { k++; if (rnd() % k == 0) chosen = f; }
        }
        if (chosen >= 0) pick[ncell++] = chosen;
    }
    if (ncell >= 2 || (allow_zero && ncell == 1)) {
        rem_op(x);
        for (int i = 0; i < ncell; i++) add_op(pick[i]);
        if (ncell == 1) tabu_until[x] = curit + TABU;
        return ncell - 1;
    }
    return -1;
}
static void local_search(void) {
    while (nf || nq) {
        if (nf) { int f = freeq[--nf]; fflag[f] = 0; if (!in[f] && tight[f] == 0) add_op(f); }
        else    { int x = queue[--nq]; qflag[x] = 0; if (in[x]) try_swap(x, 0); }
    }
}

static int cl[64];
static int collinear(int a, int b) {
    for (int i = 0; i < Q1; i++) {
        int l = EC[a * Q1 + i];
        for (int t = 0; t < Q1; t++) if (CE[l * Q1 + t] == b) return 1;
    }
    return 0;
}
/* cluster of up to k pairwise non-collinear non-chosen points, each at incidence distance <= 4 from an earlier member */
static int build_cluster(int k) {
    int x;
    do { x = (int)(rnd() % N); } while (in[x]);
    for (int tr = 0; tr < 3 && tight[x] > 1; tr++) { int y = (int)(rnd() % N); if (!in[y] && tight[y] < tight[x]) x = y; }
    int m = 0; cl[m++] = x;
    for (int tries = 0; m < k && tries < 500; tries++) {
        int a = cl[rnd() % m];
        int l = EC[a * Q1 + rnd() % Q1];
        int z = CE[l * Q1 + rnd() % Q1];
        if (z == a) continue;
        int l2 = EC[z * Q1 + rnd() % Q1];
        if (l2 == l) continue;
        int y = CE[l2 * Q1 + rnd() % Q1];
        if (y == z || in[y]) continue;
        int ok = 1;
        for (int j = 0; j < m && ok; j++) if (cl[j] == y || collinear(cl[j], y)) ok = 0;
        if (ok) cl[m++] = y;
    }
    return m;
}

static int *bq, *vis, vstamp = 1;
/* ruin: BFS in the collinearity graph from seed; remove the first R chosen points met; returns how many (<= cap) */
static int ruin(int seed, int R, int *out, int cap) {
    vstamp++;
    int head = 0, tail = 0, nr = 0;
    bq[tail++] = seed; vis[seed] = vstamp;
    while (head < tail && nr < R) {
        int p = bq[head++];
        if (in[p]) { rem_op(p); if (nr < cap) out[nr] = p; nr++; }
        for (int i = 0; i < Q1; i++) {
            int l = EC[p * Q1 + i];
            for (int t = 0; t < Q1; t++) { int r = CE[l * Q1 + t]; if (vis[r] != vstamp) { vis[r] = vstamp; bq[tail++] = r; } }
        }
    }
    return nr < cap ? nr : cap;
}

/* ---- pmode 2: exact re-optimisation of a ruined region ----
   After ruin() removed R chosen points, the candidates F are the free points (not chosen, tight 0) among the points
   collinear with a removed point (this includes the removed points). Any independent set of F can be added to the
   rest of the solution, so a maximum independent set of F (branch and bound, node-limited) is the best recreate. */
typedef unsigned __int128 u128;
#define MAXF 128
static u128 fadj[MAXF];
static int F[MAXF], nF, mis_cur[MAXF], mis_bestset[MAXF], mis_best;
static long mis_nodes, mis_limit = 20000;
static int *fidx, *fst, fstamp = 1;
static inline int pc128(u128 x) { return __builtin_popcountll((uint64_t)x) + __builtin_popcountll((uint64_t)(x >> 64)); }
static void mis_rec(u128 P, int size) {
    if (++mis_nodes > mis_limit) return;
    if (P == 0) { if (size > mis_best) { mis_best = size; memcpy(mis_bestset, mis_cur, sizeof(int) * size); } return; }
    if (size + pc128(P) <= mis_best) return;
    int vmax = -1, dmax = -1;
    for (int i = 0; i < nF; i++) {
        if (!((P >> i) & 1)) continue;
        int d = pc128(fadj[i] & P);
        if (d <= 1) { mis_cur[size] = i; mis_rec(P & ~fadj[i] & ~((u128)1 << i), size + 1); return; }
        if (d > dmax) { dmax = d; vmax = i; }
    }
    if (vmax < 0) return;
    mis_cur[size] = vmax;
    mis_rec(P & ~fadj[vmax] & ~((u128)1 << vmax), size + 1);
    mis_rec(P & ~((u128)1 << vmax), size);
}
static int lns_recreate(int nrem, const int *rem) {
    fstamp++; nF = 0;
    for (int j = 0; j < nrem; j++) {
        int p = rem[j];
        for (int i = 0; i < Q1; i++) {
            int l = EC[p * Q1 + i];
            for (int t = 0; t < Q1; t++) {
                int r = CE[l * Q1 + t];
                if (fst[r] == fstamp) continue;
                fst[r] = fstamp;
                if (!in[r] && tight[r] == 0 && nF < MAXF) F[nF++] = r;
            }
        }
    }
    for (int i = nF - 1; i > 0; i--) { int j = (int)(rnd() % (uint64_t)(i + 1)); int t = F[i]; F[i] = F[j]; F[j] = t; }
    for (int i = 0; i < nF; i++) fidx[F[i]] = i;
    for (int i = 0; i < nF; i++) {
        fadj[i] = 0; int p = F[i];
        for (int a = 0; a < Q1; a++) {
            int l = EC[p * Q1 + a];
            for (int t = 0; t < Q1; t++) { int r = CE[l * Q1 + t]; if (r != p && fidx[r] >= 0) fadj[i] |= (u128)1 << fidx[r]; }
        }
    }
    for (int i = 0; i < nF; i++) fidx[F[i]] = -1;
    u128 all = nF >= 128 ? ~(u128)0 : (((u128)1 << nF) - 1);
    mis_best = 0; mis_nodes = 0;
    mis_rec(all, 0);
    if (mis_best < nrem) return 0;
    for (int j = 0; j < mis_best; j++) add_op(F[mis_bestset[j]]);
    return 1;
}

static void save_set(const char *fn, const int *ids, int n) {
    char tmp[4096]; snprintf(tmp, sizeof tmp, "%s.tmp", fn);
    FILE *o = fopen(tmp, "w"); if (!o) return;
    for (int i = 0; i < n; i++) fprintf(o, "%d\n", ids[i]);
    fclose(o); rename(tmp, fn);
}
static int verify_set(const int *ids, int n, char *lc) {
    memset(lc, 0, N);
    for (int i = 0; i < n; i++) {
        int p = ids[i]; if (p < 0 || p >= N) return 0;
        for (int j = 0; j < Q1; j++) { int l = EC[p * Q1 + j]; if (lc[l]) return 0; lc[l] = 1; }
    }
    return 1;
}

int main(int argc, char **argv) {
    if (argc != 13) { fprintf(stderr, "usage: ils HEXBIN SEED SECONDS START|- OUT PMODE KMIN KMAX PSTEPS TABU RESTART FRAC\n"); return 1; }
    FILE *f = fopen(argv[1], "rb"); if (!f) { perror("hex"); return 1; }
    int hdr[3]; if (fread(hdr, 4, 3, f) != 3) return 1;
    q = hdr[0]; N = hdr[1]; int L = hdr[2]; Q1 = q + 1;
    if (L != N) { fprintf(stderr, "expects L == N\n"); return 1; }
    int *LP = malloc(sizeof(int) * (size_t)L * Q1);
    if (fread(LP, 4, (size_t)L * Q1, f) != (size_t)L * Q1) return 1;
    fclose(f);
    int *PL = malloc(sizeof(int) * (size_t)N * Q1); int *cnt = calloc(N, sizeof(int));
    for (int l = 0; l < L; l++) for (int i = 0; i < Q1; i++) { int p = LP[l * Q1 + i]; PL[p * Q1 + cnt[p]++] = l; }
    free(cnt);
    EC = PL; CE = LP;

    rs = 0x9E3779B97F4A7C15ULL ^ ((uint64_t)atoll(argv[2]) * 0x2545F4914F6CDD1DULL);
    for (int i = 0; i < 20; i++) rnd();
    double secs = atof(argv[3]); const char *startfn = argv[4], *outfn = argv[5];
    int pmode = atoi(argv[6]), kmin = atoi(argv[7]), kmax = atoi(argv[8]), psteps = atoi(argv[9]);
    TABU = atoi(argv[10]); long restart = atol(argv[11]); double frac = atof(argv[12]);
    if (kmin < 1) kmin = 1;
    if (kmax < kmin) kmax = kmin;
    if (kmax > 60) kmax = 60;

    owner = malloc(sizeof(int) * N); tight = calloc(N, sizeof(int)); sol = malloc(sizeof(int) * N); pos = malloc(sizeof(int) * N);
    in = calloc(N, 1); for (int i = 0; i < N; i++) owner[i] = -1;
    queue = malloc(sizeof(int) * N); qflag = calloc(N, 1); freeq = malloc(sizeof(int) * N); fflag = calloc(N, 1);
    ulogmax = 1L << 22; ulog = malloc(sizeof(int) * ulogmax);
    tabu_until = calloc(N, sizeof(long));
    int *bestsol = malloc(sizeof(int) * N); bq = malloc(sizeof(int) * N); vis = calloc(N, sizeof(int));
    int *remlist = malloc(sizeof(int) * 4096);
    char *lc = malloc(N);
    int *perm = malloc(sizeof(int) * N);
    for (int i = 0; i < N; i++) perm[i] = i;
    fidx = malloc(sizeof(int) * N); for (int i = 0; i < N; i++) fidx[i] = -1;
    fst = calloc(N, sizeof(int));

    if (strcmp(startfn, "-") != 0) {
        FILE *g = fopen(startfn, "r"); if (!g) { perror("start"); return 1; }
        int e, loaded = 0, bad = 0;
        while (fscanf(g, "%d", &e) == 1) {
            if (e < 0 || e >= N || in[e] || tight[e]) bad++; else { add_raw(e); loaded++; }
        }
        fclose(g);
        fprintf(stderr, "loaded %d from %s (rejected %d)\n", loaded, startfn, bad);
        if (frac > 0) {
            int nr = (int)(frac * ns + 0.5);
            for (int i = 0; i < nr; i++) rem_raw(sol[rnd() % ns]);
            fprintf(stderr, "removed %d at random\n", nr);
        }
    }
    for (int i = N - 1; i > 0; i--) { int j = (int)(rnd() % (uint64_t)(i + 1)); int t = perm[i]; perm[i] = perm[j]; perm[j] = t; }
    for (int i = 0; i < N; i++) { int p = perm[i]; if (!in[p] && tight[p] == 0) add_raw(p); }
    local_search();
    int bestn = ns; memcpy(bestsol, sol, sizeof(int) * ns);
    fprintf(stderr, "start %d\n", ns);
    save_set(outfn, bestsol, bestn);
    int savedn = bestn;

    double t0 = now(), tsave = t0, tprint = t0;
    long it = 0, last_imp = 0, nworse = 0, nrej = 0, nplat = 0, nimp = 0;
    while (1) {
        if ((it & 63) == 0) {
            double el = now() - t0;
            if (el > secs) break;
            if (now() - tprint > 60) {
                tprint = now();
                fprintf(stderr, "t=%.0f it=%ld cur=%d best=%d imp=%ld worse_acc=%ld rej=%ld plat=%ld\n",
                        el, it, ns, bestn, nimp, nworse, nrej, nplat);
            }
            if (bestn > savedn && now() - tsave > 15) { save_set(outfn, bestsol, bestn); savedn = bestn; tsave = now(); }
        }
        it++; curit = it;
        int cur = ns;
        logging = 1; nlog = 0; ulog_overflow = 0;
        int nrem = 0;
        if (pmode == 0) {
            int k = kmin + (int)(rnd() % (uint64_t)(kmax - kmin + 1));
            int m = build_cluster(k);
            for (int j = 0; j < m; j++) {
                int x = cl[j];
                for (int i = 0; i < Q1; i++) {
                    int o = owner[EC[x * Q1 + i]];
                    if (o >= 0) { rem_op(o); if (nrem < 4096) remlist[nrem] = o; nrem++; }
                }
                add_op(x);
            }
            if (nrem > 4096) nrem = 4096;
        } else {
            int R = kmin + (int)(rnd() % (uint64_t)(kmax - kmin + 1));
            nrem = ruin((int)(rnd() % N), R, remlist, 4096);
            if (pmode == 2) {
                /* exact recreate of the ruined region; undo when it does not reach the removed size */
                if (!lns_recreate(nrem, remlist)) { undo_log(); nrej++; }
                nrem = 0;
            }
        }
        for (int j = 0; j < nrem; j++) tabu_until[remlist[j]] = curit + TABU;
        local_search();
        for (int j = 0; j < nrem; j++) { int p = remlist[j]; if (!in[p] && tight[p] == 0) add_op(p); }
        local_search();
        for (int s = 0; s < psteps; s++) {
            int x = sol[rnd() % ns];
            if (try_swap(x, 1) >= 0) { nplat++; local_search(); }
        }
        if (ns > bestn) { bestn = ns; memcpy(bestsol, sol, sizeof(int) * ns); last_imp = it; nimp++; }
        logging = 0;
        if (ns < cur) {
            long d = cur - ns, ds = bestn - ns;
            double p = 1.0 / (1.0 + (double)d * (double)ds);
            if (!ulog_overflow && rnd01() >= p) { undo_log(); nrej++; }
            else nworse++;
        }
        nlog = 0;
        if (restart > 0 && it - last_imp > restart) { rebuild(bestsol, bestn); last_imp = it; }
    }
    fprintf(stderr, "done it=%ld imp=%ld worse_acc=%ld rej=%ld plat=%ld\n", it, nimp, nworse, nrej, nplat);
    int ok = verify_set(bestsol, bestn, lc);
    save_set(outfn, bestsol, bestn);
    printf("best %d after %ld iterations (verified %s)\n", bestn, it, ok ? "ok" : "FAIL");
    return ok ? 0 : 2;
}
