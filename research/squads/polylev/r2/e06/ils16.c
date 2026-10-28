/* e06: large set of pairwise non-collinear points of H(16).
 * Points and lines of the hexagon come from research/theorems/polylev/hex/hex_q16.bin.
 * Two points are collinear iff they share a line. A point set is valid iff every line
 * carries at most one chosen point. tight[r] = number of occupied lines through r
 * (for a non-chosen r this equals the number of chosen points collinear with r).
 * Search: greedy in random order, then ARW-style iterated local search with (1,2)-swaps
 * (remove x, insert two non-collinear points whose only chosen neighbour is x) and forced
 * insertions as perturbation. Stops on wall-clock time; writes the best set (text, first
 * line = count) whenever it improves (throttled to every 2 s).
 * usage: ils16 HEX OUT SECONDS SEED [INIT_TXT]
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define K 17
static int N, L;
static int *LN;     /* L*K  points on each line */
static int *PL;     /* N*K  lines through each point */
static int *occ;    /* L    chosen point on line, or -1 */
static int *tight;  /* N    number of occupied lines through the point */
static char *sol;   /* N    chosen flag */
static char *inq;   /* N    queue flag */
static int *qu;     /* N    stack */
static long qn = 0;
static int nsol = 0;
static int *lg;
static long lglen = 0, lgcap = 1L << 24;
static int logging = 1, overflow = 0;
static int *rl;
static int cand[K * K];
static uint64_t rs = 0x9E3779B97F4A7C15ULL;

static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }

static void push(int p) { if (!inq[p]) { inq[p] = 1; qu[qn++] = p; } }

static void ins(int p) {
    sol[p] = 1; nsol++;
    const int *pl = PL + (size_t)p * K;
    for (int i = 0; i < K; i++) {
        int l = pl[i]; occ[l] = p;
        const int *ln = LN + (size_t)l * K;
        for (int j = 0; j < K; j++) tight[ln[j]]++;
    }
    if (logging) { if (lglen < lgcap) lg[lglen++] = p + 1; else overflow = 1; }
}

static void rem(int p) {
    sol[p] = 0; nsol--;
    const int *pl = PL + (size_t)p * K;
    for (int i = 0; i < K; i++) {
        int l = pl[i]; occ[l] = -1;
        const int *ln = LN + (size_t)l * K;
        for (int j = 0; j < K; j++) tight[ln[j]]--;
    }
    if (logging) { if (lglen < lgcap) lg[lglen++] = -(p + 1); else overflow = 1; }
}

static int collinear(int a, int b) {
    const int *pa = PL + (size_t)a * K, *pb = PL + (size_t)b * K;
    for (int i = 0; i < K; i++) for (int j = 0; j < K; j++) if (pa[i] == pb[j]) return 1;
    return 0;
}

/* chosen point collinear with the 1-tight point r */
static int occupant_of(int r) {
    const int *pl = PL + (size_t)r * K;
    for (int i = 0; i < K; i++) if (occ[pl[i]] >= 0) return occ[pl[i]];
    return -1;
}

/* try a (1,2)-swap at chosen point x */
static int improve_from(int x) {
    int nc = 0;
    const int *px = PL + (size_t)x * K;
    for (int i = 0; i < K; i++) {
        const int *ln = LN + (size_t)px[i] * K;
        for (int j = 0; j < K; j++) { int r = ln[j]; if (r != x && tight[r] == 1) cand[nc++] = r; }
    }
    if (nc < 2) return 0;
    int A = -1, B = -1;
    for (int a = 0; a < nc && A < 0; a++)
        for (int b = a + 1; b < nc; b++)
            if (!collinear(cand[a], cand[b])) { A = cand[a]; B = cand[b]; break; }
    if (A < 0) return 0;
    rem(x); ins(A); ins(B);
    for (int i = 0; i < K; i++) {
        const int *ln = LN + (size_t)px[i] * K;
        for (int j = 0; j < K; j++) {
            int r = ln[j];
            if (r != x && !sol[r] && tight[r] == 0) { ins(r); push(r); }
        }
    }
    push(A); push(B);
    for (int i = 0; i < K; i++) {
        const int *ln = LN + (size_t)px[i] * K;
        for (int j = 0; j < K; j++) {
            int r = ln[j];
            if (r != x && !sol[r] && tight[r] == 1) push(occupant_of(r));
        }
    }
    return 1;
}

static void run_ls(void) {
    while (qn > 0) {
        int x = qu[--qn]; inq[x] = 0;
        if (sol[x]) improve_from(x);
    }
}

/* force a random low-tightness point in, drop its chosen neighbours, refill greedily */
static void perturb(void) {
    int v;
    for (int t = 0;; t++) {
        v = (int)(rnd() % (uint64_t)N);
        if (sol[v]) continue;
        if (tight[v] <= 2 || t >= 100) break;
    }
    const int *pv = PL + (size_t)v * K;
    int nr = 0;
    for (int i = 0; i < K; i++) {
        int y = occ[pv[i]];
        if (y >= 0) { rem(y); rl[nr++] = y; }
    }
    ins(v); push(v);
    for (int k = 0; k < nr; k++) {
        const int *py = PL + (size_t)rl[k] * K;
        for (int i = 0; i < K; i++) {
            const int *ln = LN + (size_t)py[i] * K;
            for (int j = 0; j < K; j++) {
                int r = ln[j];
                if (!sol[r] && tight[r] == 0) { ins(r); push(r); }
            }
        }
    }
    for (int k = 0; k < nr; k++) {
        const int *py = PL + (size_t)rl[k] * K;
        for (int i = 0; i < K; i++) {
            const int *ln = LN + (size_t)py[i] * K;
            for (int j = 0; j < K; j++) {
                int r = ln[j];
                if (!sol[r] && tight[r] == 1) push(occupant_of(r));
            }
        }
    }
}

static void undo(void) {
    logging = 0;
    for (long k = lglen - 1; k >= 0; k--) {
        int e = lg[k];
        if (e > 0) rem(e - 1); else ins(-e - 1);
    }
    logging = 1; lglen = 0;
}

/* check: every line has <= 1 chosen point; tight recomputed from scratch */
static int verify(void) {
    int bad = 0;
    int *t2 = calloc(N, sizeof(int));
    for (int l = 0; l < L; l++) {
        int c = 0;
        for (int j = 0; j < K; j++) c += sol[LN[(size_t)l * K + j]];
        if (c > 1) bad++;
        if (c > 0) for (int j = 0; j < K; j++) t2[LN[(size_t)l * K + j]]++;
    }
    for (int p = 0; p < N; p++) if (t2[p] != tight[p]) { bad++; break; }
    free(t2);
    return bad;
}

static void save(const char *out, int best) {
    char tmp[4096];
    snprintf(tmp, sizeof tmp, "%s.tmp", out);
    FILE *f = fopen(tmp, "w");
    if (!f) { perror("save"); return; }
    int cnt = 0;
    for (int p = 0; p < N; p++) cnt += sol[p];
    fprintf(f, "%d\n", cnt);
    for (int p = 0; p < N; p++) if (sol[p]) fprintf(f, "%d\n", p);
    fclose(f);
    rename(tmp, out);
    fprintf(stderr, "saved %d (best %d)\n", cnt, best);
}

int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage: ils16 HEX OUT SECONDS SEED [INIT]\n"); return 1; }
    const char *hex = argv[1], *out = argv[2];
    double secs = atof(argv[3]);
    rs ^= (uint64_t)atoll(argv[4]) * 0x2545F4914F6CDD1DULL + 1;
    for (int i = 0; i < 10; i++) rnd();

    FILE *f = fopen(hex, "rb");
    if (!f) { perror("hex"); return 1; }
    int hdr[3];
    if (fread(hdr, 4, 3, f) != 3) return 1;
    int q = hdr[0]; N = hdr[1]; L = hdr[2];
    if (q + 1 != K) { fprintf(stderr, "q=%d not supported\n", q); return 1; }
    LN = malloc((size_t)L * K * sizeof(int));
    if (fread(LN, sizeof(int), (size_t)L * K, f) != (size_t)L * K) { fprintf(stderr, "short read\n"); return 1; }
    fclose(f);

    PL = malloc((size_t)N * K * sizeof(int));
    int *cnt = calloc(N, sizeof(int));
    for (int l = 0; l < L; l++)
        for (int j = 0; j < K; j++) {
            int p = LN[(size_t)l * K + j];
            if (cnt[p] >= K) { fprintf(stderr, "point %d on too many lines\n", p); return 1; }
            PL[(size_t)p * K + cnt[p]++] = l;
        }
    for (int p = 0; p < N; p++) if (cnt[p] != K) { fprintf(stderr, "point %d has %d lines\n", p, cnt[p]); return 1; }
    free(cnt);

    occ = malloc((size_t)L * sizeof(int));
    for (int l = 0; l < L; l++) occ[l] = -1;
    tight = calloc(N, sizeof(int));
    sol = calloc(N, 1);
    inq = calloc(N, 1);
    qu = malloc((size_t)N * sizeof(int));
    lg = malloc((size_t)lgcap * sizeof(int));
    rl = malloc(K * sizeof(int));
    fprintf(stderr, "loaded q=%d N=%d L=%d\n", q, N, L);

    if (argc >= 6) {
        FILE *g = fopen(argv[5], "r");
        int m = 0, id;
        if (g && fscanf(g, "%d", &m) == 1) {
            int added = 0;
            while (fscanf(g, "%d", &id) == 1)
                if (id >= 0 && id < N && !sol[id] && tight[id] == 0) { ins(id); added++; }
            fprintf(stderr, "init: %d points read, %d inserted\n", m, added);
        }
        if (g) fclose(g);
    }

    int *perm = malloc((size_t)N * sizeof(int));
    for (int p = 0; p < N; p++) perm[p] = p;
    for (int p = N - 1; p > 0; p--) { int j = (int)(rnd() % (uint64_t)(p + 1)); int t = perm[p]; perm[p] = perm[j]; perm[j] = t; }
    logging = 0;
    for (int k = 0; k < N; k++) { int p = perm[k]; if (!sol[p] && tight[p] == 0) ins(p); }
    logging = 1;
    for (int p = 0; p < N; p++) if (sol[p]) push(p);
    run_ls();
    int best = nsol, cur = nsol;
    fprintf(stderr, "after greedy+LS: %d (verify bad=%d)\n", nsol, verify());
    save(out, best);

    double t0 = now(), tend = t0 + secs, tlast = t0, tsave = t0;
    int pending = 0;   /* best improved but not yet saved; then the current state has size best */
    long iter = 0;
    while (1) {
        if (now() >= tend) break;
        logging = 1; lglen = 0; overflow = 0;
        perturb();
        run_ls();
        if (nsol > best) { best = nsol; pending = 1; }
        if (pending && now() - tsave > 2.0) { save(out, best); tsave = now(); pending = 0; }
        int accept;
        if (nsol >= cur || overflow) accept = 1;
        else if (pending) accept = 0;          /* never leave an unsaved best */
        else {
            /* ARW acceptance: a worse solution is kept with probability 1/(1 + d*d*) */
            int d = cur - nsol, ds = best - nsol;
            accept = (rnd() % (uint64_t)(1 + (uint64_t)d * (uint64_t)(ds > 0 ? ds : 1))) == 0;
        }
        if (accept) cur = nsol; else undo();
        iter++;
        if (now() - tlast > 15.0) {
            fprintf(stderr, "t=%.0fs iter=%ld cur=%d best=%d\n", now() - t0, iter, cur, best);
            tlast = now();
        }
    }
    if (pending) { save(out, best); pending = 0; }
    fprintf(stderr, "final: iter=%ld cur=%d best=%d verify_bad_on_current=%d\n", iter, cur, best, verify());
    return 0;
}
