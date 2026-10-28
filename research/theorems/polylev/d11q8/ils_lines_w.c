/* ils_lines.c: maximum set of pairwise disjoint totally singular lines of Q(6,q), by an ARW-style iterated local
   search (free insertions, (1,2)-swaps, forced-insertion perturbation, undo log, acceptance of worse solutions with
   probability 1/(1+d*d*)). Lines are all t.s. lines of Q(6,q) (N*(q^3+q^2+q+1)/(q+1) of them), enumerated in-program.
   Usage: ils_lines FIELD_BIN SEED SECONDS OUTPREFIX [INIT.txt]   (INIT: start set, one line per row of q+1 point ids;
   warm start added by the polylev director, 2026-10-28)
   Writes OUTPREFIX.lines (K x (q+1) int32 point ids) and OUTPREFIX.pcol (N int32: class index or -1), at each
   improvement (at most every 5 s) and at the end. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

static int q, N, Q1, T, L;
static int *ADD, *MUL, *NEG, *INV;
static uint8_t *C;
static int32_t *pid_of;
static int32_t *LP;     /* L x Q1 */
static int32_t *POL;    /* N x T  */
static int8_t *cnt;     /* L: number of owned points on the line (= #conflicting solution lines if not in sol) */
static int8_t *insol;
static int32_t *owner;  /* N: solution line through point, -1 if uncovered */
static int32_t *fl, *fpos; static int nfree;
static int32_t *sol, *spos; static int nsol;
static int32_t *best; static int nbest = 0;
static int32_t *stk; static int nstk; static uint8_t *inq;
static int32_t *logv; static int8_t *logs; static long nlog, logcap;
static int logging = 0;
static uint64_t rs = 88172645463325252ULL;

static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }

static int pid_lookup(const int *v) {
    int first = 0; while (first < 7 && v[first] == 0) first++;
    if (first == 7) return -1;
    int s = INV[v[first]];
    long code = 0, pw = 1;
    for (int k = 0; k < 7; k++) { code += MUL[s * q + v[k]] * pw; pw *= q; }
    return pid_of[code];
}

static int bform(const int *x, const int *y) {
    int s = 0;
    s = ADD[s * q + MUL[x[0] * q + y[4]]];
    s = ADD[s * q + MUL[x[4] * q + y[0]]];
    s = ADD[s * q + MUL[x[1] * q + y[5]]];
    s = ADD[s * q + MUL[x[5] * q + y[1]]];
    s = ADD[s * q + MUL[x[2] * q + y[6]]];
    s = ADD[s * q + MUL[x[6] * q + y[2]]];
    int t = MUL[x[3] * q + y[3]];
    t = ADD[t * q + t];
    s = ADD[s * q + NEG[t]];
    return s;
}

static void free_remove(int v) {
    int i = fpos[v]; if (i < 0) return;
    int last = fl[--nfree]; fl[i] = last; fpos[last] = i; fpos[v] = -1;
}
static void free_add(int v) { if (fpos[v] >= 0) return; fpos[v] = nfree; fl[nfree++] = v; }
static void push_q(int s) { if (!inq[s]) { inq[s] = 1; stk[nstk++] = s; } }
static void log_op(int v, int s) {
    if (!logging) return;
    if (nlog == logcap) { logcap = logcap ? 2 * logcap : 1 << 16; logv = realloc(logv, logcap * 4); logs = realloc(logs, logcap); }
    logv[nlog] = v; logs[nlog] = (int8_t)s; nlog++;
}

static void do_insert(int v) {
    for (int k = 0; k < Q1; k++) {
        int p = LP[v * Q1 + k];
        owner[p] = v;
        const int32_t *row = POL + (long)p * T;
        for (int j = 0; j < T; j++) {
            int w = row[j];
            if (cnt[w] == 0) free_remove(w);
            cnt[w]++;
        }
    }
    insol[v] = 1; spos[v] = nsol; sol[nsol++] = v;
    push_q(v);
    log_op(v, 1);
}

static void do_remove(int v) {
    insol[v] = 0;
    for (int k = 0; k < Q1; k++) {
        int p = LP[v * Q1 + k];
        owner[p] = -1;
        const int32_t *row = POL + (long)p * T;
        for (int j = 0; j < T; j++) {
            int w = row[j];
            cnt[w]--;
            if (cnt[w] == 0) free_add(w);
            else if (cnt[w] == 1 && w != v && !insol[w]) {
                for (int t = 0; t < Q1; t++) {
                    int r = LP[w * Q1 + t];
                    if (owner[r] >= 0) { push_q(owner[r]); break; }
                }
            }
        }
    }
    int i = spos[v]; int last = sol[--nsol]; sol[i] = last; spos[last] = i; spos[v] = -1;
    log_op(v, -1);
}

static int disjoint(int a, int b) {
    for (int i = 0; i < Q1; i++) for (int j = 0; j < Q1; j++)
        if (LP[a * Q1 + i] == LP[b * Q1 + j]) return 0;
    return 1;
}

static void local_search(void) {
    static int *cand = NULL;
    if (!cand) cand = malloc(sizeof(int) * (size_t)Q1 * T + 16);
    for (;;) {
        while (nfree > 0) do_insert(fl[rnd() % nfree]);
        if (nstk == 0) break;
        int s = stk[--nstk]; inq[s] = 0;
        if (!insol[s]) continue;
        int nc = 0;
        for (int k = 0; k < Q1; k++) {
            int x = LP[s * Q1 + k];
            const int32_t *row = POL + (long)x * T;
            for (int j = 0; j < T; j++) { int w = row[j]; if (w != s && cnt[w] == 1) cand[nc++] = w; }
        }
        int fa = -1, fb = -1;
        for (int i = 0; i < nc && fa < 0; i++)
            for (int j = i + 1; j < nc; j++)
                if (disjoint(cand[i], cand[j])) { fa = cand[i]; fb = cand[j]; break; }
        if (fa >= 0) {
            do_remove(s); do_insert(fa); do_insert(fb);
        }
    }
}

static void revert_log(void) {
    int was = logging; logging = 0;
    for (long i = nlog - 1; i >= 0; i--) {
        if (logs[i] > 0) do_remove(logv[i]); else do_insert(logv[i]);
    }
    nlog = 0; logging = was;
    nstk = 0; memset(inq, 0, L);
}

static void write_best(const char *prefix) {
    char fn[1024];
    snprintf(fn, sizeof fn, "%s.lines", prefix);
    FILE *f = fopen(fn, "wb");
    for (int i = 0; i < nbest; i++) fwrite(LP + (long)best[i] * Q1, 4, Q1, f);
    fclose(f);
    int32_t *pc = malloc(4L * N);
    for (int p = 0; p < N; p++) pc[p] = -1;
    for (int i = 0; i < nbest; i++) for (int k = 0; k < Q1; k++) pc[LP[(long)best[i] * Q1 + k]] = i;
    snprintf(fn, sizeof fn, "%s.pcol", prefix);
    f = fopen(fn, "wb"); fwrite(pc, 4, N, f); fclose(f); free(pc);
}

int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage: ils_lines FIELD_BIN SEED SECONDS OUTPREFIX\n"); return 1; }
    FILE *f = fopen(argv[1], "rb");
    int hdr[2];
    if (fread(hdr, 4, 2, f) != 2) return 1;
    q = hdr[0]; N = hdr[1]; Q1 = q + 1;
    ADD = malloc(4L * q * q); MUL = malloc(4L * q * q); NEG = malloc(4 * q); INV = malloc(4 * q);
    if (fread(ADD, 4, q * q, f) != (size_t)(q * q) || fread(MUL, 4, q * q, f) != (size_t)(q * q)) return 1;
    if (fread(NEG, 4, q, f) != (size_t)q || fread(INV, 4, q, f) != (size_t)q) return 1;
    C = malloc((size_t)N * 7);
    if (fread(C, 1, (size_t)N * 7, f) != (size_t)N * 7) return 1;
    fclose(f);
    rs ^= (uint64_t)atoll(argv[2]) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 10; i++) rnd();
    double secs = atof(argv[3]);
    const char *outp = argv[4];

    T = (q * q * q + q * q + q + 1);
    long Qn = 1; for (int k = 0; k < 7; k++) Qn *= q;
    pid_of = malloc(4L * Qn);
    for (long i = 0; i < Qn; i++) pid_of[i] = -1;
    for (int i = 0; i < N; i++) {
        long code = 0, pw = 1;
        for (int k = 0; k < 7; k++) { code += C[(long)i * 7 + k] * pw; pw *= q; }
        pid_of[code] = i;
    }
    /* enumerate t.s. lines: from pivot p, every line through p is met by an orthogonal singular point x */
    long cap = (long)N * T / Q1 + 16;
    if ((long)N * T % Q1) { fprintf(stderr, "bad counts\n"); return 1; }
    LP = malloc(4L * cap * Q1);
    int32_t *stamp = calloc(N, 4);
    L = 0;
    int v[7], w[7], pts[64];
    for (int p = 0; p < N; p++) {
        int P[7]; for (int k = 0; k < 7; k++) P[k] = C[(long)p * 7 + k];
        for (int x = 0; x < N; x++) {
            if (x == p || stamp[x] == p + 1) continue;
            int X[7]; for (int k = 0; k < 7; k++) X[k] = C[(long)x * 7 + k];
            if (bform(P, X) != 0) continue;
            pts[0] = p; pts[1] = x;
            for (int lam = 1; lam < q; lam++) {
                for (int k = 0; k < 7; k++) v[k] = ADD[P[k] * q + MUL[lam * q + X[k]]];
                int id = pid_lookup(v);
                if (id < 0) { fprintf(stderr, "point not on Q?\n"); return 1; }
                pts[1 + lam] = id;
            }
            int mn = p;
            for (int k = 0; k < Q1; k++) { stamp[pts[k]] = p + 1; if (pts[k] < mn) mn = pts[k]; }
            if (mn == p) {
                if (L >= cap) { fprintf(stderr, "cap\n"); return 1; }
                for (int k = 0; k < Q1; k++) LP[(long)L * Q1 + k] = pts[k];
                L++;
            }
        }
    }
    (void)w;
    fprintf(stderr, "q=%d N=%d lines=%d (expect %ld)\n", q, N, L, (long)N * T / Q1);
    /* point -> lines */
    POL = malloc(4L * N * T);
    int *deg = calloc(N, sizeof(int));
    for (int l = 0; l < L; l++) for (int k = 0; k < Q1; k++) {
        int p = LP[(long)l * Q1 + k];
        if (deg[p] >= T) { fprintf(stderr, "degree overflow at %d\n", p); return 1; }
        POL[(long)p * T + deg[p]++] = l;
    }
    for (int p = 0; p < N; p++) if (deg[p] != T) { fprintf(stderr, "degree %d at point %d\n", deg[p], p); return 1; }
    free(deg); free(stamp);

    cnt = calloc(L, 1); insol = calloc(L, 1);
    owner = malloc(4L * N); for (int p = 0; p < N; p++) owner[p] = -1;
    fl = malloc(4L * L); fpos = malloc(4L * L); nfree = 0;
    for (int l = 0; l < L; l++) { fpos[l] = -1; free_add(l); }
    sol = malloc(4L * L); spos = malloc(4L * L); for (int l = 0; l < L; l++) spos[l] = -1; nsol = 0;
    best = malloc(4L * L);
    stk = malloc(4L * L); inq = calloc(L, 1); nstk = 0;

    if (argc > 5) {
        FILE *fi = fopen(argv[5], "r"); int row[64], nin = 0, miss = 0;
        while (1) {
            int ok = 1;
            for (int k = 0; k < Q1; k++) if (fscanf(fi, "%d", &row[k]) != 1) { ok = 0; break; }
            if (!ok) break;
            int found = -1; const int32_t *pl = POL + (long)row[0] * T;
            for (int j = 0; j < T && found < 0; j++) {
                int l = pl[j], hit = 0;
                for (int a = 0; a < Q1; a++) for (int c = 0; c < Q1; c++) if (LP[(long)l * Q1 + a] == row[c]) hit++;
                if (hit == Q1) found = l;
            }
            if (found >= 0 && cnt[found] == 0) { do_insert(found); nin++; } else miss++;
        }
        fclose(fi);
        fprintf(stderr, "warm start: %d lines inserted, %d not usable\n", nin, miss);
    }
    local_search();
    nbest = nsol; memcpy(best, sol, 4L * nsol);
    fprintf(stderr, "initial local optimum %d\n", nsol);
    write_best(outp);
    time_t t0 = time(NULL), tlast = t0;
    long iter = 0; int bestsz = nsol;
    while (difftime(time(NULL), t0) < secs) {
        iter++;
        int oldsz = nsol;
        nlog = 0; logging = 1;
        /* perturbation: force an uncovered point's line through with 1 or 2 conflicting lines */
        int tries = 0, done = 0;
        while (!done && tries < 200) {
            tries++;
            int p = rnd() % N;
            if (owner[p] >= 0) continue;
            int wl = POL[(long)p * T + rnd() % T];
            if (cnt[wl] == 0 || cnt[wl] > 2) continue;
            int own[2], no = 0;
            for (int k = 0; k < Q1; k++) {
                int r = LP[(long)wl * Q1 + k];
                if (owner[r] >= 0) {
                    int o = owner[r], dup = 0;
                    for (int t = 0; t < no; t++) if (own[t] == o) dup = 1;
                    if (!dup) own[no++] = o;
                }
            }
            for (int t = 0; t < no; t++) do_remove(own[t]);
            do_insert(wl);
            done = 1;
        }
        local_search();
        int newsz = nsol;
        int accept;
        if (newsz >= oldsz) accept = 1;
        else {
            int d = oldsz - newsz, ds = bestsz - newsz;
            accept = ((double)(rnd() % 1000000) / 1e6) < 1.0 / (1.0 + (double)d * ds);
        }
        if (!accept) revert_log();
        logging = 0; nlog = 0;
        if (nsol > bestsz) {
            bestsz = nsol; nbest = nsol; memcpy(best, sol, 4L * nsol);
            fprintf(stderr, "iter %ld: new best %d (t=%.0fs)\n", iter, bestsz, difftime(time(NULL), t0));
            if (difftime(time(NULL), tlast) >= 5) { write_best(outp); tlast = time(NULL); }
        }
        if (iter % 200000 == 0) fprintf(stderr, "iter %ld cur %d best %d\n", iter, nsol, bestsz);
    }
    write_best(outp);
    fprintf(stderr, "done: %ld iterations, best %d\n", iter, bestsz);
    printf("%d\n", bestsz);
    return 0;
}
