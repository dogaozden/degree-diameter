/* tsorbq.c: orbit quotient of the totally singular lines of Q(6,q) (all of them, hexagon lines and ideal lines) under
   a cyclic collineation group of H(q) given by the point permutation of a generator (int32 per point).
   An orbit is admissible when its lines are pairwise disjoint; two admissible orbits are adjacent when a line of one
   meets a line of the other. An independent set of the quotient is a set of pairwise disjoint t.s. lines (point
   classes for Corollary 5.2 of POLYGON_LEVELS.md).
   Enumeration of the lines and the field file format are those of squad card r2/e09 (ils_lines.c).
   polylev job (Opus), 2026-10-28.
   Usage: tsorbq FIELD_BIN PPERM OUTPREFIX [MINSIZE]   (orbits with fewer than MINSIZE lines are left out)
   Writes OUTPREFIX_n.bin, _off.bin, _nb.bin (CSR, for mis3/mcq), OUTPREFIX.reps (n x (q+1) int32: one line of each
   admissible orbit) and OUTPREFIX.osz (n int32: orbit sizes). */

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


int main(int argc, char **argv) {
    if (argc < 4) { fprintf(stderr, "usage: tsorbq FIELD_BIN PPERM OUTPREFIX\n"); return 1; }
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
    int32_t *pm = malloc(4L * N);
    f = fopen(argv[2], "rb"); if (!f || fread(pm, 4, N, f) != (size_t)N) { fprintf(stderr, "pperm\n"); return 1; } fclose(f);
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


    /* line permutation */
    int32_t *lm = malloc(4L * L);
    int32_t *mark = calloc(N, 4);
    for (int l = 0; l < L; l++) {
        int a = pm[LP[(long)l * Q1]], b = pm[LP[(long)l * Q1 + 1]];
        const int32_t *row = POL + (long)a * T; int img = -1;
        for (int j = 0; j < T && img < 0; j++) {
            const int32_t *pp = LP + (long)row[j] * Q1;
            for (int k = 0; k < Q1; k++) if (pp[k] == b) { img = row[j]; break; }
        }
        if (img < 0) { fprintf(stderr, "image of line %d is not a t.s. line\n", l); return 1; }
        lm[l] = img;
    }
    /* orbits */
    int32_t *orb = malloc(4L * L); for (int l = 0; l < L; l++) orb[l] = -1;
    int no = 0; int32_t *rep = malloc(4L * L), *osz = calloc(L, 4);
    for (int s = 0; s < L; s++) {
        if (orb[s] >= 0) continue;
        int x = s; rep[no] = s;
        while (orb[x] < 0) { orb[x] = no; osz[no]++; x = lm[x]; }
        no++;
    }
    /* admissibility: lines of an orbit pairwise disjoint */
    int minsize = argc > 4 ? atoi(argv[4]) : 1;
    int32_t *qid = malloc(4L * no); int n = 0; int stampv = 0;
    for (int i = 0; i < N; i++) mark[i] = 0;
    for (int o = 0; o < no; o++) {
        stampv++; int ok = 1; int x = rep[o];
        for (int t = 0; t < osz[o] && ok; t++) {
            for (int k = 0; k < Q1; k++) { int p = LP[(long)x * Q1 + k]; if (mark[p] == stampv) { ok = 0; break; } mark[p] = stampv; }
            x = lm[x];
        }
        qid[o] = (ok && osz[o] >= minsize) ? n++ : -1;
    }
    fprintf(stderr, "%d orbits, %d admissible\n", no, n);
    /* adjacency */
    int64_t *off = malloc(8L * (n + 1)); long cap2 = 1L << 24; int32_t *nb = malloc(4L * cap2); long m = 0;
    int32_t *seen = calloc(n, 4); int sv = 0; int32_t *qrep = malloc(4L * n), *qsz = malloc(4L * n);
    for (int o = 0; o < no; o++) {
        int v = qid[o]; if (v < 0) continue;
        qrep[v] = rep[o]; qsz[v] = osz[o];
        off[v] = m; sv++; seen[v] = sv;
        int a = rep[o];
        for (int k = 0; k < Q1; k++) {
            const int32_t *row = POL + (long)LP[(long)a * Q1 + k] * T;
            for (int j = 0; j < T; j++) {
                int u = qid[orb[row[j]]];
                if (u < 0 || seen[u] == sv) continue;
                seen[u] = sv;
                if (m == cap2) { cap2 *= 2; nb = realloc(nb, 4L * cap2); }
                nb[m++] = u;
            }
        }
    }
    off[n] = m;
    char fn[1024]; int32_t nn = n;
    snprintf(fn, sizeof fn, "%s_n.bin", argv[3]); f = fopen(fn, "wb"); fwrite(&nn, 4, 1, f); fclose(f);
    int32_t *off32 = malloc(4L * (n + 1));
    for (int v = 0; v <= n; v++) { if (off[v] > 2147483647L) { fprintf(stderr, "too many edges\n"); return 1; } off32[v] = (int32_t)off[v]; }
    snprintf(fn, sizeof fn, "%s_off.bin", argv[3]); f = fopen(fn, "wb"); fwrite(off32, 4, n + 1, f); fclose(f);
    snprintf(fn, sizeof fn, "%s_nb.bin", argv[3]); f = fopen(fn, "wb"); fwrite(nb, 4, m, f); fclose(f);
    snprintf(fn, sizeof fn, "%s.reps", argv[3]); f = fopen(fn, "wb");
    for (int v = 0; v < n; v++) fwrite(LP + (long)qrep[v] * Q1, 4, Q1, f);
    fclose(f);
    snprintf(fn, sizeof fn, "%s.osz", argv[3]); f = fopen(fn, "wb"); fwrite(qsz, 4, n, f); fclose(f);
    fprintf(stderr, "quotient: %d vertices, %ld adjacency entries (mean degree %.1f)\n", n, m, (double)m / n);
    return 0;
}
