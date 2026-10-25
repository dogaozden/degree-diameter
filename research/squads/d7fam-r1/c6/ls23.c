/* ls23.c: local search for a large set S of pairwise non-concurrent lines of H(q)
   (equivalently: every point lies on at most one line of S).  Elements = lines, cells = points.
   Moves on S:
     (1,2)-swap: drop x, add two non-concurrent lines whose only conflict in S is x.
     (2,3)-swap: drop x1 and y (linked by a 2-tight line), add three pairwise non-concurrent lines whose
                 conflicts in S all lie in {x1,y}.
     (1,1)-plateau walk: drop a random chosen x, add a random 1-tight line f (only conflict x);
                 x may not come back for TABU iterations.
     Perturbation: with probability PFORCE% force-insert a random 2-tight line (its 2 conflicts are dropped),
                 otherwise a plateau step.  Local search runs from a queue of chosen lines whose neighbourhood
                 gained a line with tight <= 2 (touch_removed) or that were just added.
     The best set is kept; the walk is restored to it when it falls more than SLACK below.
   usage: ls23 HEXBIN START|- SEED SECONDS OUT.txt [TABU=20] [PFORCE=3] [SLACK=2]
   OUT is rewritten at each improvement (one line id per line). */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>

static int q, NP, NL, Q1;
static int *LP, *PL;            /* line -> its points (Q1 each), point -> its lines (Q1 each) */
static int *owner, *tight;      /* owner[point] = chosen line through it or -1; tight[line] = #chosen lines meeting it */
static char *in, *qin;
static int *sol, *pos, ns;
static int *queue, nq;
static long *tabu;
static int *bestsol, nbest;
static uint64_t rs;
static const char *outfn;
static long long nm12 = 0, nm23 = 0, nplat = 0, nforce = 0, nrestore = 0, npairs = 0, npoolsum = 0, npoolmax = 0, nB2 = 0;

static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline int rndn(int n) { return (int)(rnd() % (uint64_t)n); }
static inline void push(int x) { if (!qin[x]) { qin[x] = 1; queue[nq++] = x; } }

static void touch_removed(int c);
static void add_line(int l) {
    in[l] = 1; pos[l] = ns; sol[ns++] = l;
    for (int i = 0; i < Q1; i++) {
        int p = LP[l * Q1 + i]; owner[p] = l;
        for (int j = 0; j < Q1; j++) { int f = PL[p * Q1 + j]; if (f != l) tight[f]++; }
    }
    push(l);
}
static void rem_line(int l) {
    in[l] = 0; int p0 = pos[l]; int last = sol[--ns]; sol[p0] = last; pos[last] = p0;
    for (int i = 0; i < Q1; i++) {
        int p = LP[l * Q1 + i]; owner[p] = -1;
        for (int j = 0; j < Q1; j++) { int f = PL[p * Q1 + j]; if (f != l) tight[f]--; }
    }
    touch_removed(l);
}
static int meets(int a, int b) {
    for (int i = 0; i < Q1; i++) {
        int p = LP[a * Q1 + i];
        for (int j = 0; j < Q1; j++) if (LP[b * Q1 + j] == p) return 1;
    }
    return 0;
}
/* after c left the chosen set: a line g meeting c that now has tight <= 2 may be a new candidate for every
   chosen line x meeting g, so queue those x */
static void touch_removed(int c) {
    for (int i = 0; i < Q1; i++) {
        int p = LP[c * Q1 + i];
        for (int j = 0; j < Q1; j++) {
            int g = PL[p * Q1 + j];
            if (g == c || in[g] || tight[g] > 2) continue;
            for (int k = 0; k < Q1; k++) {
                int r = LP[g * Q1 + k];
                for (int t = 0; t < Q1; t++) { int x = PL[r * Q1 + t]; if (in[x]) push(x); }
            }
        }
    }
}
static void fill_near(int l) {  /* add free lines on the points of l */
    for (int i = 0; i < Q1; i++) {
        int p = LP[l * Q1 + i];
        for (int j = 0; j < Q1; j++) { int f = PL[p * Q1 + j]; if (!in[f] && tight[f] == 0) add_line(f); }
    }
}

#define MAXP 128
static int A1[MAXP], nA1, Bf[MAXP], By[MAXP], nB, pool[MAXP];

static int find_triple(const int *P, int n, int *out) {
    for (int i = 0; i < n; i++) for (int j = i + 1; j < n; j++) {
        if (meets(P[i], P[j])) continue;
        for (int k = j + 1; k < n; k++)
            if (!meets(P[i], P[k]) && !meets(P[j], P[k])) { out[0] = P[i]; out[1] = P[j]; out[2] = P[k]; return 1; }
    }
    return 0;
}
static void shuffle(int *a, int n) { for (int i = n - 1; i > 0; i--) { int j = rndn(i + 1), t = a[i]; a[i] = a[j]; a[j] = t; } }

/* improving (1,2) or (2,3) move with chosen x1 removed; returns 1 if applied */
static int try_improve(int x1) {
    nA1 = 0; nB = 0;
    for (int i = 0; i < Q1; i++) {
        int p = LP[x1 * Q1 + i];
        for (int j = 0; j < Q1; j++) {
            int f = PL[p * Q1 + j];
            if (f == x1 || in[f]) continue;
            if (tight[f] == 1) { if (nA1 < MAXP) A1[nA1++] = f; }
            else if (tight[f] == 2 && nB < MAXP) {
                int y = -1;
                for (int k = 0; k < Q1; k++) { int o = owner[LP[f * Q1 + k]]; if (o >= 0 && o != x1) { y = o; break; } }
                Bf[nB] = f; By[nB] = y; nB++;
            }
        }
    }
    if (nA1 == 0 && nB == 0) return 0;
    nB2 += nB;
    shuffle(A1, nA1);
    for (int a = 0; a < nA1; a++) for (int b = a + 1; b < nA1; b++) if (!meets(A1[a], A1[b])) {
        int u = A1[a], v = A1[b];
        rem_line(x1); add_line(u); add_line(v);
        fill_near(x1);
        nm12++;
        return 1;
    }
    int ys[MAXP], ny = 0;
    for (int k = 0; k < nB; k++) {
        int y = By[k]; if (y < 0) continue;
        int seen = 0;
        for (int t = 0; t < ny; t++) if (ys[t] == y) { seen = 1; break; }
        if (seen) continue;
        ys[ny++] = y;
        int np = 0;
        for (int a = 0; a < nA1 && np < 60; a++) pool[np++] = A1[a];
        for (int t = 0; t < nB && np < 60; t++) if (By[t] == y) pool[np++] = Bf[t];
        for (int i = 0; i < Q1; i++) {
            int p = LP[y * Q1 + i];
            for (int j = 0; j < Q1; j++) {
                int h = PL[p * Q1 + j];
                if (h != y && !in[h] && tight[h] == 1 && np < 60) pool[np++] = h;
            }
        }
        int tr[3];
        npairs++; npoolsum += np; if (np > npoolmax) npoolmax = np;
        if (np >= 3 && find_triple(pool, np, tr)) {
            rem_line(x1); rem_line(y);
            add_line(tr[0]); add_line(tr[1]); add_line(tr[2]);
            fill_near(x1); fill_near(y);
            nm23++;
            return 1;
        }
    }
    return 0;
}

static void run_queue(void) {
    while (nq) {
        int x = queue[--nq]; qin[x] = 0;
        if (in[x]) try_improve(x);
    }
}

/* (1,1) plateau step: drop a random chosen x for a random non-tabu 1-tight line through a point of x */
static int plateau_step(long it, int TT) {
    for (int tries = 0; tries < 30; tries++) {
        int x = sol[rndn(ns)];
        int off = rndn(Q1);
        for (int i = 0; i < Q1; i++) {
            int p = LP[x * Q1 + ((i + off) % Q1)];
            int cnt = 0, pick = -1;
            for (int j = 0; j < Q1; j++) {
                int f = PL[p * Q1 + j];
                if (f == x || in[f] || tight[f] != 1 || tabu[f] > it) continue;
                cnt++; if (rndn(cnt) == 0) pick = f;
            }
            if (pick >= 0) {
                rem_line(x); tabu[x] = it + TT;
                add_line(pick);
                fill_near(x);
                return 1;
            }
        }
    }
    return 0;
}

/* force-insert a random non-chosen 2-tight line, dropping its two conflicts */
static void forced_insert(long it, int TT) {
    int v = -1;
    for (int tries = 0; tries < 200000; tries++) {
        int c = rndn(NL);
        if (!in[c] && tight[c] == 2 && tabu[c] <= it) { v = c; break; }
    }
    if (v < 0) return;
    int rm[64], k = 0;
    for (int i = 0; i < Q1; i++) { int o = owner[LP[v * Q1 + i]]; if (o >= 0) rm[k++] = o; }
    for (int t = 0; t < k; t++) { rem_line(rm[t]); tabu[rm[t]] = it + TT; }
    add_line(v);
    for (int t = 0; t < k; t++) fill_near(rm[t]);
}

static void save_best(void) {
    nbest = ns; memcpy(bestsol, sol, sizeof(int) * ns);
    FILE *o = fopen(outfn, "w");
    if (o) { for (int i = 0; i < nbest; i++) fprintf(o, "%d\n", bestsol[i]); fclose(o); }
}
static void restore_best(void) {
    while (ns) rem_line(sol[ns - 1]);
    for (int i = 0; i < nbest; i++) add_line(bestsol[i]);
    nrestore++;
}
static int verify_points(const int *S, int n) {  /* no point on two chosen lines */
    char *mk = calloc(NP, 1); int ok = 1;
    for (int i = 0; i < n && ok; i++) for (int j = 0; j < Q1; j++) {
        int p = LP[S[i] * Q1 + j]; if (mk[p]) { ok = 0; break; } mk[p] = 1;
    }
    free(mk); return ok;
}
static double now(void) { struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts); return ts.tv_sec + 1e-9 * ts.tv_nsec; }

int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: ls23 HEXBIN START|- SEED SECONDS OUT.txt [TABU=20] [PFORCE=3] [SLACK=2]\n"); return 1; }
    FILE *f = fopen(argv[1], "rb"); if (!f) return 1;
    int hdr[3]; if (fread(hdr, 4, 3, f) != 3) return 1;
    q = hdr[0]; NP = hdr[1]; NL = hdr[2]; Q1 = q + 1;
    LP = malloc(sizeof(int) * (size_t)NL * Q1);
    if (fread(LP, 4, (size_t)NL * Q1, f) != (size_t)NL * Q1) return 1;
    fclose(f);
    PL = malloc(sizeof(int) * (size_t)NP * Q1); int *cnt = calloc(NP, sizeof(int));
    for (int l = 0; l < NL; l++) for (int i = 0; i < Q1; i++) {
        int p = LP[l * Q1 + i];
        if (cnt[p] >= Q1) { fprintf(stderr, "point degree exceeds q+1\n"); return 1; }
        PL[p * Q1 + cnt[p]++] = l;
    }
    free(cnt);

    uint64_t seed = strtoull(argv[3], 0, 10);
    rs = 0x9E3779B97F4A7C15ULL ^ (seed * 0x2545F4914F6CDD1DULL); if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();
    double secs = atof(argv[4]); outfn = argv[5];
    int TT = argc > 6 ? atoi(argv[6]) : 20;
    int PF = argc > 7 ? atoi(argv[7]) : 3;
    int SLACK = argc > 8 ? atoi(argv[8]) : 2;

    owner = malloc(sizeof(int) * NP); for (int i = 0; i < NP; i++) owner[i] = -1;
    tight = calloc(NL, sizeof(int)); in = calloc(NL, 1); qin = calloc(NL, 1);
    sol = malloc(sizeof(int) * NL); pos = malloc(sizeof(int) * NL); queue = malloc(sizeof(int) * NL);
    tabu = calloc(NL, sizeof(long)); bestsol = malloc(sizeof(int) * NL);
    ns = 0; nq = 0;
    if (strcmp(argv[2], "-")) {
        FILE *g = fopen(argv[2], "r"); int e;
        while (fscanf(g, "%d", &e) == 1) {
            if (!in[e] && tight[e] == 0) add_line(e); else fprintf(stderr, "start conflict %d skipped\n", e);
        }
        fclose(g);
    }
    int *perm = malloc(sizeof(int) * NL); for (int i = 0; i < NL; i++) perm[i] = i;
    for (int i = NL - 1; i > 0; i--) { int j = rndn(i + 1), t = perm[i]; perm[i] = perm[j]; perm[j] = t; }
    for (int i = 0; i < NL; i++) if (!in[perm[i]] && tight[perm[i]] == 0) add_line(perm[i]);
    fprintf(stderr, "start %d (maximal)\n", ns);
    run_queue();
    fprintf(stderr, "after LS %d  m12=%lld m23=%lld\n", ns, nm12, nm23);
    save_best();

    double t0 = now(), lastp = t0; long it = 0;
    while (1) {
        it++;
        if ((it & 63) == 0) {
            double el = now() - t0;
            if (el > secs) break;
            if (now() - lastp > 30) {
                lastp = now();
                fprintf(stderr, "t=%.0f it=%ld cur=%d best=%d plat=%lld force=%lld m12=%lld m23=%lld restore=%lld\n",
                        el, it, ns, nbest, nplat, nforce, nm12, nm23, nrestore);
            }
        }
        if (rndn(100) < PF) { forced_insert(it, TT); nforce++; }
        else if (plateau_step(it, TT)) nplat++;
        else { forced_insert(it, TT); nforce++; }
        run_queue();
        if (ns > nbest) { save_best(); fprintf(stderr, "improved best %d at it=%ld\n", nbest, it); }
        else if (ns < nbest - SLACK) restore_best();
    }
    printf("pairs %lld avgpool %.2f maxpool %lld avgB %.2f\n", npairs, npairs ? (double)npoolsum/npairs : 0.0, npoolmax, (double)nB2/(nplat+nforce+1));
    printf("best %d after %ld iterations, plat=%lld force=%lld m12=%lld m23=%lld restore=%lld, verify_points=%d\n",
           nbest, it, nplat, nforce, nm12, nm23, nrestore, verify_points(bestsol, nbest));
    return 0;
}
