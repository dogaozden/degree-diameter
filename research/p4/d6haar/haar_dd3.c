/* Annealing search for Haar graphs of diameter <= D, for any D >= 3 (copied in spirit from research/d5/haar_search3.c).
 *
 * Haar graph H(G, S): vertices G x {A, B}, edges (g, A) ~ (s g, B) for s in S, |S| = d. Right multiplication is an
 * automorphism that is transitive on each side, so only distances from (e, A) and (e, B) matter. With T = S^-1 S and
 * U = S S^-1 (both closed under inverses, both contain e):
 *   D = 2k   : diameter <= D  iff  S T^(k-1) = G               (one condition; it implies T^k = G = U^k)
 *   D = 2k+1 : diameter <= D  iff  T^k = G and U^k = G         (the odd condition S T^k = G follows)
 * Cost = number of elements of G missed by these sets (summed over the two sides when D is odd).
 *
 * Group: G = G0 x Z_c, G0 read from a multiplication table (groups.py format: N0, then N0 rows; identity = 0).
 * Element index x = g * c + z. Every product set is computed with dedup (stamp array), so one evaluation costs about
 * sum_j |X_j| |T| multiplications, where X_j are the partial products (e.g. D = 7: |T| + |T^2| |T| per side).
 *
 * haar_dd3 = haar_dd2 plus targeted candidates: with probability PT (default 0.5) a candidate x is chosen so that
 * one missed element g becomes covered by a word using a new pair (g = u t or t u, u from the current T^(k-1),
 * t a pair of x with a random s_j; even D: g = x w, w in T^(k-1)).
 * haar_dd2: for odd D, each step picks one position i and scores K replacements x for S_i. With S' = S minus S_i,
 * T' = S'^-1 S' and N = the new pairs (x^-1 s_j, s_j^-1 x not in T'), every word of T^k with a letter from N is in
 * T^(j-1) N T'^(k-j) for j = its last N position. T'^m (m < k) and T'^k are computed once per step; per candidate
 * only the words with an N letter are formed (about 0.6 of the full count at D = 7). Even D: as in haar_dd.
 *
 * Usage: haar_dd3 D d table c seed seconds [outfile|-] [K] [PT]
 *   c is either a number (second factor Z_c) or a second table file (G = G0 x G1, x = g * |G1| + z).
 *        haar_dd check D d table c seed        (cost vs. brute-force BFS on the graph, random S)
 *        haar_dd eval D d table c x1 .. xd     (cost and BFS diameter of a given S)
 * On cost 0 writes: "D d N c table" then d lines "x" (x = element index in G0 x Z_c).
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>

#define MAXD 24

static int D, d, N, N0, C;
static uint16_t *MT0;   /* MT0[g*N0 + h] */
static int *IT0;
static int *bg, *bz;    /* x -> (g, z) */
static int *stamp, cur = 1;
static int *bufA, *bufB;
static int S[MAXD], best[MAXD];
static long long evals;
static inline int used(int x, int n);

static uint16_t *MT1;   /* second factor G1 (Z_c or a table), order C: MT1[z*C + w] */
static int *IT1;
static inline int mul(int x, int y) {
    return MT0[bg[x] * N0 + bg[y]] * C + MT1[bz[x] * C + bz[y]];
}
static inline int inv(int x) {
    return IT0[bg[x]] * C + IT1[bz[x]];
}

static unsigned long long rs;
static inline unsigned long long rnd(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs;
}
static double now(void) {
    struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec;
}

/* out = distinct elements of X * Y (|X| = nx, |Y| = ny); returns the count */
static int prodset(const int *X, int nx, const int *Y, int ny, int *out) {
    int n = 0;
    cur++;
    for (int i = 0; i < nx; i++)
        for (int j = 0; j < ny; j++) {
            int t = mul(X[i], Y[j]);
            if (stamp[t] != cur) { stamp[t] = cur; out[n++] = t; }
        }
    return n;
}

/* T = S^-1 S (side 0) or S S^-1 (side 1), deduplicated */
static int pairset(const int *X, int side, int *out) {
    int n = 0;
    cur++;
    for (int i = 0; i < d; i++)
        for (int j = 0; j < d; j++) {
            int t = side == 0 ? mul(inv(X[i]), X[j]) : mul(X[i], inv(X[j]));
            if (stamp[t] != cur) { stamp[t] = cur; out[n++] = t; }
        }
    return n;
}

/* number of elements of T^k (k >= 1) */
static int power_size(const int *T, int nt, int k) {
    int n = nt;
    int *A = bufA, *B = bufB;
    memcpy(A, T, sizeof(int) * nt);
    for (int j = 1; j < k; j++) {
        n = prodset(A, n, T, nt, B);
        int *t = A; A = B; B = t;
        if (n == N) break;
    }
    return n;
}

static int cost(const int *X) {
    static int T[MAXD * MAXD];
    if (D % 2 == 0) {
        int k = D / 2;
        int nt = pairset(X, 0, T);
        if (k == 1) return N - d;
        /* S T^(k-1): compute T^(k-1) into bufA, then S * that */
        int n = nt;
        int *A = bufA, *B = bufB;
        memcpy(A, T, sizeof(int) * nt);
        for (int j = 1; j < k - 1; j++) {
            n = prodset(A, n, T, nt, B);
            int *t = A; A = B; B = t;
        }
        n = prodset(X, d, A, n, B);
        return N - n;
    } else {
        int k = D / 2, c = 0;
        for (int side = 0; side < 2; side++) {
            int nt = pairset(X, side, T);
            c += N - power_size(T, nt, k);
        }
        return c;
    }
}


/* ---- odd D, shared position i: per-step precompute and per-candidate scoring ---- */
#define MAXK 8
static int *Pset[2][MAXK], Pn[2][MAXK];   /* Pset[side][m] = T'^m, m = 0..k-1 */
static int *mark0[2], tok0 = 0, cnt0[2];  /* mark0[side][g] == tok0 iff g in T'^k */
static int Tp[2][MAXD * MAXD], Tpn[2];    /* T' */
static int *Qa, *Qb, *Rb;

static void prep_side(int side, int i) {
    int k = D / 2, n = 0;
    cur++;
    for (int a = 0; a < d; a++) {
        if (a == i) continue;
        for (int b = 0; b < d; b++) {
            if (b == i) continue;
            int t = side == 0 ? mul(inv(S[a]), S[b]) : mul(S[a], inv(S[b]));
            if (stamp[t] != cur) { stamp[t] = cur; Tp[side][n++] = t; }
        }
    }
    Tpn[side] = n;
    Pset[side][0][0] = 0; Pn[side][0] = 1;
    for (int m = 1; m < k; m++) Pn[side][m] = prodset(Pset[side][m - 1], Pn[side][m - 1], Tp[side], n, Pset[side][m]);
    /* T'^k into mark0 */
    int c = 0;
    const int *A = Pset[side][k - 1];
    for (int u = 0; u < Pn[side][k - 1]; u++)
        for (int v = 0; v < n; v++) {
            int g = mul(A[u], Tp[side][v]);
            if (mark0[side][g] != tok0) { mark0[side][g] = tok0; c++; }
        }
    cnt0[side] = c;
}

static int *covst, covtok = 0;   /* covst[g] == covtok iff g newly covered by the current candidate */

static int cand_side(int side, int i, int x) {
    int k = D / 2;
    static int Nn[2 * MAXD], T[MAXD * MAXD];
    int nn = 0, nt = 0;
    cur++;                                       /* T = T' u N, N = new pairs not in T' */
    for (int a = 0; a < Tpn[side]; a++) { stamp[Tp[side][a]] = cur; T[nt++] = Tp[side][a]; }
    for (int j = 0; j < d; j++) {
        if (j == i) continue;
        int y = S[j];
        int t1 = side == 0 ? mul(inv(x), y) : mul(x, inv(y));
        int t2 = side == 0 ? mul(inv(y), x) : mul(y, inv(x));
        if (stamp[t1] != cur) { stamp[t1] = cur; Nn[nn++] = t1; T[nt++] = t1; }
        if (stamp[t2] != cur) { stamp[t2] = cur; Nn[nn++] = t2; T[nt++] = t2; }
    }
    if (nn == 0) return N - cnt0[side];
    covtok++;
    int newc = 0, qn = 1;
    int *Q = Qa, *Qn = Qb;
    Q[0] = 0;
    for (int j = 1; j <= k; j++) {               /* words whose last N letter is at position j */
        if (j > 1) { int m = prodset(Q, qn, T, nt, Qn); int *t = Q; Q = Qn; Qn = t; qn = m; }   /* Q = T^(j-1) */
        if (j == k) {                            /* P = T'^0 = {e}: mark T^(k-1) N directly */
            for (int u = 0; u < qn; u++)
                for (int v = 0; v < nn; v++) {
                    int g = mul(Q[u], Nn[v]);
                    if (mark0[side][g] != tok0 && covst[g] != covtok) { covst[g] = covtok; newc++; }
                }
            break;
        }
        int rn = prodset(Q, qn, Nn, nn, Rb);     /* R = T^(j-1) N */
        const int *P = Pset[side][k - j];
        int pn = Pn[side][k - j];
        for (int u = 0; u < rn; u++)
            for (int v = 0; v < pn; v++) {
                int g = mul(Rb[u], P[v]);
                if (mark0[side][g] != tok0 && covst[g] != covtok) { covst[g] = covtok; newc++; }
            }
    }
    return N - cnt0[side] - newc;
}

static void prep(int i) {
    tok0++;
    prep_side(0, i);
    prep_side(1, i);
}
static int cand_cost(int i, int x) {
    return cand_side(0, i, x) + cand_side(1, i, x);
}


/* ---- targeted candidates: missed elements and T^(k-1) of the current S ---- */
static int *Wset[2], Wn[2], *Miss[2], Mn[2];

static void analyze(const int *X) {
    static int T[MAXD * MAXD];
    int k = D / 2;
    int sides = D % 2 ? 2 : 1;
    for (int side = 0; side < sides; side++) {
        int nt = pairset(X, side, T);
        int n = 1;
        Wset[side][0] = 0;                       /* T^0 = {e} */
        for (int j = 1; j < k; j++) {
            n = prodset(Wset[side], n, T, nt, bufB);
            memcpy(Wset[side], bufB, sizeof(int) * n);
        }
        Wn[side] = n;
        int m = D % 2 ? prodset(Wset[side], n, T, nt, bufB) : prodset(X, d, Wset[side], n, bufB);
        cur++;
        for (int u = 0; u < m; u++) stamp[bufB[u]] = cur;
        Mn[side] = 0;
        for (int g = 0; g < N; g++) if (stamp[g] != cur) Miss[side][Mn[side]++] = g;
    }
    if (sides == 1) Mn[1] = 0;
}

/* a replacement for S[i] that covers a random missed element, or -1 */
static int targeted(int i) {
    int tot = Mn[0] + Mn[1];
    if (tot == 0) return -1;
    int r = rnd() % tot, side = r < Mn[0] ? 0 : 1;
    int g = Miss[side][side ? r - Mn[0] : r];
    int u = Wset[side][rnd() % Wn[side]];
    int j;
    do { j = rnd() % d; } while (j == i);
    int sj = S[j], x, v = rnd() & 3;
    if (D % 2 == 0) {
        x = mul(g, inv(u));                     /* g = x u */
    } else {
        int t = (v & 2) ? mul(inv(u), g) : mul(g, inv(u));   /* new letter last (g = u t) or first (g = t u) */
        if (side == 0) x = (v & 1) ? mul(sj, inv(t)) : mul(sj, t);      /* t = x^-1 s_j  or  t = s_j^-1 x */
        else           x = (v & 1) ? mul(t, sj) : mul(inv(t), sj);      /* t = x s_j^-1  or  t = s_j x^-1 */
    }
    if (x == 0 || used(x, d)) return -1;
    return x;
}

/* brute-force: BFS on the Haar graph, return max eccentricity (or 1e9 if disconnected) */
static int bfs_diam(const int *X) {
    int n = 2 * N, diam = 0;
    int *dist = malloc(sizeof(int) * n), *q = malloc(sizeof(int) * n);
    int Xi[MAXD];
    for (int i = 0; i < d; i++) Xi[i] = inv(X[i]);
    for (int src = 0; src < 2; src++) {   /* (e, A) and (e, B) suffice */
        for (int v = 0; v < n; v++) dist[v] = -1;
        int s0 = src * N, h = 0, t = 0;
        dist[s0] = 0; q[t++] = s0;
        while (h < t) {
            int v = q[h++];
            int g = v % N, side = v / N;
            for (int i = 0; i < d; i++) {
                int w = side == 0 ? N + mul(X[i], g) : mul(Xi[i], g);
                if (dist[w] < 0) { dist[w] = dist[v] + 1; q[t++] = w; }
            }
        }
        for (int v = 0; v < n; v++) { if (dist[v] < 0) { diam = 1000000000; break; } if (dist[v] > diam) diam = dist[v]; }
    }
    free(dist); free(q);
    return diam;
}

static inline int used(int x, int n) {
    for (int j = 0; j < n; j++) if (S[j] == x) return 1;
    return 0;
}

static void random_start(void) {
    S[0] = 0;
    for (int i = 1; i < d; i++) {
        int x;
        do { x = rnd() % N; } while (used(x, i));
        S[i] = x;
    }
}

static void load_into(const char *path, uint16_t **MTp, int **ITp, int *Np) {
    FILE *f = fopen(path, "r");
    if (!f) { fprintf(stderr, "cannot open table %s\n", path); exit(1); }
    int n;
    if (fscanf(f, "%d", &n) != 1 || n < 1 || n > 65535) { fprintf(stderr, "bad table size\n"); exit(1); }
    uint16_t *M = malloc(sizeof(uint16_t) * (size_t)n * n);
    for (long i = 0; i < (long)n * n; i++) {
        int v;
        if (fscanf(f, "%d", &v) != 1 || v < 0 || v >= n) { fprintf(stderr, "bad entry %ld\n", i); exit(1); }
        M[i] = (uint16_t)v;
    }
    fclose(f);
    for (int h = 0; h < n; h++)
        if (M[h] != h || M[(long)h * n] != h) { fprintf(stderr, "element 0 is not the identity\n"); exit(1); }
    int *I = malloc(sizeof(int) * n);
    for (int g = 0; g < n; g++) {
        I[g] = -1;
        for (int h = 0; h < n; h++) if (M[(long)g * n + h] == 0) I[g] = h;
        if (I[g] < 0) { fprintf(stderr, "no inverse for %d\n", g); exit(1); }
    }
    *MTp = M; *ITp = I; *Np = n;
}
static void load_table(const char *path) { load_into(path, &MT0, &IT0, &N0); }

/* second factor: a number c means Z_c, anything else is a table file */
static void load_second(const char *arg) {
    char *end;
    long c = strtol(arg, &end, 10);
    if (*end == 0) {
        if (c < 1 || c > 65535) { fprintf(stderr, "bad c\n"); exit(1); }
        C = (int)c;
        MT1 = malloc(sizeof(uint16_t) * (size_t)C * C);
        IT1 = malloc(sizeof(int) * C);
        for (int z = 0; z < C; z++) {
            IT1[z] = z ? C - z : 0;
            for (int w = 0; w < C; w++) MT1[z * C + w] = (uint16_t)((z + w) % C);
        }
    } else {
        load_into(arg, &MT1, &IT1, &C);
    }
}

int main(int argc, char **argv) {
    if (argc > 6 && strcmp(argv[1], "eval") == 0) {   /* eval D d table c x1 .. xd : cost and BFS diameter */
        D = atoi(argv[2]); d = atoi(argv[3]); load_second(argv[5]);
        load_table(argv[4]);
        N = N0 * C;
        bg = malloc(sizeof(int) * N); bz = malloc(sizeof(int) * N);
        for (int x = 0; x < N; x++) { bg[x] = x / C; bz[x] = x % C; }
        stamp = calloc(N, sizeof(int));
        bufA = malloc(sizeof(int) * N); bufB = malloc(sizeof(int) * N);
        for (int i = 0; i < d; i++) S[i] = atoi(argv[6 + i]);
        printf("cost=%d bfs_diameter=%d N=%d\n", cost(S), bfs_diam(S), N);
        if (D % 2 == 1) {                   /* list the missed elements per side as (g0, z) */
            static int T[MAXD * MAXD];
            for (int side = 0; side < 2; side++) {
                int nt = pairset(S, side, T), n = nt;
                int *A = bufA, *B = bufB;
                memcpy(A, T, sizeof(int) * nt);
                for (int j = 1; j < D / 2; j++) { n = prodset(A, n, T, nt, B); int *t = A; A = B; B = t; }
                cur++;
                for (int u = 0; u < n; u++) stamp[A[u]] = cur;
                printf("side %d missed:", side);
                for (int g = 0; g < N; g++) if (stamp[g] != cur) printf(" (%d,%d)", bg[g], bz[g]);
                printf("\n");
            }
        }
        return 0;
    }
    int check = argc > 1 && strcmp(argv[1], "check") == 0;
    int a = check ? 2 : 1;
    if (argc < a + (check ? 5 : 6)) {
        fprintf(stderr, "usage: haar_dd3 D d table c seed seconds [outfile|-] [K] [PT]\n"
                        "       haar_dd check D d table c seed\n");
        return 1;
    }
    D = atoi(argv[a]); d = atoi(argv[a + 1]);
    const char *table = argv[a + 2];
    load_second(argv[a + 3]);
    const char *second = argv[a + 3];
    rs = 0x9E3779B97F4A7C15ULL ^ (unsigned long long)atoll(argv[a + 4]) * 2654435761ULL;
    double secs = check ? 0 : atof(argv[a + 5]);
    const char *out = (!check && argc > a + 6 && strcmp(argv[a + 6], "-")) ? argv[a + 6] : NULL;
    int K = (!check && argc > a + 7) ? atoi(argv[a + 7]) : 20;
    if (d > MAXD || d < 2 || K < 1 || D < 3 || C < 1) { fprintf(stderr, "bad parameters\n"); return 1; }
    load_table(table);
    N = N0 * C;
    bg = malloc(sizeof(int) * N); bz = malloc(sizeof(int) * N);
    for (int x = 0; x < N; x++) { bg[x] = x / C; bz[x] = x % C; }
    stamp = calloc(N, sizeof(int));
    bufA = malloc(sizeof(int) * N); bufB = malloc(sizeof(int) * N);
    Qa = malloc(sizeof(int) * N); Qb = malloc(sizeof(int) * N); Rb = malloc(sizeof(int) * N);
    covst = calloc(N, sizeof(int));
    for (int sd = 0; sd < 2; sd++) {
        mark0[sd] = calloc(N, sizeof(int));
        for (int m = 0; m < MAXK; m++) Pset[sd][m] = malloc(sizeof(int) * N);
    }
    for (int sd = 0; sd < 2; sd++) {
        Wset[sd] = malloc(sizeof(int) * N); Miss[sd] = malloc(sizeof(int) * N);
    }
    double PT = (!check && argc > a + 8) ? atof(argv[a + 8]) : 0.5;
    int odd = D % 2 == 1;
    if (odd && D / 2 > MAXK) { fprintf(stderr, "D too large\n"); return 1; }

    if (check) {
        int ok = 1, zeros = 0;
        for (int trial = 0; trial < 200; trial++) {
            random_start();
            int c = cost(S), dm = bfs_diam(S);
            if ((c == 0) != (dm <= D)) { ok = 0; printf("mismatch trial %d: cost %d diam %d\n", trial, c, dm); }
            zeros += c == 0;
        }
        if (odd)
            for (int trial = 0; trial < 300; trial++) {
                random_start();
                int i = 1 + rnd() % (d - 1), x, old = S[i];
                do { x = rnd() % N; } while (used(x, d) && x != old);
                prep(i);
                int ci = cand_cost(i, x);
                S[i] = x;
                int cf = cost(S);
                if (ci != cf) { ok = 0; printf("incremental mismatch trial %d: %d vs %d\n", trial, ci, cf); }
            }
        int hit = 0, tries = 0;
        for (int trial = 0; trial < 300; trial++) {   /* analyze() agrees with cost(); targeted moves cover their g */
            random_start();
            int c0 = cost(S);
            analyze(S);
            if (Mn[0] + Mn[1] != c0) { ok = 0; printf("analyze mismatch %d vs %d\n", Mn[0] + Mn[1], c0); }
            if (c0 == 0) continue;
            int i = 1 + rnd() % (d - 1), old = S[i];
            unsigned long long save = rs;
            int x = targeted(i);
            if (x < 0) continue;
            rs = save;                                 /* replay the same random choices to learn g */
            int tot = Mn[0] + Mn[1], r = rnd() % tot, side = r < Mn[0] ? 0 : 1;
            int g = Miss[side][side ? r - Mn[0] : r];
            S[i] = x;
            analyze(S);
            int still = 0;
            for (int m = 0; m < Mn[side]; m++) if (Miss[side][m] == g) still = 1;
            tries++; hit += !still;
            S[i] = old;
        }
        printf("targeted: %d of %d moves covered their element\n", hit, tries);
        printf("check %s (D=%d d=%d N=%d, %d of 200 random S had cost 0)\n", ok ? "OK" : "FAILED", D, d, N, zeros);
        return ok ? 0 : 1;
    }

    int bestc = 1 << 30, restarts = 0;
    long long steps = 0;
    double t0 = now(), lastp = t0;
    while (now() - t0 < secs && bestc > 0) {
        restarts++;
        random_start();
        int c = cost(S);
        analyze(S);
        double T0 = 2.0, temp = T0;
        long since = 0;
        int runbest = c;
        while (c > 0 && now() - t0 < secs) {
            steps++;
            int bi = -1, bx = 0, bc = 1 << 30;
            int si = 1 + rnd() % (d - 1);
            if (odd) prep(si);
            for (int t = 0; t < K; t++) {
                int i = odd ? si : 1 + rnd() % (d - 1);
                int nw = -1, old = S[i];
                if ((rnd() & 0xffff) < PT * 65536.0) nw = targeted(i);
                if (nw < 0) do { nw = rnd() % N; } while (used(nw, d));
                int c2;
                if (odd) c2 = cand_cost(i, nw);
                else { S[i] = nw; c2 = cost(S); S[i] = old; }
                evals++;
                if (c2 < bc) { bc = c2; bi = i; bx = nw; }
            }
            if (bc <= c || exp((c - bc) / temp) * 4294967296.0 > (double)(rnd() & 0xffffffffULL)) {
                if (S[bi] != bx) { S[bi] = bx; analyze(S); }
                c = bc;
                if (c < runbest) { runbest = c; since = 0; } else since++;
            } else {
                since++;
            }
            temp = T0 * exp(-(double)(since % 20000) / 4000.0) + 0.05;
            if (c < bestc) { bestc = c; memcpy(best, S, sizeof(int) * d); }
            if (since > 60000) break;
            if (now() - lastp > 300) {
                lastp = now();
                printf("  t=%.0f best=%d run=%d cur=%d restarts=%d steps=%lld\n", lastp - t0, bestc, runbest, c, restarts, steps);
                fflush(stdout);
            }
        }
    }
    double el = now() - t0;
    printf("D=%d d=%d table=%s c=%d N=%d n=%d K=%d best=%d restarts=%d steps=%lld evals=%lld time=%.1f evals_per_s=%.0f\n",
           D, d, table, C, N, 2 * N, K, bestc, restarts, steps, evals, el, evals / el);
    if (bestc > 0 && out) {                 /* near miss: keep S in <outfile>.best for later study */
        char path[1024];
        snprintf(path, sizeof path, "%s.best", out);
        FILE *f = fopen(path, "w");
        if (f) {
            fprintf(f, "%d %d %d %d %s %s best=%d\n", D, d, N, C, table, second, bestc);
            for (int i = 0; i < d; i++) fprintf(f, "%d\n", best[i]);
            fclose(f);
        }
    }
    if (bestc == 0 && out) {
        if (bfs_diam(best) > D) { fprintf(stderr, "internal: BFS disagrees on best\n"); return 2; }
        FILE *f = fopen(out, "w");
        if (!f) { fprintf(stderr, "cannot write %s\n", out); f = stdout; }
        fprintf(f, "%d %d %d %d %s %s\n", D, d, N, C, table, second);
        for (int i = 0; i < d; i++) fprintf(f, "%d\n", best[i]);
        if (f != stdout) fclose(f);
    }
    return 0;
}
