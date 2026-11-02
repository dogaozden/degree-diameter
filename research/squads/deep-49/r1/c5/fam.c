/* c5 fam.c: exhaustive twin-type vertex insertions into the 4,970 graph X (seeds/valid4970.edges).
   X: A = 0..2484, B = 2485..4969, 4-regular. New a* = 4970 (A side), b* = 4971 (B side).
   A surgery is (P, Q, M): a* ~ P (4 B-vertices, may include b*), b* ~ Q (4 A-vertices, may include a*),
   M = perfect matching of deleted X-edges (q,p), q in Q, p in P (q loses p and gains b*, p loses q and gains a*).
   Degree preservation forces M to be a perfect matching between the Q- and P-vertices of X.
   Cost = unordered far pairs (distance > 9 or unreachable), bit-parallel BFS.
   usage: fam FAMILY BESTFILE [wFrom wTo]   FAMILY in D1 D2 D3 D3m D4 D5 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>

#define N0 4970
#define NN 4972
#define NA 2485
#define AS 4970
#define BS 4971

static int base[N0][4];
static int nb[NN][4];
static uint64_t vis[NN], fr[NN], nx[NN];

static void load(const char *fn) {
    FILE *f = fopen(fn, "r");
    if (!f) { fprintf(stderr, "cannot open %s\n", fn); exit(2); }
    int n; if (fscanf(f, "%d", &n) != 1 || n != N0) { fprintf(stderr, "bad header\n"); exit(2); }
    int deg[N0]; memset(deg, 0, sizeof deg);
    int u, v;
    while (fscanf(f, "%d %d", &u, &v) == 2) {
        if (!(u < NA && v >= NA && v < N0) || deg[u] >= 4 || deg[v] >= 4) { fprintf(stderr, "bad edge %d %d\n", u, v); exit(2); }
        base[u][deg[u]++] = v; base[v][deg[v]++] = u;
    }
    for (int i = 0; i < N0; i++) if (deg[i] != 4) { fprintf(stderr, "deg\n"); exit(2); }
    fclose(f);
}

static void reset(void) { for (int i = 0; i < N0; i++) memcpy(nb[i], base[i], sizeof nb[i]); }

static int replace_in(int x, int from, int to) {
    for (int k = 0; k < 4; k++) if (nb[x][k] == from) { nb[x][k] = to; return 1; }
    return 0;
}

static int build(const int *P, const int *Q, int nm, const int M[][2]) {
    reset();
    for (int i = 0; i < 4; i++) { nb[AS][i] = P[i]; nb[BS][i] = Q[i]; }
    for (int i = 0; i < nm; i++) {
        int q = M[i][0], p = M[i][1];
        if (!replace_in(q, p, BS)) return 0;
        if (!replace_in(p, q, AS)) return 0;
    }
    return 1;
}

static int valid(void) {
    for (int x = 0; x < NN; x++)
        for (int k = 0; k < 4; k++) {
            int y = nb[x][k];
            if (y < 0 || y >= NN || y == x) return 0;
            for (int j = 0; j < k; j++) if (nb[x][j] == y) return 0;
            int ok = 0; for (int j = 0; j < 4; j++) if (nb[y][j] == x) ok = 1;
            if (!ok) return 0;
        }
    return 1;
}

static long long far9(void) {
    long long far = 0;
    int n = NN;
    for (int s0 = 0; s0 < n; s0 += 64) {
        int ns = n - s0 < 64 ? n - s0 : 64;
        uint64_t full = ns == 64 ? ~0ULL : ((1ULL << ns) - 1);
        memset(vis, 0, sizeof vis); memset(fr, 0, sizeof fr);
        for (int k = 0; k < ns; k++) { vis[s0 + k] |= 1ULL << k; fr[s0 + k] |= 1ULL << k; }
        for (int lev = 1; lev <= 9; lev++) {
            int any = 0;
            for (int x = 0; x < n; x++) {
                uint64_t acc = fr[nb[x][0]] | fr[nb[x][1]] | fr[nb[x][2]] | fr[nb[x][3]];
                acc &= ~vis[x]; nx[x] = acc; any |= (acc != 0);
            }
            if (!any) break;
            for (int x = 0; x < n; x++) vis[x] |= nx[x];
            memcpy(fr, nx, sizeof(uint64_t) * n);
        }
        for (int x = 0; x < n; x++) far += __builtin_popcountll(full & ~vis[x]);
    }
    return far / 2;
}

/* family statistics */
static long long nev = 0, nvalid = 0, bestf = -1, nbest = 0;
static long long hist[64]; /* histogram of far counts up to 63, last bucket = >=63 */
static char bestfile[512];
static char bestdesc[512];
static double t0;

static void write_graph(const char *fn) {
    FILE *f = fopen(fn, "w");
    fprintf(f, "%d\n", NN);
    for (int x = 0; x < NN; x++) for (int k = 0; k < 4; k++) if (nb[x][k] > x) fprintf(f, "%d %d\n", x, nb[x][k]);
    fclose(f);
}

static void evaluate(const int *P, const int *Q, int nm, const int M[][2], const char *desc) {
    nev++;
    if (!build(P, Q, nm, M) || !valid()) return;
    nvalid++;
    long long f = far9();
    hist[f < 63 ? f : 63]++;
    if (bestf < 0 || f < bestf) {
        bestf = f; nbest = 1;
        write_graph(bestfile);
        strncpy(bestdesc, desc, sizeof bestdesc - 1);
        printf("NEWBEST far=%lld %s\n", f, desc); fflush(stdout);
    } else if (f == bestf) nbest++;
}

static const int perm3[6][3] = {{0,1,2},{0,2,1},{1,0,2},{1,2,0},{2,0,1},{2,1,0}};
static const int perm4[24][4] = {
 {0,1,2,3},{0,1,3,2},{0,2,1,3},{0,2,3,1},{0,3,1,2},{0,3,2,1},
 {1,0,2,3},{1,0,3,2},{1,2,0,3},{1,2,3,0},{1,3,0,2},{1,3,2,0},
 {2,0,1,3},{2,0,3,1},{2,1,0,3},{2,1,3,0},{2,3,0,1},{2,3,1,0},
 {3,0,1,2},{3,0,2,1},{3,1,0,2},{3,1,2,0},{3,2,0,1},{3,2,1,0}};

/* D1: a* twin of v=0 (P = N(0)); b* gets a transversal a_i of the freed edges (a_i, b_i), a_i in N(b_i)\{0}. */
static void fam_D1(void) {
    int P[4], Q[4], M[4][2];
    for (int i = 0; i < 4; i++) P[i] = base[0][i];
    int c[4];
    for (c[0] = 0; c[0] < 3; c[0]++) for (c[1] = 0; c[1] < 3; c[1]++) for (c[2] = 0; c[2] < 3; c[2]++) for (c[3] = 0; c[3] < 3; c[3]++) {
        for (int i = 0; i < 4; i++) {
            int b = P[i], cnt = 0, a = -1;
            for (int k = 0; k < 4; k++) if (base[b][k] != 0) { if (cnt == c[i]) a = base[b][k]; cnt++; }
            Q[i] = a; M[i][0] = a; M[i][1] = b;
        }
        char d[128]; snprintf(d, sizeof d, "D1 c=%d%d%d%d Q=%d,%d,%d,%d", c[0], c[1], c[2], c[3], Q[0], Q[1], Q[2], Q[3]);
        evaluate(P, Q, 4, M, d);
    }
}

/* D2: b* twin of w=2485 (Q = N(w)); a* gets p_j in N(q_j)\{w}, matched edge (q_j, p_j). */
static void fam_D2(void) {
    int w = NA; /* B vertex 2485 */
    int Q[4], P[4], M[4][2];
    for (int i = 0; i < 4; i++) Q[i] = base[w][i];
    int c[4];
    for (c[0] = 0; c[0] < 3; c[0]++) for (c[1] = 0; c[1] < 3; c[1]++) for (c[2] = 0; c[2] < 3; c[2]++) for (c[3] = 0; c[3] < 3; c[3]++) {
        for (int i = 0; i < 4; i++) {
            int a = Q[i], cnt = 0, p = -1;
            for (int k = 0; k < 4; k++) if (base[a][k] != w) { if (cnt == c[i]) p = base[a][k]; cnt++; }
            P[i] = p; M[i][0] = a; M[i][1] = p;
        }
        char d[128]; snprintf(d, sizeof d, "D2 c=%d%d%d%d P=%d,%d,%d,%d", c[0], c[1], c[2], c[3], P[0], P[1], P[2], P[3]);
        evaluate(P, Q, 4, M, d);
    }
}

/* D3: a* ~ {p1,p2,p3,b*}, b* ~ {a1,a2,a3,a*}; p_i = three of N(0) (omit o), (a_i,p_i) deleted, a_i in N(p_i)\{0}. */
static void fam_D3(void) {
    for (int o = 0; o < 4; o++) {
        int p[3], k = 0;
        for (int i = 0; i < 4; i++) if (i != o) p[k++] = base[0][i];
        int c[3];
        for (c[0] = 0; c[0] < 3; c[0]++) for (c[1] = 0; c[1] < 3; c[1]++) for (c[2] = 0; c[2] < 3; c[2]++) {
            int a[3];
            for (int i = 0; i < 3; i++) {
                int cnt = 0; a[i] = -1;
                for (int j = 0; j < 4; j++) if (base[p[i]][j] != 0) { if (cnt == c[i]) a[i] = base[p[i]][j]; cnt++; }
            }
            int P[4] = {p[0], p[1], p[2], BS}, Q[4] = {a[0], a[1], a[2], AS};
            int M[3][2] = {{a[0], p[0]}, {a[1], p[1]}, {a[2], p[2]}};
            char d[160]; snprintf(d, sizeof d, "D3 omit=%d c=%d%d%d a=%d,%d,%d", o, c[0], c[1], c[2], a[0], a[1], a[2]);
            evaluate(P, Q, 3, M, d);
        }
    }
}

/* D3m: mirror of D3: b* ~ {q1,q2,q3,a*}, a* ~ {p1,p2,p3,b*}, q_i = three of N(w=2485) (omit o), (q_i,p_i) deleted,
   p_i in N(q_i)\{w}. */
static void fam_D3m(void) {
    int w = NA;
    for (int o = 0; o < 4; o++) {
        int q[3], k = 0;
        for (int i = 0; i < 4; i++) if (i != o) q[k++] = base[w][i];
        int c[3];
        for (c[0] = 0; c[0] < 3; c[0]++) for (c[1] = 0; c[1] < 3; c[1]++) for (c[2] = 0; c[2] < 3; c[2]++) {
            int p[3];
            for (int i = 0; i < 3; i++) {
                int cnt = 0; p[i] = -1;
                for (int j = 0; j < 4; j++) if (base[q[i]][j] != w) { if (cnt == c[i]) p[i] = base[q[i]][j]; cnt++; }
            }
            int P[4] = {p[0], p[1], p[2], BS}, Q[4] = {q[0], q[1], q[2], AS};
            int M[3][2] = {{q[0], p[0]}, {q[1], p[1]}, {q[2], p[2]}};
            char d[160]; snprintf(d, sizeof d, "D3m omit=%d c=%d%d%d w=%d", o, c[0], c[1], c[2], w);
            evaluate(P, Q, 3, M, d);
        }
    }
}

/* D4: a* twin of v=0 (P = N(0)), b* twin of w (Q = N(w)), deleted edges = perfect matching between N(w) and N(0). */
static void fam_D4(int wf, int wt) {
    int P[4], Q[4], M[4][2];
    for (int i = 0; i < 4; i++) P[i] = base[0][i];
    for (int w = wf; w < wt; w++) {
        if (w < NA || w >= N0) continue;
        for (int i = 0; i < 4; i++) Q[i] = base[w][i];
        for (int s = 0; s < 24; s++) {
            int ok = 1;
            for (int i = 0; i < 4; i++) {
                int q = Q[i], p = P[perm4[s][i]], f = 0;
                for (int k = 0; k < 4; k++) if (base[q][k] == p) f = 1;
                if (!f) { ok = 0; break; }
                M[i][0] = q; M[i][1] = p;
            }
            if (!ok) continue;
            char d[160]; snprintf(d, sizeof d, "D4 w=%d perm=%d%d%d%d", w, perm4[s][0], perm4[s][1], perm4[s][2], perm4[s][3]);
            evaluate(P, Q, 4, M, d);
        }
    }
}

/* D5: a* ~ {b*} + P', b* ~ {a*} + Q', P' = three of N(0) (omit o), Q' = three of N(w) (omit o'), perfect matching
   of size 3 between P' and Q' in X (deleted), w over all B vertices. */
static void fam_D5(int wf, int wt) {
    for (int w = wf; w < wt; w++) {
        if (w < NA || w >= N0) continue;
        for (int o = 0; o < 4; o++) for (int o2 = 0; o2 < 4; o2++) {
            int p[3], q[3], kp = 0, kq = 0;
            for (int i = 0; i < 4; i++) if (i != o) p[kp++] = base[0][i];
            for (int i = 0; i < 4; i++) if (i != o2) q[kq++] = base[w][i];
            for (int s = 0; s < 6; s++) {
                int ok = 1, M[3][2];
                for (int i = 0; i < 3; i++) {
                    int qq = q[i], pp = p[perm3[s][i]], f = 0;
                    for (int k = 0; k < 4; k++) if (base[qq][k] == pp) f = 1;
                    if (!f) { ok = 0; break; }
                    M[i][0] = qq; M[i][1] = pp;
                }
                if (!ok) continue;
                int P[4] = {p[0], p[1], p[2], BS}, Q[4] = {q[0], q[1], q[2], AS};
                char d[160]; snprintf(d, sizeof d, "D5 w=%d o=%d o2=%d perm=%d%d%d", w, o, o2, perm3[s][0], perm3[s][1], perm3[s][2]);
                evaluate(P, Q, 3, M, d);
            }
        }
    }
}


/* BFS distances in the base graph X from a source */
static void bfs_base(int s, int *d) {
    static int q[N0];
    for (int i = 0; i < N0; i++) d[i] = -1;
    int h = 0, t = 0; d[s] = 0; q[t++] = s;
    while (h < t) { int x = q[h++]; for (int k = 0; k < 4; k++) { int y = base[x][k]; if (d[y] < 0) { d[y] = d[x] + 1; q[t++] = y; } } }
}

/* D7: a* ~ {p1,p2,p3} (three of N(0), omit o) + x (B vertex at distance 3 from 0); b* ~ {a1,a2,a3,a_x};
   (a_i,p_i) with a_i in N(p_i)\{0} and (a_x,x) with a_x in N(x) are the deleted edges. x ranges over list index [wf,wt). */
static void fam_D7(int wf, int wt) {
    static int d0[N0]; bfs_base(0, d0);
    int xs[N0], nx_ = 0;
    for (int x = NA; x < N0; x++) if (d0[x] == 3) xs[nx_++] = x;
    if (wt > nx_) wt = nx_;
    for (int xi = wf; xi < wt; xi++) {
        int x = xs[xi];
        for (int o = 0; o < 4; o++) {
            int p[3], k = 0;
            for (int i = 0; i < 4; i++) if (i != o) p[k++] = base[0][i];
            for (int c0 = 0; c0 < 3; c0++) for (int c1 = 0; c1 < 3; c1++) for (int c2 = 0; c2 < 3; c2++) for (int cx = 0; cx < 4; cx++) {
                int c[3] = {c0, c1, c2}, a[3];
                for (int i = 0; i < 3; i++) {
                    int cnt = 0; a[i] = -1;
                    for (int j = 0; j < 4; j++) if (base[p[i]][j] != 0) { if (cnt == c[i]) a[i] = base[p[i]][j]; cnt++; }
                }
                int ax = base[x][cx];
                int P[4] = {p[0], p[1], p[2], x}, Q[4] = {a[0], a[1], a[2], ax};
                int M[4][2] = {{a[0], p[0]}, {a[1], p[1]}, {a[2], p[2]}, {ax, x}};
                char d[200]; snprintf(d, sizeof d, "D7 x=%d o=%d c=%d%d%d cx=%d a=%d,%d,%d ax=%d", x, o, c0, c1, c2, cx, a[0], a[1], a[2], ax);
                evaluate(P, Q, 4, M, d);
            }
        }
    }
}

/* D7m: mirror: b* ~ {q1,q2,q3} (three of N(w), w=2485, omit o) + y (A vertex at distance 3 from w);
   a* ~ {p1,p2,p3,p_y}; (q_i,p_i), p_i in N(q_i)\{w}, and (y,p_y), p_y in N(y) are deleted. y ranges over list index. */
static void fam_D7m(int wf, int wt) {
    int w = NA;
    static int dw[N0]; bfs_base(w, dw);
    int ys[N0], ny = 0;
    for (int y = 0; y < NA; y++) if (dw[y] == 3) ys[ny++] = y;
    if (wt > ny) wt = ny;
    for (int yi = wf; yi < wt; yi++) {
        int y = ys[yi];
        for (int o = 0; o < 4; o++) {
            int q[3], k = 0;
            for (int i = 0; i < 4; i++) if (i != o) q[k++] = base[w][i];
            for (int c0 = 0; c0 < 3; c0++) for (int c1 = 0; c1 < 3; c1++) for (int c2 = 0; c2 < 3; c2++) for (int cy = 0; cy < 4; cy++) {
                int c[3] = {c0, c1, c2}, p[3];
                for (int i = 0; i < 3; i++) {
                    int cnt = 0; p[i] = -1;
                    for (int j = 0; j < 4; j++) if (base[q[i]][j] != w) { if (cnt == c[i]) p[i] = base[q[i]][j]; cnt++; }
                }
                int py = base[y][cy];
                int P[4] = {p[0], p[1], p[2], py}, Q[4] = {q[0], q[1], q[2], y};
                int M[4][2] = {{q[0], p[0]}, {q[1], p[1]}, {q[2], p[2]}, {y, py}};
                char d[200]; snprintf(d, sizeof d, "D7m y=%d o=%d c=%d%d%d cy=%d q=%d,%d,%d py=%d", y, o, c0, c1, c2, cy, q[0], q[1], q[2], py);
                evaluate(P, Q, 4, M, d);
            }
        }
    }
}


/* GEN k R: surgeries given by a k-matching of X-edges (k = 3: a*b* edge; k = 4: none). WLOG one deleted edge is
   e0 = (0, N(0)[t]) (the four edge types are the four G-orbits of edges); the other k-1 edges are chosen among
   the X-edges with an endpoint within distance R of {0, N(0)[t]}, pairwise vertex-disjoint. */
static void fam_GEN(int k, int R, int wf, int wt) {
    static int d[N0], q_[N0];
    for (int t = 0; t < 4; t++) {
        int p0 = base[0][t];
        for (int i = 0; i < N0; i++) d[i] = -1;
        int h = 0, tl = 0; d[0] = 0; q_[tl++] = 0; d[p0] = 0; q_[tl++] = p0;
        while (h < tl) { int x = q_[h++]; for (int j = 0; j < 4; j++) { int y = base[x][j]; if (d[y] < 0) { d[y] = d[x] + 1; q_[tl++] = y; } } }
        /* list of candidate edges (qa, pb) with qa in A, pb in B, min endpoint distance <= R, not touching e0 */
        static int EQ[20000], EP[20000]; int ne = 0;
        for (int qa = 1; qa < NA; qa++) for (int j = 0; j < 4; j++) {
            int pb = base[qa][j];
            if (qa == 0 || pb == p0) continue;
            int dm = d[qa] < d[pb] ? d[qa] : d[pb];
            if (dm <= R && dm >= 0) { EQ[ne] = qa; EP[ne] = pb; ne++; }
        }
        if (k == 3) {
            for (int i = wf; i < ne && i < wt; i++) for (int j = i + 1; j < ne; j++) {
                if (EQ[i] == EQ[j] || EP[i] == EP[j]) continue;
                int M[3][2] = {{0, p0}, {EQ[i], EP[i]}, {EQ[j], EP[j]}};
                int P[4] = {p0, EP[i], EP[j], BS}, Q[4] = {0, EQ[i], EQ[j], AS};
                char dd[160]; snprintf(dd, sizeof dd, "GEN3 R=%d t=%d e=(%d,%d)(%d,%d)", R, t, EQ[i], EP[i], EQ[j], EP[j]);
                evaluate(P, Q, 3, M, dd);
            }
        } else {
            for (int i = wf; i < ne && i < wt; i++) for (int j = i + 1; j < ne; j++) for (int l = j + 1; l < ne; l++) {
                int qs[3] = {EQ[i], EQ[j], EQ[l]}, ps[3] = {EP[i], EP[j], EP[l]};
                int ok = 1;
                for (int a = 0; a < 3 && ok; a++) for (int b = a + 1; b < 3; b++) if (qs[a] == qs[b] || ps[a] == ps[b]) { ok = 0; break; }
                if (!ok) continue;
                int M[4][2] = {{0, p0}, {qs[0], ps[0]}, {qs[1], ps[1]}, {qs[2], ps[2]}};
                int P[4] = {p0, ps[0], ps[1], ps[2]}, Q[4] = {0, qs[0], qs[1], qs[2]};
                char dd[160]; snprintf(dd, sizeof dd, "GEN4 R=%d t=%d e=(%d,%d)(%d,%d)(%d,%d)", R, t, qs[0], ps[0], qs[1], ps[1], qs[2], ps[2]);
                evaluate(P, Q, 4, M, dd);
            }
        }
        fprintf(stderr, "t=%d candidate edges=%d\n", t, ne);
    }
}


/* SWAP: single-edge swap neighbourhood of a 4-matching (no a*b* edge). Start matching from env START="q1,p1;q2,p2;q3,p3;q4,p4".
   Each position j in 0..3 is replaced by any X-edge (q,p) (edge index e in [wf,wt) over the 9940 edges) disjoint from the
   other three edges. Records the best neighbour; prints the number of neighbours strictly better than the start. */
static void fam_SWAP(int wf, int wt, const char *start) {
    int sq[4], sp[4], k = 0;
    const char *c = start;
    while (k < 4 && *c) {
        int a, b, nread;
        if (sscanf(c, "%d,%d%n", &a, &b, &nread) != 2) break;
        sq[k] = a; sp[k] = b; k++; c += nread;
        while (*c == ';' || *c == ' ') c++;
    }
    if (k != 4) { fprintf(stderr, "bad START\n"); exit(2); }
    /* edge list of X */
    static int EQ[N0 * 2], EP[N0 * 2]; int ne = 0;
    for (int q = 0; q < NA; q++) for (int j = 0; j < 4; j++) { EQ[ne] = q; EP[ne] = base[q][j]; ne++; }
    int start_far = -1;
    { int M[4][2]; int P[4], Q[4];
      for (int i = 0; i < 4; i++) { M[i][0] = sq[i]; M[i][1] = sp[i]; P[i] = sp[i]; Q[i] = sq[i]; }
      if (build(P, Q, 4, M) && valid()) { start_far = far9(); }
      printf("START far=%lld\n", start_far); fflush(stdout); }
    for (int j = 0; j < 4; j++) for (int e = wf; e < wt && e < ne; e++) {
        int q = EQ[e], p = EP[e], ok = 1;
        for (int i = 0; i < 4 && ok; i++) if (i != j && (sq[i] == q || sp[i] == p)) ok = 0;
        if (!ok) continue;
        if (q == sq[j] && p == sp[j]) continue;
        int M[4][2], P[4], Q[4];
        for (int i = 0; i < 4; i++) { M[i][0] = i == j ? q : sq[i]; M[i][1] = i == j ? p : sp[i]; P[i] = M[i][1]; Q[i] = M[i][0]; }
        char d[200]; snprintf(d, sizeof d, "SWAP j=%d e=(%d,%d) M=(%d,%d)(%d,%d)(%d,%d)(%d,%d)", j, q, p,
            M[0][0], M[0][1], M[1][0], M[1][1], M[2][0], M[2][1], M[3][0], M[3][1]);
        evaluate(P, Q, 4, M, d);
    }
}


/* SWAPK: single-edge swap neighbourhood of a 3-matching with the a*b* edge (K = 3). START="q1,p1;q2,p2;q3,p3". */
static void fam_SWAP3(int wf, int wt, const char *start) {
    int sq[3], sp[3], k = 0;
    const char *c = start;
    while (k < 3 && *c) {
        int a, b, nread;
        if (sscanf(c, "%d,%d%n", &a, &b, &nread) != 2) break;
        sq[k] = a; sp[k] = b; k++; c += nread;
        while (*c == ';' || *c == ' ') c++;
    }
    if (k != 3) { fprintf(stderr, "bad START\n"); exit(2); }
    static int EQ[N0 * 2], EP[N0 * 2]; int ne = 0;
    for (int q = 0; q < NA; q++) for (int j = 0; j < 4; j++) { EQ[ne] = q; EP[ne] = base[q][j]; ne++; }
    for (int j = 0; j < 3; j++) for (int e = wf; e < wt && e < ne; e++) {
        int q = EQ[e], p = EP[e], ok = 1;
        for (int i = 0; i < 3 && ok; i++) if (i != j && (sq[i] == q || sp[i] == p)) ok = 0;
        if (!ok) continue;
        if (q == sq[j] && p == sp[j]) continue;
        int M[3][2], P[4], Q[4];
        for (int i = 0; i < 3; i++) { M[i][0] = i == j ? q : sq[i]; M[i][1] = i == j ? p : sp[i]; P[i] = M[i][1]; Q[i] = M[i][0]; }
        P[3] = BS; Q[3] = AS;
        char d[200]; snprintf(d, sizeof d, "SWAP3 j=%d e=(%d,%d) M=(%d,%d)(%d,%d)(%d,%d)", j, q, p,
            M[0][0], M[0][1], M[1][0], M[1][1], M[2][0], M[2][1]);
        evaluate(P, Q, 3, M, d);
    }
}

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: fam FAMILY BESTFILE [wFrom wTo]\n"); return 2; }
    load("/home/user/degree-diameter/research/squads/deep-49/seeds/valid4970.edges");
    snprintf(bestfile, sizeof bestfile, "%s", argv[2]);
    int wf = argc > 3 ? atoi(argv[3]) : 0, wt = argc > 4 ? atoi(argv[4]) : N0;
    int Rr = argc > 5 ? atoi(argv[5]) : 1;
    t0 = (double)clock() / CLOCKS_PER_SEC;
    const char *f = argv[1];
    if (!strcmp(f, "D1")) fam_D1();
    else if (!strcmp(f, "D2")) fam_D2();
    else if (!strcmp(f, "D3")) fam_D3();
    else if (!strcmp(f, "D3m")) fam_D3m();
    else if (!strcmp(f, "D4")) fam_D4(wf, wt);
    else if (!strcmp(f, "D5")) fam_D5(wf, wt);
    else if (!strcmp(f, "D7")) fam_D7(wf, wt);
    else if (!strcmp(f, "SWAP")) fam_SWAP(wf, wt, getenv("START"));
    else if (!strcmp(f, "SWAP3")) fam_SWAP3(wf, wt, getenv("START"));
    else if (!strcmp(f, "GEN3")) fam_GEN(3, Rr, wf, wt);
    else if (!strcmp(f, "GEN4")) fam_GEN(4, Rr, wf, wt);
    else if (!strcmp(f, "D7m")) fam_D7m(wf, wt);
    else { fprintf(stderr, "unknown family\n"); return 2; }
    printf("FAMILY %s range=[%d,%d) evaluated=%lld valid_surgeries=%lld best_far=%lld at_best=%lld cpu=%.1fs\n",
           f, wf, wt, nev, nvalid, bestf, nbest, (double)clock() / CLOCKS_PER_SEC - t0);
    printf("HIST");
    for (int i = 0; i < 64; i++) if (hist[i]) printf(" %d:%lld", i, hist[i]);
    printf("\n");
    return 0;
}
