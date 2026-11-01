/* coset2.c: bipartite coset graphs over G = PGL(2,q) or PSL(2,q) (q prime < 256) with vertex stabilizer H.
 * Vertices: left cosets Hx (side A) and Hy (side B). Edge Hx ~ Hy iff x y^-1 lies in D, where D is a union of R
 * disjoint regular double cosets H g_r H (size h*h each), so |D| = R*h*h = d*h and the degree is d.
 * G acts on both sides, so the diameter test is two BFS (from an A vertex, and from a B vertex).
 * Usage: coset2 q d h T R K seed     (K random candidates; each = R random regular double cosets)
 *   env HTYPE=D : H dihedral of order h (order h/2 torus element r and a non-square involution s)
 *   default     : H cyclic of order h.     env PSL=1 : G = PSL(2,q) instead of PGL(2,q).
 *   env CHECK=1 : graph sanity check on the first candidate (d-regular, symmetric adjacency).
 * Output per candidate: "cand <i> reps <keys> uncB <n> uncA <n>". uncB = B vertices at distance > T-1 from the
 * A root (unreached counted), uncA = A vertices at distance > T (root excluded). Histogram of uncB at the end.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

static int Q, Q2, Q3, NKEYS, MG, PSLF;
static int invt[256];
typedef struct { int a, b, c, d; } E;
static int *labkey, *stampk, *repk, NL, IDKEY;

static inline E dec(int key) {
    E r;
    if (key < Q3) { r.a = 1; r.b = key / Q2; r.c = (key / Q) % Q; r.d = key % Q; }
    else { int k = key - Q3; r.a = 0; r.b = 1; r.c = k / Q; r.d = k % Q; }
    return r;
}
static inline int kof(E x) {
    if (x.a) { int s = invt[x.a]; int b = x.b * s % Q, c = x.c * s % Q, d = x.d * s % Q; return b * Q2 + c * Q + d; }
    { int s = invt[x.b]; int c = x.c * s % Q, d = x.d * s % Q; return Q3 + c * Q + d; }
}
static inline E mul(E x, E y) {
    E r;
    r.a = (x.a * y.a + x.b * y.c) % Q; r.b = (x.a * y.b + x.b * y.d) % Q;
    r.c = (x.c * y.a + x.d * y.c) % Q; r.d = (x.c * y.b + x.d * y.d) % Q;
    return r;
}
static inline E einv(E x) { E r; r.a = x.d; r.b = (Q - x.b) % Q; r.c = (Q - x.c) % Q; r.d = x.a; return r; }
static int is_sq(int x) { int p = 1; for (int e = 0; e < (Q - 1) / 2; e++) p = p * x % Q; return p == 1; }
static int valid_key(int key) {
    E e = dec(key); int det;
    if (key < Q3) det = ((e.d - e.b * e.c) % Q + Q) % Q; else det = (Q - e.c) % Q;
    if (det == 0) return 0;
    if (PSLF && !is_sq(det)) return 0;
    return 1;
}
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }

int main(int argc, char **argv) {
    if (argc < 8) { fprintf(stderr, "usage: coset2 q d h T R K seed\n"); return 2; }
    Q = atoi(argv[1]); int dg = atoi(argv[2]), h = atoi(argv[3]), T = atoi(argv[4]), R = atoi(argv[5]);
    int K = atoi(argv[6]); unsigned seed = (unsigned)atol(argv[7]);
    PSLF = getenv("PSL") && !strcmp(getenv("PSL"), "1");
    Q2 = Q * Q; Q3 = Q2 * Q; NKEYS = Q3 + Q2; MG = PSLF ? (Q3 - Q) / 2 : Q3 - Q;
    if (R * h * h != dg * h) { fprintf(stderr, "need R*h*h == d*h (regular double cosets)\n"); return 2; }
    for (int x = 1; x < Q; x++) for (int y = 1; y < Q; y++) if (x * y % Q == 1) invt[x] = y;
    IDKEY = 1;
    labkey = malloc(sizeof(int) * NKEYS);
    stampk = calloc(NKEYS, sizeof(int));
    long nvalid = 0;
    for (int k = 0; k < NKEYS; k++) { labkey[k] = -1; if (valid_key(k)) nvalid++; }
    if (nvalid != MG) { fprintf(stderr, "bad element count %ld vs %d\n", nvalid, MG); return 2; }

    /* H */
    E *H = malloc(sizeof(E) * h);
    int dihedral = getenv("HTYPE") && !strcmp(getenv("HTYPE"), "D");
    if (!dihedral) {
        int g0 = -1;
        for (int k = 0; k < NKEYS && g0 < 0; k++) {
            if (!valid_key(k)) continue;
            E g = dec(k), p = g; int ord = 1;
            while (kof(p) != IDKEY && ord < h) { p = mul(p, g); ord++; }
            if (ord == h && kof(p) == IDKEY) g0 = k;
        }
        if (g0 < 0) { fprintf(stderr, "no element of order %d\n", h); return 2; }
        E g = dec(g0), p = dec(IDKEY); for (int i = 0; i < h; i++) { H[i] = p; p = mul(p, g); }
    } else {
        int rkey = -1;
        for (int k = 0; k < NKEYS && rkey < 0; k++) {
            if (!valid_key(k)) continue;
            E g = dec(k), p = g; int ord = 1;
            while (kof(p) != IDKEY && ord < h / 2) { p = mul(p, g); ord++; }
            if (ord == h / 2 && kof(p) == IDKEY && h / 2 > 2) rkey = k;
        }
        if (rkey < 0) { fprintf(stderr, "no element of order %d\n", h / 2); return 2; }
        int nu = -1;
        for (int x = 2; x < Q && nu < 0; x++) if (!is_sq(x)) nu = x;
        E r = dec(rkey), s; s.a = 0; s.b = 1; s.c = nu; s.d = 0;
        int cnt = 1; H[0] = dec(IDKEY); int changed = 1;
        while (changed) {
            changed = 0;
            for (int i = 0; i < cnt; i++) {
                E gens[2] = { r, s };
                for (int t = 0; t < 2; t++) {
                    E y = mul(H[i], gens[t]); int k = kof(y), found = 0;
                    for (int j = 0; j < cnt; j++) if (kof(H[j]) == k) { found = 1; break; }
                    if (!found) { if (cnt >= h) { fprintf(stderr, "dihedral closure too big\n"); return 2; } H[cnt++] = y; changed = 1; }
                }
            }
        }
        if (cnt != h) { fprintf(stderr, "dihedral closure order %d != %d (not normalised by s)\n", cnt, h); return 2; }
    }

    /* left H-coset labels (shared by both sides) */
    NL = MG / h; repk = malloc(sizeof(int) * NL); int nl = 0;
    for (int k = 0; k < NKEYS; k++) {
        if (labkey[k] >= 0 || !valid_key(k)) continue;
        E z = dec(k);
        for (int i = 0; i < h; i++) labkey[kof(mul(H[i], z))] = nl;
        repk[nl++] = k;
    }
    if (nl != NL) { fprintf(stderr, "coset count mismatch\n"); return 2; }

    /* regular double cosets (size h*h): representatives */
    int *rl = malloc(sizeof(int) * (size_t)(NKEYS / (h * h) + 16)); long nrl = 0;
    int *dk = malloc(sizeof(int) * (size_t)h * h * R);
    for (int k = 0; k < NKEYS; k++) {
        if (!valid_key(k) || stampk[k]) continue;
        int cid = (int)(nrl + 1); /* stamp only for enumeration: use large offset */
        int cnt = 0; E z = dec(k);
        for (int i = 0; i < h; i++) for (int j = 0; j < h; j++) {
            int kk = kof(mul(mul(H[i], z), H[j]));
            if (stampk[kk] != -1 - k) { stampk[kk] = -1 - k; cnt++; }
        }
        (void)cid;
        if (cnt == h * h) rl[nrl++] = k;
    }
    memset(stampk, 0, sizeof(int) * NKEYS);
    fprintf(stderr, "q=%d PSL=%d d=%d h=%d R=%d T=%d |G|=%d N=%d lambda=%.4f regular double cosets=%ld H=%s\n",
            Q, PSLF, dg, h, R, T, MG, NL, 0.0, nrl, dihedral ? "dihedral" : "cyclic");
    if (nrl < R) { fprintf(stderr, "too few regular double cosets\n"); return 2; }

    unsigned char *dist = malloc(2 * (size_t)NL);
    int *queue = malloc(sizeof(int) * 2 * (size_t)NL);
    int *labA = calloc(NL, sizeof(int)), *labB = calloc(NL, sizeof(int));
    E *ea = malloc(sizeof(E) * dg), *db = malloc(sizeof(E) * dg);
    long *hist = calloc(2 * (size_t)NL + 1, sizeof(long));
    srand(seed);
    long nzero = 0; double t0 = now();
    int *reps = malloc(sizeof(int) * R);
    for (int ci = 0; ci < K; ci++) {
        /* R distinct random regular double cosets */
        for (int r = 0; r < R; r++) {
            int ok;
            do {
                reps[r] = rl[(long)(((unsigned long)rand() << 16 ^ (unsigned long)rand()) % (unsigned long)nrl)];
                ok = 1;
                for (int s2 = 0; s2 < r; s2++) if (reps[s2] == reps[r]) ok = 0;
            } while (!ok);
        }
        /* D keys */
        int cnt = 0, cid = ci + 1;
        for (int r = 0; r < R; r++) {
            E z = dec(reps[r]);
            for (int i = 0; i < h; i++) for (int j = 0; j < h; j++) {
                int kk = kof(mul(mul(H[i], z), H[j]));
                if (stampk[kk] != cid) { stampk[kk] = cid; dk[cnt++] = kk; }
            }
        }
        if (cnt != dg * h) { fprintf(stderr, "union size %d != %d (double cosets overlap)\n", cnt, dg * h); continue; }
        /* B->A steps: one d in D per left coset; A->B steps: inverses of such d, one per left coset */
        int nb = 0, na = 0;
        for (int i = 0; i < cnt; i++) {
            int lab = labkey[dk[i]];
            if (labA[lab] != cid) { labA[lab] = cid; db[nb++] = dec(dk[i]); }
        }
        for (int i = 0; i < cnt; i++) {
            E e = einv(dec(dk[i]));
            int lab = labkey[kof(e)];
            if (labB[lab] != cid) { labB[lab] = cid; ea[na++] = e; }
        }
        if (na != dg || nb != dg) { fprintf(stderr, "degree error %d %d\n", na, nb); return 3; }

        if (getenv("CHECK") && ci == 0) {
            long bad = 0, edges = 0;
            for (int a = 0; a < NL; a++) {
                E x = dec(repk[a]);
                for (int j = 0; j < na; j++) {
                    int b = labkey[kof(mul(ea[j], x))]; edges++;
                    E y = dec(repk[b]); int found = 0;
                    for (int i = 0; i < nb; i++) if (labkey[kof(mul(db[i], y))] == a) { found = 1; break; }
                    if (!found) bad++;
                }
            }
            fprintf(stderr, "CHECK: edges=%ld (expect %ld) asymmetric=%ld\n", edges, (long)NL * dg, bad);
        }

        /* BFS from the A root */
        memset(dist, 255, 2 * (size_t)NL);
        int root = labkey[IDKEY];
        long qh = 0, qt = 0;
        dist[root] = 0; queue[qt++] = root;
        while (qh < qt) {
            int v = queue[qh++]; int dv = dist[v];
            if (dv >= T) continue;
            if (v < NL) {
                E x = dec(repk[v]);
                for (int j = 0; j < dg; j++) {
                    int w = NL + labkey[kof(mul(ea[j], x))];
                    if (dist[w] == 255) { dist[w] = dv + 1; queue[qt++] = w; }
                }
            } else {
                E y = dec(repk[v - NL]);
                for (int i = 0; i < dg; i++) {
                    int w = labkey[kof(mul(db[i], y))];
                    if (dist[w] == 255) { dist[w] = dv + 1; queue[qt++] = w; }
                }
            }
        }
        long uncB = 0, uncA = 0;
        for (int l = 0; l < NL; l++) {
            if (dist[NL + l] == 255 || dist[NL + l] > T - 1) uncB++;
            if (l != root && (dist[l] == 255 || dist[l] > T)) uncA++;
        }
        hist[uncB]++;
        if (uncB == 0 && uncA == 0) nzero++;
        printf("cand %d reps", ci);
        for (int r = 0; r < R; r++) printf(" %d", reps[r]);
        printf(" uncB %ld uncA %ld\n", uncB, uncA);
        fflush(stdout);
        if ((ci + 1) % 50 == 0 || ci + 1 == K)
            fprintf(stderr, "  %d/%d done, %.1f s, diameter-ok so far: %ld\n", ci + 1, K, now() - t0, nzero);
    }
    fprintf(stderr, "summary: runs=%d diameter-ok=%ld\n", K, nzero);
    return 0;
}
