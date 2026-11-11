/* bicm: bi-coset graphs of G = Z_m x|_r Z_k (k = h*kp) with point stabiliser H = <(0,kp)> of order h.
 * Group law (a,j)(b,l) = (a + r^j b, j + l).  Right cosets of H are labelled (a, j mod kp).
 * Vertices A: a + m*j (j in Z_kp); B: nv + a + m*j, nv = m*kp.
 * Edges: (a,j)_A ~ (a + r^j u, j + v)_B for (u,v) in N0 (4 pairs, u in Z_m, v in Z_kp).
 * N0 is invariant under (u,v) -> (zeta u, v), zeta = r^kp mod m; then the graph is G-invariant and
 * both sides are vertex-transitive, so two roots (A: 0, B: nv) decide the diameter (D = 9).
 *
 * Normal form: scaling u -> c u (c a unit mod m) and shifting v -> v + t are isomorphisms.  Let s* be the largest
 * zeta-orbit size among the four pairs.  Some pair (u,v) of size s* can be moved to (d,0), d = gcd(u,m) | m, so
 * every N0 is covered by: first object = orbit of d at v=0 (one per distinct orbit), rest = all completions with
 * objects of size <= s*.  N0 made only of zeta-fixed u (s* = 1) are disconnected (a stays in a coset of
 * Fix(zeta) != Z_m) and are skipped.
 *
 * Usage: bicm FAMFILE START MODE S BUDGET
 *   FAMFILE lines "m kp h r gG" (gG = |G/G'|, echoed only).  MODE exh: all normal-form N0; smp: S of them
 *   chosen uniformly (reservoir).  Stops after BUDGET seconds and prints NEXT idx.
 * Output per family: "RES idx m kp h r zeta gG status ncand neval best ties N0(8 ints: u0 v0 u1 v1 ...)"
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#ifndef DIAM
#define DIAM 9
#endif
static int m, kp, h, r, nv, n;
static int *Rj;      /* r^j mod m, j < kp */
static int *adj;     /* 4 per vertex; A: 0..nv-1, B: nv..n-1 */
static int *dist, *queue;
static long best, ties, neval;
static int bestN0[8];

static double now_s(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }

static int *RU;      /* RU[j*4+i] = r^j * u_i mod m */
static int *JV;      /* JV[j*4+i] = (j + v_i) mod kp */
static int *JM;      /* JM[l*4+i] = (l - v_i) mod kp */
static void build(const int *N0) {
    for (int i = 0; i < 4; i++) {
        int u = N0[2 * i], v = N0[2 * i + 1];
        for (int j = 0; j < kp; j++) {
            RU[j * 4 + i] = (int)(((long)Rj[j] * u) % m);
            int l = j + v; if (l >= kp) l -= kp;
            JV[j * 4 + i] = l;
            int jm = j - v; if (jm < 0) jm += kp;
            JM[j * 4 + i] = jm;
        }
    }
    for (int j = 0; j < kp; j++) for (int a = 0; a < m; a++) {
        int x = a + m * j;
        for (int i = 0; i < 4; i++) {
            int b = a + RU[j * 4 + i]; if (b >= m) b -= m;
            adj[4 * x + i] = nv + b + m * JV[j * 4 + i];
        }
    }
    /* B side: y = (b,l); A-neighbour (b - r^j u, j) with j = l - v_i */
    for (int l = 0; l < kp; l++) for (int b = 0; b < m; b++) {
        int y = nv + b + m * l;
        for (int i = 0; i < 4; i++) {
            int j = JM[l * 4 + i];
            int a = b - RU[j * 4 + i]; if (a < 0) a += m;
            adj[4 * y + i] = a + m * j;
        }
    }
}

static int bfs_far(int root) {
    for (int i = 0; i < n; i++) dist[i] = -1;
    int hd = 0, tl = 0; queue[tl++] = root; dist[root] = 0;
    while (hd < tl) {
        int x = queue[hd++];
        if (dist[x] >= DIAM) continue;
        for (int i = 0; i < 4; i++) {
            int y = adj[4 * x + i];
            if (dist[y] < 0) { dist[y] = dist[x] + 1; queue[tl++] = y; }
        }
    }
    return n - tl;
}

static void evaluate(const int *N0) {
    build(N0);
    neval++;
    long fa = bfs_far(0);
    if (fa > best) return;
    long fb = bfs_far(nv);
    long tot = fa + fb;
    if (tot < best) { best = tot; ties = 1; memcpy(bestN0, N0, sizeof(int) * 8); }
    else if (tot == best) ties++;
}

/* zeta-orbits of Z_m */
static int norb, *orb_of, *orb_size, *orb_start, *orb_elems, *orb_seen;
static int kpv;
static int *objs_sz1; static int nsz1;

/* sampling state */
static int MODE_SMP; static long S_SMP; static long seen_cnt, resv_n;
static int *resv;
static unsigned long long rng_state = 88172645463325252ULL;
static unsigned long long xr(void) { rng_state ^= rng_state << 13; rng_state ^= rng_state >> 7; rng_state ^= rng_state << 17; return rng_state; }

static void emit(const int *N0) {
    seen_cnt++;
    if (!MODE_SMP) { evaluate(N0); return; }
    if (resv_n < S_SMP) { memcpy(resv + 8 * resv_n, N0, sizeof(int) * 8); resv_n++; }
    else {
        unsigned long long k = xr() % (unsigned long long)seen_cnt;
        if (k < (unsigned long long)S_SMP) memcpy(resv + 8 * k, N0, sizeof(int) * 8);
    }
}

/* put orbit O (all its u, with v) into N0 starting at pair slot */
static void put_orbit(int *N0, int slot, int O, int v) {
    int sz = orb_size[O];
    for (int t = 0; t < sz; t++) { N0[2 * (slot + t)] = orb_elems[orb_start[O] + t]; N0[2 * (slot + t) + 1] = v; }
}

int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: bicm FAMFILE START MODE S BUDGET\n"); return 1; }
    FILE *ff = fopen(argv[1], "r");
    if (!ff) { perror("fam"); return 1; }
    int start = atoi(argv[2]);
    MODE_SMP = strcmp(argv[3], "smp") == 0;
    S_SMP = atol(argv[4]);
    double budget = atof(argv[5]);
    double t0 = now_s();
    char line[256];
    int idx = 0;
    /* skip to start */
    while (idx < start && fgets(line, sizeof line, ff)) idx++;
    if (idx < start) { printf("NEXT %d\n", idx); return 0; }
    int mm, kk, hh, rr; long gG;
    while (fgets(line, sizeof line, ff)) {
        if (sscanf(line, "%d %d %d %d %ld", &mm, &kk, &hh, &rr, &gG) != 5) { idx++; continue; }
        if (now_s() - t0 > budget) break;
        m = mm; kp = kk; h = hh; r = rr; nv = m * kp; n = 2 * nv; kpv = kp;
        Rj = malloc(sizeof(int) * kp);
        long p = 1 % m;
        for (int j = 0; j < kp; j++) { Rj[j] = (int)p; p = p * r % m; }
        long zeta = 1 % m;
        for (int j = 0; j < kp; j++) zeta = zeta * r % m;      /* r^kp */
        long chk = zeta; for (int t = 1; t < h; t++) chk = chk * zeta % m;
        if (zeta == 1 % m || chk != 1 % m) {
            printf("RES %d %d %d %d %d %ld %ld skip 0 0 -1 0\n", idx, m, kp, h, r, zeta, gG);
            free(Rj); idx++; continue;
        }
        orb_of = malloc(sizeof(int) * m); orb_size = malloc(sizeof(int) * m); orb_start = malloc(sizeof(int) * m);
        orb_elems = malloc(sizeof(int) * m); orb_seen = malloc(sizeof(int) * m);
        for (int u = 0; u < m; u++) orb_of[u] = -1;
        norb = 0; int pos = 0;
        for (int u = 0; u < m; u++) {
            if (orb_of[u] >= 0) continue;
            orb_start[norb] = pos; int x = u, sz = 0;
            do { orb_of[x] = norb; orb_elems[pos++] = x; sz++; x = (int)((long)x * zeta % m); } while (x != u);
            orb_size[norb] = sz; orb_seen[norb] = 0; norb++;
        }
        int nobj = norb * kp;
        objs_sz1 = malloc(sizeof(int) * (nobj + 1)); nsz1 = 0;
        for (int O = 0; O < norb; O++) if (orb_size[O] == 1) for (int v = 0; v < kp; v++) objs_sz1[nsz1++] = O * kp + v;
        int sl[4], nsl = 0;
        for (int s = 4; s >= 2; s--) { for (int O = 0; O < norb; O++) if (orb_size[O] == s) { sl[nsl++] = s; break; } }
        int N0[8];
        seen_cnt = 0; resv_n = 0;
        resv = MODE_SMP ? malloc(sizeof(int) * 8 * (S_SMP + 1)) : NULL;
        best = 1L << 40; ties = 0; neval = 0;
        adj = malloc(sizeof(int) * 4 * n); dist = malloc(sizeof(int) * n); queue = malloc(sizeof(int) * n);
        RU = malloc(sizeof(int) * 4 * kp); JV = malloc(sizeof(int) * 4 * kp); JM = malloc(sizeof(int) * 4 * kp);
        for (int si = 0; si < nsl; si++) {
            int s = sl[si];
            for (int O = 0; O < norb; O++) orb_seen[O] = 0;
            for (int d = 1; d <= m; d++) {
                if (m % d) continue;
                int u = d % m;
                int O = orb_of[u];
                if (orb_size[O] != s || orb_seen[O]) continue;
                orb_seen[O] = 1;
                int R = 4 - s;
                int o1 = O * kp;               /* object (O, v=0) */
                put_orbit(N0, 0, O, 0);
                if (R == 0) emit(N0);
                else if (R == 1) {
                    for (int q = 0; q < nsz1; q++) {
                        int o2 = objs_sz1[q];
                        if (o2 == o1) continue;
                        put_orbit(N0, 0, O, 0);
                        put_orbit(N0, s, o2 / kp, o2 % kp);
                        emit(N0);
                    }
                } else { /* R == 2 */
                    for (int O2 = 0; O2 < norb; O2++) {
                        if (orb_size[O2] != 2) continue;
                        for (int v = 0; v < kp; v++) {
                            if (O2 * kp + v == o1) continue;
                            put_orbit(N0, 0, O, 0);
                            put_orbit(N0, 2, O2, v);
                            emit(N0);
                        }
                    }
                    for (int q = 0; q < nsz1; q++) for (int q2 = q + 1; q2 < nsz1; q2++) {
                        int oa = objs_sz1[q], ob = objs_sz1[q2];
                        if (oa == o1 || ob == o1) continue;
                        put_orbit(N0, 0, O, 0);
                        put_orbit(N0, 2, oa / kp, oa % kp);
                        put_orbit(N0, 3, ob / kp, ob % kp);
                        emit(N0);
                    }
                }
            }
        }
        if (MODE_SMP) for (long q = 0; q < resv_n; q++) evaluate(resv + 8 * q);
        printf("RES %d %d %d %d %d %ld %ld ok %ld %ld %ld %ld", idx, m, kp, h, r, zeta, gG, seen_cnt, neval, best, ties);
        if (neval > 0) for (int i = 0; i < 8; i++) printf(" %d", bestN0[i]);
        printf("\n");
        fflush(stdout);
        free(resv); free(objs_sz1); free(orb_of); free(orb_size); free(orb_start); free(orb_elems); free(orb_seen);
        free(adj); free(dist); free(queue); free(Rj); free(RU); free(JV); free(JM);
        idx++;
    }
    printf("NEXT %d\n", idx);
    return 0;
}
