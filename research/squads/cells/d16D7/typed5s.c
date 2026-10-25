/* typed5s.c: the typed-level hexagon construction of typed5.c, made invariant under a collineation group G = <g> of
   H(q) that acts semiregularly on points and lines (g in SL(3,q) acting as (v,a,w) -> (gv, a, g^-T w), see collin.py).
   cell-16-7 session (resume), 2026-10-25.

   G acts on every level in the same way and cyclically on each hub orbit, so (x, j) -> (g x, j), hub (k,t) -> (k,t+1)
   is an automorphism of the graph and BFS from one vertex per orbit gives the exact diameter (apsp_aut.c checks the
   automorphism edge by edge first). What has to be G-invariant: the freed sets R_H (non-collinear points) and R_L
   (non-concurrent lines) are unions of G-orbits; the bijections of the unfriendly transitions are G-equivariant
   (orbit -> orbit with an offset); hubs come in G-orbits (hub (k,t) is joined to g^(t+c) b in level j); the hub graph
   is a voltage graph over Z_m on the hub orbits. Friendly transitions use the identity, which commutes with G.

   Construction recap (typed5.c): levels j in Z_L, types (H: class A = points; D: class A = lines); matchings
   M_k^(j): A_j -> B_{j+k}, k = 1..r; friendly (t_j != t_{j+k}) = identity, freed on R_H / R_L; unfriendly = equivariant
   bijection, nothing freed. Line-side hubs take one free A-slot per level, point-side hubs one free B-slot per level.

   Usage:
     typed5s make HEXBIN TYPES SEED HUBDEG RHFILE RLFILE OUT.sol [KMAXORB]     choose maps, hubs, hub graph; write .sol
     typed5s edges HEXBIN SOL OUT.edges OUT.aut                               build the graph from .sol
       OUT.edges: apsp.c format ("n" then "u v"); OUT.aut: n int32, the automorphism (vertex -> image)
   .sol format (text): "typed5s q N L TYPES m n", "gmat" + 9 entries of g (row-major), "RH k" + k orbit
   representatives (points), "RL k" + reps (lines), for each unfriendly transition "unf j k c" + c lines "src dst off"
   (sigma(g^t src) = g^(t+off) dst), "hubB K" + K lines of L slots "rep off" (line-side hub (k,t) ~ (g^(t+off) rep, j)),
   "hubA K" + K lines (point-side hubs, B-slots), "hg e" + e lines "kB kA c" (hub B (kB,t) ~ hub A (kA, t+c)).
   Vertex ids: (point p, level j) = 2Nj + p, (line l, level j) = 2Nj + N + l, line-side hub (k,t) = 2NL + mk + t,
   point-side hub (k,t) = 2NL + m KB + mk + t. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

static int q, N, Q1, L, R, m;
static int32_t *LP, *PL;
static uint8_t *X;
static int64_t *pcode;
static int g[3][3], gi[3][3];
static int *perm[2], *orb[2], *pos[2], *rep[2], no[2];  /* kind 0 points, 1 lines: G action, orbit id, position, reps */
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline int rndi(int n) { return (int)(rnd() % (uint64_t)n); }
static void shuffle(int *a, int n) { for (int i = n - 1; i > 0; i--) { int j = rndi(i + 1); int t = a[i]; a[i] = a[j]; a[j] = t; } }

static void load_hex(const char *fn) {
    FILE *f = fopen(fn, "rb"); if (!f) { perror(fn); exit(1); }
    int32_t h[3]; if (fread(h, 4, 3, f) != 3) exit(1);
    q = h[0]; N = h[1]; Q1 = q + 1;
    LP = malloc(sizeof(int32_t) * (size_t)N * Q1); if (fread(LP, 4, (size_t)N * Q1, f) != (size_t)N * Q1) exit(1);
    X = malloc((size_t)N * 7); if (fread(X, 1, (size_t)N * 7, f) != (size_t)N * 7) exit(1);
    fclose(f);
    PL = malloc(sizeof(int32_t) * (size_t)N * Q1); int *c = calloc(N, sizeof(int));
    for (int l = 0; l < N; l++) for (int k = 0; k < Q1; k++) { int p = LP[(size_t)l * Q1 + k]; PL[(size_t)p * Q1 + c[p]++] = l; }
    free(c);
    pcode = malloc(sizeof(int64_t) * N);
    for (int p = 0; p < N; p++) { int64_t cc = 0; for (int i = 6; i >= 0; i--) cc = cc * q + X[(size_t)p * 7 + i]; pcode[p] = cc; if (p && pcode[p] <= pcode[p - 1]) { fprintf(stderr, "points not in code order\n"); exit(1); } }
}
static int md(long a) { a %= q; return a < 0 ? (int)a + q : (int)a; }
static int inv(int a) { for (int b = 1; b < q; b++) if (md((long)a * b) == 1) return b; return 0; }
static int lookup(int *v) {
    int s = -1; for (int i = 0; i < 7; i++) if (v[i]) { s = inv(v[i]); break; }
    for (int i = 0; i < 7; i++) v[i] = md((long)v[i] * s);
    int64_t cc = 0; for (int i = 6; i >= 0; i--) cc = cc * q + v[i];
    int lo = 0, hi = N - 1; while (lo <= hi) { int mid = (lo + hi) / 2; if (pcode[mid] == cc) return mid; if (pcode[mid] < cc) lo = mid + 1; else hi = mid - 1; }
    fprintf(stderr, "image is not a point\n"); exit(1);
}
/* G action from the matrix g: v -> g v, a -> a, w -> g^-T w */
static void build_action(void) {
    /* inverse of g mod q (adjugate / det) */
    long det = (long)g[0][0] * (g[1][1] * g[2][2] - g[1][2] * g[2][1]) - (long)g[0][1] * (g[1][0] * g[2][2] - g[1][2] * g[2][0]) + (long)g[0][2] * (g[1][0] * g[2][1] - g[1][1] * g[2][0]);
    int di = inv(md(det)); if (!di) { fprintf(stderr, "singular g\n"); exit(1); }
    for (int i = 0; i < 3; i++) for (int j = 0; j < 3; j++) {
        int a1 = (j + 1) % 3, a2 = (j + 2) % 3, b1 = (i + 1) % 3, b2 = (i + 2) % 3;   /* cofactor of (j,i) -> adj(i,j) */
        long cof = (long)g[a1][b1] * g[a2][b2] - (long)g[a1][b2] * g[a2][b1];
        gi[i][j] = md(cof * di);
    }
    for (int i = 0; i < 3; i++) for (int j = 0; j < 3; j++) { long s = 0; for (int k = 0; k < 3; k++) s += (long)g[i][k] * gi[k][j]; if (md(s) != (i == j)) { fprintf(stderr, "inverse failed\n"); exit(1); } }
    perm[0] = malloc(sizeof(int) * N); perm[1] = malloc(sizeof(int) * N);
    for (int p = 0; p < N; p++) {
        int x[7], y[7]; for (int i = 0; i < 7; i++) x[i] = X[(size_t)p * 7 + i];
        for (int i = 0; i < 3; i++) { long s = 0; for (int k = 0; k < 3; k++) s += (long)g[i][k] * x[k]; y[i] = md(s); }
        y[3] = x[3];
        for (int i = 0; i < 3; i++) { long s = 0; for (int k = 0; k < 3; k++) s += (long)gi[k][i] * x[4 + k]; y[4 + i] = md(s); }   /* g^-T w */
        perm[0][p] = lookup(y);
    }
    for (int l = 0; l < N; l++) {
        int a = perm[0][LP[(size_t)l * Q1]], b = perm[0][LP[(size_t)l * Q1 + 1]], img = -1;
        for (int u = 0; u < Q1 && img < 0; u++) for (int v = 0; v < Q1; v++) if (PL[(size_t)a * Q1 + u] == PL[(size_t)b * Q1 + v]) { img = PL[(size_t)a * Q1 + u]; break; }
        if (img < 0) { fprintf(stderr, "g is not a collineation\n"); exit(1); }
        for (int k = 0; k < Q1; k++) { int pp = perm[0][LP[(size_t)l * Q1 + k]], ok = 0; for (int u = 0; u < Q1; u++) if (PL[(size_t)pp * Q1 + u] == img) ok = 1; if (!ok) { fprintf(stderr, "g is not a collineation\n"); exit(1); } }
        perm[1][l] = img;
    }
    m = 0;
    for (int kd = 0; kd < 2; kd++) {
        orb[kd] = malloc(sizeof(int) * N); pos[kd] = malloc(sizeof(int) * N); rep[kd] = malloc(sizeof(int) * N); no[kd] = 0;
        for (int i = 0; i < N; i++) orb[kd][i] = -1;
        for (int s = 0; s < N; s++) if (orb[kd][s] < 0) {
            int x = s, t = 0; while (orb[kd][x] < 0) { orb[kd][x] = no[kd]; pos[kd][x] = t++; x = perm[kd][x]; }
            if (x != s) { fprintf(stderr, "not a permutation\n"); exit(1); }
            if (m == 0) m = t; else if (t != m) { fprintf(stderr, "G is not semiregular (orbit %d vs %d)\n", t, m); exit(1); }
            rep[kd][no[kd]++] = s;   /* s is the smallest element of its orbit */
        }
    }
}
/* element g^t rep(o) */
static int *orbel[2];
static void build_orbel(void) {
    for (int kd = 0; kd < 2; kd++) { orbel[kd] = malloc(sizeof(int) * N); for (int x = 0; x < N; x++) orbel[kd][(size_t)orb[kd][x] * m + pos[kd][x]] = x; }
}
static inline int mm(long a) { a %= m; return a < 0 ? (int)(a + m) : (int)a; }
static inline int el(int kd, int o, int t) { t %= m; if (t < 0) t += m; return orbel[kd][(size_t)o * m + t]; }

static int ty[64];
static inline int akind(int j) { return ty[j]; }        /* class A of level j: points (0) for H, lines (1) for D */
static inline int bkind(int j) { return 1 - ty[j]; }

int main(int argc, char **argv) {
    if (argc < 2) { fprintf(stderr, "usage: see header\n"); return 2; }
    int make = !strcmp(argv[1], "make");
    if (make && argc < 9) { fprintf(stderr, "typed5s make HEXBIN TYPES SEED HUBDEG RHFILE RLFILE OUT.sol [KMAXORB]\n"); return 2; }
    if (!make && argc < 6) { fprintf(stderr, "typed5s edges HEXBIN SOL OUT.edges OUT.aut\n"); return 2; }
    load_hex(argv[2]);
    char types[64]; int seedv = 0, hubdeg = 0, kmax = 0;
    int nRH = 0, nRL = 0, *RHo = malloc(sizeof(int) * N), *RLo = malloc(sizeof(int) * N);
    FILE *fs = NULL;
    if (make) {
        strcpy(types, argv[3]); seedv = atoi(argv[4]); hubdeg = atoi(argv[5]); kmax = argc > 9 ? atoi(argv[9]) : 0;
        /* the generator: the order-61 element used by collin.py for q = 13 (other q: pass GMAT env "a00 a01 ... a22") */
        const char *gm = getenv("GMAT"); int gv[9] = {5, 2, 0, 12, 5, 2, 12, 0, 5};
        if (gm) sscanf(gm, "%d %d %d %d %d %d %d %d %d", gv, gv + 1, gv + 2, gv + 3, gv + 4, gv + 5, gv + 6, gv + 7, gv + 8);
        for (int i = 0; i < 9; i++) g[i / 3][i % 3] = gv[i];
    } else {
        fs = fopen(argv[3], "r"); if (!fs) { perror(argv[3]); return 1; }
        int qq, NN; long nn;
        if (fscanf(fs, "typed5s %d %d %d %63s %d %ld", &qq, &NN, &L, types, &m, &nn) != 6 || qq != q || NN != N) { fprintf(stderr, "bad sol header\n"); return 1; }
        char w[32]; if (fscanf(fs, "%31s", w) != 1 || strcmp(w, "gmat")) return 1;
        for (int i = 0; i < 9; i++) if (fscanf(fs, "%d", &g[i / 3][i % 3]) != 1) return 1;
    }
    L = (int)strlen(types); R = (L - 1) / 2;
    for (int j = 0; j < L; j++) ty[j] = types[j] == 'D';
    int msol = m;
    build_action(); build_orbel();
    if (!make && msol != m) { fprintf(stderr, "orbit size mismatch\n"); return 1; }
    fprintf(stderr, "q=%d N=%d L=%d types=%s |G|=%d orbits %d/%d\n", q, N, L, types, m, no[0], no[1]);
    /* unfriendly maps: umap[j][k][o] = (dst orbit, offset) */
    int *usrc[64][4], *udst[64][4], *uoff[64][4];
    int KB = 0, KA = 0, *hBrep = NULL, *hBoff = NULL, *hArep = NULL, *hAoff = NULL, ne = 0, *eB = NULL, *eA = NULL, *eC = NULL;
    if (make) {
        rs ^= (uint64_t)seedv * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 10; i++) rnd();
        /* read freed sets (element lists, must be unions of orbits) */
        for (int kd = 0; kd < 2; kd++) {
            FILE *f = fopen(argv[6 + kd], "r"); if (!f) { perror(argv[6 + kd]); return 1; }
            int *cnt = calloc(no[kd], sizeof(int)), x; char buf[256];
            while (fgets(buf, sizeof buf, f)) if (buf[0] != '#' && sscanf(buf, "%d", &x) == 1) { if (x < 0 || x >= N) return 1; cnt[orb[kd][x]]++; }
            fclose(f);
            int *outo = kd == 0 ? RHo : RLo, n = 0;
            for (int o = 0; o < no[kd]; o++) { if (cnt[o] == m) outo[n++] = o; else if (cnt[o]) { fprintf(stderr, "set %d is not a union of orbits\n", kd); return 1; } }
            if (kd == 0) nRH = n; else nRL = n;
            free(cnt);
        }
    } else {
        char w[32]; int k;
        if (fscanf(fs, "%31s %d", w, &k) != 2 || strcmp(w, "RH")) return 1;
        for (int i = 0; i < k; i++) { int x; if (fscanf(fs, "%d", &x) != 1) return 1; RHo[nRH++] = orb[0][x]; }
        if (fscanf(fs, "%31s %d", w, &k) != 2 || strcmp(w, "RL")) return 1;
        for (int i = 0; i < k; i++) { int x; if (fscanf(fs, "%d", &x) != 1) return 1; RLo[nRL++] = orb[1][x]; }
    }
    char *inR[2]; inR[0] = calloc(N, 1); inR[1] = calloc(N, 1);
    for (int i = 0; i < nRH; i++) for (int t = 0; t < m; t++) inR[0][el(0, RHo[i], t)] = 1;
    for (int i = 0; i < nRL; i++) for (int t = 0; t < m; t++) inR[1][el(1, RLo[i], t)] = 1;
    /* check the set conditions */
    for (int kd = 0; kd < 2; kd++) {
        const int32_t *A = kd == 0 ? PL : LP, *B = kd == 0 ? LP : PL;
        for (int x = 0; x < N; x++) if (inR[kd][x]) for (int a = 0; a < Q1; a++) { int y = A[(size_t)x * Q1 + a]; for (int b = 0; b < Q1; b++) { int z = B[(size_t)y * Q1 + b]; if (z != x && inR[kd][z]) { fprintf(stderr, "freed set %d not independent\n", kd); return 1; } } }
    }
    fprintf(stderr, "|R_H| = %d orbits = %d points, |R_L| = %d orbits = %d lines\n", nRH, nRH * m, nRL, nRL * m);
    for (int j = 0; j < L; j++) for (int k = 1; k <= R; k++) {
        int j2 = (j + k) % L, a = akind(j), b = bkind(j2);
        usrc[j][k] = udst[j][k] = uoff[j][k] = NULL;
        if (a == b) continue;
        usrc[j][k] = malloc(sizeof(int) * no[a]); udst[j][k] = malloc(sizeof(int) * no[a]); uoff[j][k] = malloc(sizeof(int) * no[a]);
        if (make) {
            int *pi = malloc(sizeof(int) * no[b]); for (int i = 0; i < no[b]; i++) pi[i] = i; shuffle(pi, no[b]);
            for (int o = 0; o < no[a]; o++) { usrc[j][k][o] = o; udst[j][k][o] = pi[o]; uoff[j][k][o] = rndi(m); }
            free(pi);
        } else {
            char w[32]; int jj, kk, c;
            if (fscanf(fs, "%31s %d %d %d", w, &jj, &kk, &c) != 4 || strcmp(w, "unf") || jj != j || kk != k || c != no[a]) { fprintf(stderr, "bad unf block\n"); return 1; }
            char *seen = calloc(no[a], 1), *seenb = calloc(no[b], 1);
            for (int i = 0; i < c; i++) { int s, d, off; if (fscanf(fs, "%d %d %d", &s, &d, &off) != 3) return 1;
                int os = orb[a][s], od = orb[b][d]; if (seen[os] || seenb[od]) { fprintf(stderr, "unf not a bijection\n"); return 1; }
                seen[os] = seenb[od] = 1;
                /* sigma(g^t s) = g^(t+off) d; store relative to the orbit representatives */
                usrc[j][k][os] = os; udst[j][k][os] = od; uoff[j][k][os] = mm((long)off + pos[b][d] - pos[a][s]);
            }
            free(seen); free(seenb);
        }
    }
    /* free slots per level (as orbit lists), for hubs */
    int *slA[64], nA[64], *slB[64], nB[64];
    for (int j = 0; j < L; j++) { slA[j] = malloc(sizeof(int) * 2 * R * no[0]); slB[j] = malloc(sizeof(int) * 2 * R * no[0]); nA[j] = nB[j] = 0; }
    for (int j = 0; j < L; j++) for (int k = 1; k <= R; k++) {
        int j2 = (j + k) % L, a = akind(j), b = bkind(j2);
        if (a != b) continue;
        int nr = a == 0 ? nRH : nRL, *ro = a == 0 ? RHo : RLo;
        for (int i = 0; i < nr; i++) { slA[j][nA[j]++] = ro[i]; slB[j2][nB[j2]++] = ro[i]; }
    }
    if (make) {
        KB = KA = 1 << 30;
        for (int j = 0; j < L; j++) { if (nA[j] < KB) KB = nA[j]; if (nB[j] < KA) KA = nB[j]; }
        if (kmax > 0) { if (KB > kmax) KB = kmax; if (KA > kmax) KA = kmax; }
        hBrep = malloc(sizeof(int) * KB * L); hBoff = malloc(sizeof(int) * KB * L);
        hArep = malloc(sizeof(int) * KA * L); hAoff = malloc(sizeof(int) * KA * L);
        for (int j = 0; j < L; j++) {
            shuffle(slA[j], nA[j]); shuffle(slB[j], nB[j]);
            /* the same orbit may appear twice in a list (two freed slots per element): give the two hub orbits
               different offsets so that no element gets two hubs in one orbit-slot... any offsets are fine because
               each element has as many free slots as copies of its orbit in the list */
            for (int k = 0; k < KB; k++) { hBrep[k * L + j] = slA[j][k]; hBoff[k * L + j] = rndi(m); }
            for (int k = 0; k < KA; k++) { hArep[k * L + j] = slB[j][k]; hAoff[k * L + j] = rndi(m); }
        }
        /* hub graph: hubdeg rounds of a random injection between hub orbits with random voltages */
        int KX = KB > KA ? KB : KA; eB = malloc(sizeof(int) * KX * hubdeg); eA = malloc(sizeof(int) * KX * hubdeg); eC = malloc(sizeof(int) * KX * hubdeg);
        int *dB = calloc(KB, sizeof(int)), *dA = calloc(KA, sizeof(int));
        for (int r2 = 0; r2 < hubdeg; r2++) {
            int *pa = malloc(sizeof(int) * KX), *pb = malloc(sizeof(int) * KX);
            for (int i = 0; i < KX; i++) { pa[i] = i % KB; pb[i] = i % KA; }
            shuffle(pa, KX); shuffle(pb, KX);
            for (int i = 0; i < KX; i++) {
                int u = pa[i], v = pb[i]; if (dB[u] >= hubdeg || dA[v] >= hubdeg) continue;
                int c = rndi(m), dup = 0;
                for (int e = 0; e < ne; e++) if (eB[e] == u && eA[e] == v && eC[e] == c) dup = 1;
                if (dup) continue;
                eB[ne] = u; eA[ne] = v; eC[ne] = c; ne++; dB[u]++; dA[v]++;
            }
            free(pa); free(pb);
        }
        /* write .sol */
        long n = 2L * N * L + (long)m * (KB + KA);
        FILE *fo = fopen(argv[8], "w"); if (!fo) { perror(argv[8]); return 1; }
        fprintf(fo, "typed5s %d %d %d %s %d %ld\n", q, N, L, types, m, n);
        fprintf(fo, "gmat"); for (int i = 0; i < 9; i++) fprintf(fo, " %d", g[i / 3][i % 3]); fprintf(fo, "\n");
        fprintf(fo, "RH %d\n", nRH); for (int i = 0; i < nRH; i++) fprintf(fo, "%d\n", rep[0][RHo[i]]);
        fprintf(fo, "RL %d\n", nRL); for (int i = 0; i < nRL; i++) fprintf(fo, "%d\n", rep[1][RLo[i]]);
        for (int j = 0; j < L; j++) for (int k = 1; k <= R; k++) {
            int j2 = (j + k) % L, a = akind(j), b = bkind(j2); if (a == b) continue;
            fprintf(fo, "unf %d %d %d\n", j, k, no[a]);
            for (int o = 0; o < no[a]; o++) fprintf(fo, "%d %d %d\n", rep[a][o], rep[b][udst[j][k][o]], uoff[j][k][o]);
        }
        fprintf(fo, "hubB %d\n", KB);
        for (int k = 0; k < KB; k++) { for (int j = 0; j < L; j++) fprintf(fo, "%s%d %d", j ? " " : "", rep[akind(j)][hBrep[k * L + j]], hBoff[k * L + j]); fprintf(fo, "\n"); }
        fprintf(fo, "hubA %d\n", KA);
        for (int k = 0; k < KA; k++) { for (int j = 0; j < L; j++) fprintf(fo, "%s%d %d", j ? " " : "", rep[bkind(j)][hArep[k * L + j]], hAoff[k * L + j]); fprintf(fo, "\n"); }
        fprintf(fo, "hg %d\n", ne); for (int e = 0; e < ne; e++) fprintf(fo, "%d %d %d\n", eB[e], eA[e], eC[e]);
        fclose(fo);
        fprintf(stderr, "wrote %s: n = %ld (+%ld), hub orbits %d + %d, hub-graph base edges %d\n", argv[8], n, (long)m * (KB + KA), KB, KA, ne);
        for (int j = 0; j < L; j++) fprintf(stderr, "  level %d (%c): free A-slot orbits %d, B-slot orbits %d\n", j, types[j], nA[j], nB[j]);
        return 0;
    }
    /* ---- edges mode: hubs and hub graph from the sol ---- */
    char w[32];
    if (fscanf(fs, "%31s %d", w, &KB) != 2 || strcmp(w, "hubB")) { fprintf(stderr, "bad hubB\n"); return 1; }
    hBrep = malloc(sizeof(int) * (KB + 1) * L); hBoff = malloc(sizeof(int) * (KB + 1) * L);
    for (int k = 0; k < KB; k++) for (int j = 0; j < L; j++) { int x, off; if (fscanf(fs, "%d %d", &x, &off) != 2) return 1; hBrep[k * L + j] = orb[akind(j)][x]; hBoff[k * L + j] = mm((long)off + pos[akind(j)][x]); }
    if (fscanf(fs, "%31s %d", w, &KA) != 2 || strcmp(w, "hubA")) { fprintf(stderr, "bad hubA\n"); return 1; }
    hArep = malloc(sizeof(int) * (KA + 1) * L); hAoff = malloc(sizeof(int) * (KA + 1) * L);
    for (int k = 0; k < KA; k++) for (int j = 0; j < L; j++) { int x, off; if (fscanf(fs, "%d %d", &x, &off) != 2) return 1; hArep[k * L + j] = orb[bkind(j)][x]; hAoff[k * L + j] = mm((long)off + pos[bkind(j)][x]); }
    if (fscanf(fs, "%31s %d", w, &ne) != 2 || strcmp(w, "hg")) { fprintf(stderr, "bad hg\n"); return 1; }
    eB = malloc(sizeof(int) * (ne + 1)); eA = malloc(sizeof(int) * (ne + 1)); eC = malloc(sizeof(int) * (ne + 1));
    for (int e = 0; e < ne; e++) if (fscanf(fs, "%d %d %d", &eB[e], &eA[e], &eC[e]) != 3 || eB[e] < 0 || eB[e] >= KB || eA[e] < 0 || eA[e] >= KA) { fprintf(stderr, "bad hg edge\n"); return 1; }
    fclose(fs);
    long NV0 = 2L * N * L, n = NV0 + (long)m * (KB + KA);
    #define VID(j, kind, x) ((long)(j) * 2 * N + (long)(kind) * N + (x))
    /* slot accounting: free slots per vertex = number of deleted matching edges there; hubs must not exceed it */
    int *freeA = calloc((size_t)L * N, sizeof(int)), *freeB = calloc((size_t)L * N, sizeof(int));
    for (int j = 0; j < L; j++) for (int k = 1; k <= R; k++) {
        int j2 = (j + k) % L, a = akind(j), b = bkind(j2); if (a != b) continue;
        for (int x = 0; x < N; x++) if (inR[a][x]) { freeA[(size_t)j * N + x]++; freeB[(size_t)j2 * N + x]++; }
    }
    FILE *f = fopen(argv[4], "w"); if (!f) { perror(argv[4]); return 1; }
    fprintf(f, "%ld\n", n); long ecount = 0;
    for (int j = 0; j < L; j++) for (int l = 0; l < N; l++) for (int k = 0; k < Q1; k++) { fprintf(f, "%ld %ld\n", VID(j, 0, LP[(size_t)l * Q1 + k]), VID(j, 1, l)); ecount++; }
    for (int j = 0; j < L; j++) for (int k = 1; k <= R; k++) {
        int j2 = (j + k) % L, a = akind(j), b = bkind(j2);
        for (int x = 0; x < N; x++) {
            int y;
            if (a == b) { if (inR[a][x]) continue; y = x; }
            else { int o = orb[a][x]; y = el(b, udst[j][k][o], pos[a][x] + uoff[j][k][o]); }
            fprintf(f, "%ld %ld\n", VID(j, a, x), VID(j2, b, y)); ecount++;
        }
    }
    for (int k = 0; k < KB; k++) for (int t = 0; t < m; t++) for (int j = 0; j < L; j++) {
        int a = akind(j), x = el(a, hBrep[k * L + j], t + hBoff[k * L + j]);
        if (--freeA[(size_t)j * N + x] < 0) { fprintf(stderr, "A-slot overused at level %d element %d\n", j, x); return 1; }
        fprintf(f, "%ld %ld\n", NV0 + (long)m * k + t, VID(j, a, x)); ecount++;
    }
    for (int k = 0; k < KA; k++) for (int t = 0; t < m; t++) for (int j = 0; j < L; j++) {
        int b = bkind(j), x = el(b, hArep[k * L + j], t + hAoff[k * L + j]);
        if (--freeB[(size_t)j * N + x] < 0) { fprintf(stderr, "B-slot overused at level %d element %d\n", j, x); return 1; }
        fprintf(f, "%ld %ld\n", NV0 + (long)m * (KB + k) + t, VID(j, b, x)); ecount++;
    }
    for (int e = 0; e < ne; e++) for (int t = 0; t < m; t++) { fprintf(f, "%ld %ld\n", NV0 + (long)m * eB[e] + t, NV0 + (long)m * (KB + eA[e]) + (t + eC[e]) % m); ecount++; }
    fclose(f);
    /* automorphism */
    int32_t *aut = malloc(sizeof(int32_t) * n);
    for (int j = 0; j < L; j++) for (int kd = 0; kd < 2; kd++) for (int x = 0; x < N; x++) aut[VID(j, kd, x)] = (int32_t)VID(j, kd, perm[kd][x]);
    for (long h = NV0; h < n; h++) { long r2 = h - NV0, k = r2 / m, t = r2 % m; aut[h] = (int32_t)(NV0 + k * m + (t + 1) % m); }
    FILE *fa = fopen(argv[5], "wb"); if (!fa || fwrite(aut, 4, n, fa) != (size_t)n) { perror(argv[5]); return 1; } fclose(fa);
    fprintf(stderr, "wrote %s: n = %ld, edges %ld (base %ld, +%ld hubs)\n", argv[4], n, ecount, NV0, n - NV0);
    return 0;
}
