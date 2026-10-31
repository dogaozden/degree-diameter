/* fsd.c: formula-only self-dual (bipartite Cayley) Haar search at diameter 5, any valency K.  No GAP, no table files.
 *
 * Group G = H x C_n3; element index e = h * n3 + l (h the index in H, l in Z_n3).  H is one of
 *   meta m k r : C_m : C_k = <x, y | x^m = y^k = 1, y x y^-1 = x^r>, x^i y^j = (i,j) has h = i*k + j and
 *                (i,j)(a,b) = (i + r^j a, j + b)   (the convention of ../selfdual-d5/records/build_metacyclic_haar.py)
 *   psl p      : PSL(2,p), p prime: matrices [[a,b],[c,d]] (ad - bc = 1) modulo -1, represented by the one whose first
 *                nonzero entry of (a,b) is in 1..(p-1)/2; h = 0 is the identity, then the others in lexicographic
 *                order of (a,b,c,d)
 *   sl p       : SL(2,p), p prime, every [[a,b],[c,d]] with ad - bc = 1; h = 0 the identity, then lexicographic.
 * Generators: meta x = (1,0), y = (0,1); psl/sl s = [[1,1],[0,1]], t = [[0,1],[-1,0]]; and z = (e, 1) if n3 > 1.
 *
 * Self-dual family (../selfdual-d5/README.md): G^ = G u G t, t x t^-1 = beta(x), t^2 = c; S = T t^-1 for an
 * inverse-closed T in G t of size K with t in T; then psi(S) = S for psi(x) = c^-1 beta(x)^-1, H(G,S) = Cay(G^, T)
 * and only X X = G (X = S^-1 S) has to be checked.
 * Records: for every automorphism beta of the formula family below with beta^2 inner (coset representatives modulo
 * Inn(G), one per class under conjugation by the family's outer generators), every c0 with beta^2 = conj(c0),
 * beta(c0) = c0 (one per class c0 ~ z beta(z) c0, z central), i.e. every extension G^ with this beta, and then every
 * G^-conjugacy class of elements t' = g t0 of the coset (orbits of g -> h g beta(h)^-1 and g -> beta(g)):
 *   ALPHA (t' an involution, c' = e): S = e + (f-1) psi-fixed + m psi-2-orbits, f + 2m = K, f = K mod 2, f >= 1;
 *   EXT   (t' not an involution, c' = t'^2 != e; K even): S = {e, c'^-1} + (K/2 - 1) further 2-orbits.
 * Family: meta: x -> x^a, y -> x^b y^c z^d, z -> z^w;  psl/sl: h -> A h A^-1 with A = 1 or diag(1, nonsquare)
 *   (the two cosets of PGL(2,p) mod PSL(2,p)), z -> z^w.  Automorphisms outside the family are missed (less
 *   complete, never wrong).
 *
 * Tabu (as ../selfdual-d5/src/sdtabu.c, with the FAST energy of sdtabu2.c from the d5b branch): energy |G \ X X|,
 * move = replace one psi-fixed element or one 2-orbit, NB random candidates per step, tabu tenure TEN, restart after
 * STALL steps without improvement; every energy-0 set gets the full three-condition Haar check before "SOL".
 *
 * usage: fsd meta m k r n3 | psl p n3 | sl p n3   [MODE]
 *   MODE (env): RECS (print records and stop), CHECK="i1 i2 ..." (element indices; energy + full check), default: tabu
 * env: K (default 12), SECS (per record and type, default 10), SEED, NB (48), TEN (12), STALL (2000), MAXSOL (2),
 *      TYPES (comma list of f values, x = EXT; default all), REC (only this record), EDGES (edge list of first SOL),
 *      DEEP=thr,secs (extra seconds for a type whose best <= thr), MAXREC (cap on records, default 400).
 * output: GROUP line, REC lines, "SOL rec R f F | indices | coordinates", one TABU line per (record, type), DONE.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <stdint.h>

static int hkind;                  /* 0 meta, 1 psl, 2 sl */
static int m_, k_, r_, p_, nh, n3, n, K = 12;
/* meta */
static int *TM;                    /* TM[j*m + a] = r^j a mod m */
typedef struct { int i, j, l, jm; } EM;
static EM *E;                      /* per element (meta): i, j, l, j*m */
/* psl/sl */
static uint8_t (*MAT)[4]; static int *IDX4, *RED; static int *EH, *EL;
static int *inv;

static inline int hmat(int h1, int h2) {
    const uint8_t *A = MAT[h1], *B = MAT[h2]; int p = p_;
    int a = RED[A[0] * B[0] + A[1] * B[2]], b = RED[A[0] * B[1] + A[1] * B[3]];
    int c = RED[A[2] * B[0] + A[3] * B[2]], d = RED[A[2] * B[1] + A[3] * B[3]];
    return IDX4[((a * p + b) * p + c) * p + d];
}
static inline int gmul(int a, int b) {
    if (hkind == 0) {
        const EM *A = &E[a], *B = &E[b];
        int i = A->i + TM[A->jm + B->i]; if (i >= m_) i -= m_;
        int j = A->j + B->j; if (j >= k_) j -= k_;
        int l = A->l + B->l; if (l >= n3) l -= n3;
        return (i * k_ + j) * n3 + l;
    }
    int l = EL[a] + EL[b]; if (l >= n3) l -= n3;
    return hmat(EH[a], EH[b]) * n3 + l;
}

static int ipow(long long b, long long e, long long mod) { long long r = 1 % mod; b %= mod; if (b < 0) b += mod;
    while (e) { if (e & 1) r = r * b % mod; b = b * b % mod; e >>= 1; } return (int)r; }
static int gcd(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a < 0 ? -a : a; }

static int ngen, gens[3];
static void build_group(int argc, char **argv) {
    if (!strcmp(argv[1], "meta")) {
        hkind = 0; m_ = atoi(argv[2]); k_ = atoi(argv[3]); r_ = ((atoi(argv[4]) % m_) + m_) % m_; n3 = atoi(argv[5]);
        if (ipow(r_, k_, m_) != 1 % m_) { fprintf(stderr, "need r^k = 1 mod m\n"); exit(2); }
        nh = m_ * k_; n = nh * n3;
        TM = malloc(sizeof(int) * nh);
        for (int j = 0; j < k_; j++) { int rj = ipow(r_, j, m_); for (int a = 0; a < m_; a++) TM[j * m_ + a] = (int)((long long)rj * a % m_); }
        E = malloc(sizeof(EM) * n); inv = malloc(sizeof(int) * n);
        for (int i = 0; i < m_; i++) for (int j = 0; j < k_; j++) for (int l = 0; l < n3; l++) {
            int e = (i * k_ + j) * n3 + l; E[e].i = i; E[e].j = j; E[e].l = l; E[e].jm = j * m_; }
        for (int e = 0; e < n; e++) { int i = E[e].i, j = E[e].j, l = E[e].l, jj = (k_ - j) % k_;
            int ii = (m_ - TM[jj * m_ + i]) % m_; inv[e] = (ii * k_ + jj) * n3 + (n3 - l) % n3; }
        ngen = 0; if (m_ > 1) gens[ngen++] = (1 * k_ + 0) * n3; if (k_ > 1) gens[ngen++] = (0 * k_ + 1) * n3; if (n3 > 1) gens[ngen++] = 1;
    } else if (!strcmp(argv[1], "psl") || !strcmp(argv[1], "sl")) {
        hkind = !strcmp(argv[1], "psl") ? 1 : 2; p_ = atoi(argv[2]); n3 = atoi(argv[3]); int p = p_;
        IDX4 = malloc(sizeof(int) * p * p * p * p); for (int i = 0; i < p * p * p * p; i++) IDX4[i] = -1;
        RED = malloc(sizeof(int) * 2 * p * p); for (int i = 0; i < 2 * p * p; i++) RED[i] = i % p;
        int cap = p * (p * p - 1); MAT = malloc(4 * cap); nh = 0;
        MAT[nh][0] = 1; MAT[nh][1] = 0; MAT[nh][2] = 0; MAT[nh][3] = 1; nh++;
        for (int a = 0; a < p; a++) for (int b = 0; b < p; b++) for (int c = 0; c < p; c++) for (int d = 0; d < p; d++) {
            if (((a * d - b * c) % p + p) % p != 1) continue;
            if (a == 1 && b == 0 && c == 0 && d == 1) continue;
            if (hkind == 1) { int fst = a ? a : b; if (fst > (p - 1) / 2) continue; }
            MAT[nh][0] = a; MAT[nh][1] = b; MAT[nh][2] = c; MAT[nh][3] = d; nh++; }
        for (int h = 0; h < nh; h++) { int a = MAT[h][0], b = MAT[h][1], c = MAT[h][2], d = MAT[h][3];
            IDX4[((a * p + b) * p + c) * p + d] = h;
            if (hkind == 1) IDX4[((((p - a) % p) * p + (p - b) % p) * p + (p - c) % p) * p + (p - d) % p] = h; }
        n = nh * n3; EH = malloc(sizeof(int) * n); EL = malloc(sizeof(int) * n); inv = malloc(sizeof(int) * n);
        for (int e = 0; e < n; e++) { EH[e] = e / n3; EL[e] = e % n3; }
        for (int e = 0; e < n; e++) { const uint8_t *A = MAT[EH[e]];
            int hi = IDX4[((A[3] * p + (p - A[1]) % p) * p + (p - A[2]) % p) * p + A[0]];
            inv[e] = hi * n3 + (n3 - EL[e]) % n3; }
        int s = IDX4[((1 * p + 1) * p + 0) * p + 1], t = IDX4[((0 * p + 1) * p + (p - 1)) * p + 0];
        ngen = 0; gens[ngen++] = s * n3; gens[ngen++] = t * n3; if (n3 > 1) gens[ngen++] = 1;
    } else { fprintf(stderr, "unknown group kind %s\n", argv[1]); exit(2); }
    (void)argc;
    for (int e = 0; e < n; e++) if (gmul(e, inv[e]) != 0 || gmul(inv[e], e) != 0) { fprintf(stderr, "inverse check fails at %d\n", e); exit(1); }
    if (n >= 65536) { fprintf(stderr, "n = %d too large\n", n); exit(2); }
}
static void coords(int e, char *buf) {
    if (hkind == 0) { if (n3 > 1) sprintf(buf, "%d,%d,%d", E[e].i, E[e].j, E[e].l); else sprintf(buf, "%d,%d", E[e].i, E[e].j); }
    else { const uint8_t *A = MAT[EH[e]]; if (n3 > 1) sprintf(buf, "%d.%d.%d.%d,%d", A[0], A[1], A[2], A[3], EL[e]);
        else sprintf(buf, "%d.%d.%d.%d", A[0], A[1], A[2], A[3]); }
}

/* ---------- automorphisms from generator images ---------- */
static int *bfsq;
static int make_aut(const int *img, int *beta) {     /* 1 if gens -> img extends to an automorphism (beta filled) */
    static char *seen = NULL; if (!seen) seen = malloc(n);
    memset(seen, 0, n); beta[0] = 0; seen[0] = 1; int qh = 0, qt = 0; bfsq[qt++] = 0;
    while (qh < qt) { int u = bfsq[qh++];
        for (int g = 0; g < ngen; g++) { int v = gmul(u, gens[g]); if (!seen[v]) { seen[v] = 1; beta[v] = gmul(beta[u], img[g]); bfsq[qt++] = v; } } }
    if (qt != n) return 0;
    for (int u = 0; u < n; u++) for (int g = 0; g < ngen; g++) if (beta[gmul(u, gens[g])] != gmul(beta[u], img[g])) return 0;
    memset(seen, 0, n); for (int u = 0; u < n; u++) { if (seen[beta[u]]) return 0; seen[beta[u]] = 1; }
    return 1;
}
static uint64_t keyof(const int *img) { uint64_t kk = 0; for (int g = 0; g < ngen; g++) kk = kk << 16 | (uint64_t)img[g]; return kk; }
static uint64_t coset_key(const int *beta) {         /* min over g of the generator images of conj(g) beta */
    uint64_t best = ~0ULL; int im[3];
    for (int g = 0; g < n; g++) { int gi = inv[g];
        for (int s = 0; s < ngen; s++) im[s] = gmul(gmul(g, beta[gens[s]]), gi);
        uint64_t kk = keyof(im); if (kk < best) best = kk; }
    return best;
}

#define MAXCAND 20000
typedef struct { int img[3]; char desc[96]; } Cand;
static Cand *cand; static int ncand;
static void add_cand(const int *img, const char *desc) {
    if (ncand >= MAXCAND) return; memcpy(cand[ncand].img, img, sizeof(int) * 3); snprintf(cand[ncand].desc, 96, "%s", desc); ncand++; }
static int *outer_img[16]; static int nouter;      /* outer generators of the family (generator images) */
static int el_meta(int i, int j, int l) { return (((i % m_ + m_) % m_) * k_ + ((j % k_ + k_) % k_)) * n3 + ((l % n3 + n3) % n3); }
static void family(void) {
    cand = malloc(sizeof(Cand) * MAXCAND); ncand = 0; char d[96]; int img[3];
    if (hkind == 0) {
        int g1 = gcd(r_ - 1 + m_, m_);                 /* b only matters mod gcd(r-1, m) up to Inn */
        for (int a = 1; a < m_ || (m_ == 1 && a == 1); a++) { if (gcd(a, m_) != 1) continue;
            int a2 = (int)((long long)a * a % m_), ok = 0; for (int j = 0; j < k_; j++) if (ipow(r_, j, m_) == a2 % m_) ok = 1;
            if (!ok) continue;
            for (int c = 1; c <= k_; c++) { int cc = c % k_; if (k_ > 1 && (gcd(c, k_) != 1 || (c * c) % k_ != 1 % k_)) continue;
                if (k_ > 1 && ipow(r_, c, m_) != r_ % m_) continue; if (k_ == 1 && c > 1) break;
                for (int b = 0; b < g1; b++) for (int dd = 0; dd < n3; dd++) { if ((long long)dd * k_ % n3) continue;
                    for (int w = 1; w <= n3; w++) { int ww = w % n3; if (n3 > 1 && (gcd(w, n3) != 1 || (w * w) % n3 != 1 % n3)) continue;
                        if (n3 == 1 && w > 1) break;
                        int q = 0; if (m_ > 1) img[q++] = el_meta(a, 0, 0); if (k_ > 1) img[q++] = el_meta(b, cc, dd); if (n3 > 1) img[q++] = el_meta(0, 0, ww);
                        snprintf(d, 96, "x->x^%d y->x^%d y^%d z^%d z->z^%d", a, b, cc, dd, ww); add_cand(img, d); } } } }
        /* outer generators: x -> x^u (u over a generating set of the units), y -> y z^dd, z -> z^w */
        nouter = 0; int seenu[4096] = {0}; int gen_cnt = 0;
        if (m_ <= 4096) { seenu[1 % m_] = 1; gen_cnt = 1; int tot = 0; for (int u = 1; u < m_; u++) if (gcd(u, m_) == 1) tot++;
            for (int u = 2; u < m_ && gen_cnt < tot && nouter < 6; u++) { if (gcd(u, m_) != 1 || seenu[u]) continue;
                int *im = malloc(sizeof(int) * 3); int q = 0; if (m_ > 1) im[q++] = el_meta(u, 0, 0); if (k_ > 1) im[q++] = el_meta(0, 1, 0); if (n3 > 1) im[q++] = el_meta(0, 0, 1);
                outer_img[nouter++] = im;
                int changed = 1; seenu[u] = 1; while (changed) { changed = 0; for (int v = 1; v < m_; v++) if (seenu[v]) for (int w = 1; w < m_; w++) if (seenu[w]) {
                    int vw = (int)((long long)v * w % m_); if (!seenu[vw]) { seenu[vw] = 1; changed = 1; } } }
                gen_cnt = 0; for (int v = 1; v < m_; v++) gen_cnt += seenu[v]; } }
        if (n3 > 1 && k_ > 1) for (int dd = 1; dd < n3 && nouter < 10; dd++) if ((long long)dd * k_ % n3 == 0) {
            int *im = malloc(sizeof(int) * 3); im[0] = el_meta(1, 0, 0); im[1] = el_meta(0, 1, dd); im[2] = el_meta(0, 0, 1); outer_img[nouter++] = im; break; }
        if (n3 > 1) for (int w = 2; w < n3 && nouter < 14; w++) if (gcd(w, n3) == 1) {
            int *im = malloc(sizeof(int) * 3); int q = 0; if (m_ > 1) im[q++] = el_meta(1, 0, 0); if (k_ > 1) im[q++] = el_meta(0, 1, 0); im[q++] = el_meta(0, 0, w); outer_img[nouter++] = im; }
    } else {
        int p = p_, nsq = 2; while (ipow(nsq, (p - 1) / 2, p) == 1) nsq++;
        for (int A = 0; A < 2; A++) for (int w = 1; w <= n3; w++) { int ww = w % n3;
            if (n3 > 1 && (gcd(w, n3) != 1 || (w * w) % n3 != 1 % n3)) continue; if (n3 == 1 && w > 1) break;
            /* conj by diag(1, u): [[a,b],[c,d]] -> [[a, b/u],[u c, d]] */
            int u = A ? nsq : 1, ui = ipow(u, p - 2, p);
            int q = 0; for (int g = 0; g < 2; g++) { const uint8_t *M = MAT[EH[gens[g]]];
                int a = M[0], b = (int)((long long)M[1] * ui % p), c = (int)((long long)M[2] * u % p), dd = M[3];
                img[q++] = IDX4[((a * p + b) * p + c) * p + dd] * n3; }
            if (n3 > 1) img[q++] = ww;
            snprintf(d, 96, "h->D h D^-1, D = diag(1,%d); z->z^%d", u, ww); add_cand(img, d); }
        nouter = 0;
        if (n3 > 1) for (int w = 2; w < n3 && nouter < 8; w++) if (gcd(w, n3) == 1) {
            int *im = malloc(sizeof(int) * 3); im[0] = gens[0]; im[1] = gens[1]; im[2] = w; outer_img[nouter++] = im; }
    }
}

/* ---------- records ---------- */
#define MAXRECS 4096
static int nrec, rkind[MAXRECS], rc[MAXRECS], *rbeta[MAXRECS], rorder[MAXRECS]; static char rdesc[MAXRECS][200];
static int MAXREC_ = 400;
static int *par; static int findp(int x) { while (par[x] != x) { par[x] = par[par[x]]; x = par[x]; } return x; }
static int elorder(int g) { int o = 1, x = g; while (x != 0) { x = gmul(x, g); o++; if (o > n) return -1; } return o; }
static void make_records(void) {
    family();
    int *beta = malloc(sizeof(int) * n), *b2 = malloc(sizeof(int) * n), *tmp = malloc(sizeof(int) * n);
    bfsq = malloc(sizeof(int) * n);
    uint64_t *ck = malloc(sizeof(uint64_t) * ncand); int *ok = calloc(ncand, sizeof(int)), nok = 0;
    for (int c = 0; c < ncand; c++) { if (!make_aut(cand[c].img, beta)) { ck[c] = ~0ULL; continue; }
        ck[c] = coset_key(beta); ok[c] = 1; nok++; }
    /* dedupe by coset key, then merge classes under outer conjugation (gamma beta gamma^-1) */
    int *rep = malloc(sizeof(int) * ncand), nrep = 0;
    for (int c = 0; c < ncand; c++) if (ok[c]) { int dup = 0; for (int q = 0; q < nrep; q++) if (ck[rep[q]] == ck[c]) { dup = 1; break; } if (!dup) rep[nrep++] = c; }
    int *rpar = malloc(sizeof(int) * nrep); for (int q = 0; q < nrep; q++) rpar[q] = q;
    int *gam = malloc(sizeof(int) * n), *gami = malloc(sizeof(int) * n);
    for (int o = 0; o < nouter; o++) { if (!make_aut(outer_img[o], gam)) continue;
        for (int u = 0; u < n; u++) gami[gam[u]] = u;
        for (int q = 0; q < nrep; q++) { make_aut(cand[rep[q]].img, beta);
            for (int u = 0; u < n; u++) tmp[u] = gam[beta[gami[u]]];
            uint64_t kk = coset_key(tmp);
            for (int q2 = 0; q2 < nrep; q2++) if (ck[rep[q2]] == kk) { int a = q, b = q2; while (rpar[a] != a) a = rpar[a]; while (rpar[b] != b) b = rpar[b]; if (a != b) rpar[b] = a; } } }
    /* centre */
    int *Z = malloc(sizeof(int) * n), nz = 0;
    for (int g = 0; g < n; g++) { int cz = 1; for (int s = 0; s < ngen; s++) if (gmul(g, gens[s]) != gmul(gens[s], g)) { cz = 0; break; } if (cz) Z[nz++] = g; }
    printf("FAMILY candidates %d automorphisms %d coset_reps %d outer_gens %d centre %d\n", ncand, nok, nrep, nouter, nz);
    par = malloc(sizeof(int) * n); int *cls = malloc(sizeof(int) * n);
    nrec = 0;
    for (int q = 0; q < nrep && nrec < MAXREC_; q++) { if (rpar[q] != q) continue;
        int c = rep[q]; make_aut(cand[c].img, beta);
        for (int u = 0; u < n; u++) b2[u] = beta[beta[u]];
        int c0 = -1;
        for (int g = 0; g < n && c0 < 0; g++) { int gi = inv[g], good = 1;
            for (int s = 0; s < ngen; s++) if (b2[gens[s]] != gmul(gmul(g, gens[s]), gi)) { good = 0; break; }
            if (good) c0 = g; }
        if (c0 < 0) continue;                           /* beta^2 not inner */
        /* valid c in c0 Z with beta(c) = c, one per class c ~ z beta(z) c */
        int *cl = malloc(sizeof(int) * nz), ncl = 0;
        for (int zi = 0; zi < nz; zi++) { int cc = gmul(c0, Z[zi]); if (beta[cc] != cc) continue;
            int dup = 0; for (int y = 0; y < ncl && !dup; y++) for (int zj = 0; zj < nz; zj++) if (gmul(gmul(Z[zj], beta[Z[zj]]), cl[y]) == cc) { dup = 1; break; }
            if (!dup) cl[ncl++] = cc; }
        for (int ci = 0; ci < ncl && nrec < MAXREC_; ci++) { int cc = cl[ci];
            /* classes of t' = g t0 under g -> h g beta(h)^-1 and g -> beta(g) */
            for (int g = 0; g < n; g++) par[g] = g;
            for (int g = 0; g < n; g++) { for (int s = 0; s < ngen; s++) { int h = gens[s];
                    int g2 = gmul(gmul(h, g), inv[beta[h]]); int a = findp(g), b = findp(g2); if (a != b) par[a] = b; }
                int a = findp(g), b = findp(beta[g]); if (a != b) par[a] = b; }
            int ncls = 0; for (int g = 0; g < n; g++) if (findp(g) == g) cls[ncls++] = g;
            /* representative of each class: the smallest g */
            int *rp = malloc(sizeof(int) * n); for (int g = 0; g < n; g++) rp[g] = -1;
            for (int g = 0; g < n; g++) { int a = findp(g); if (rp[a] < 0) rp[a] = g; }
            for (int t = 0; t < ncls && nrec < MAXREC_; t++) { int g = rp[cls[t]];
                int cp = gmul(gmul(g, beta[g]), cc);            /* t'^2 */
                if (cp != 0 && K % 2) continue;                 /* odd K: T contains an involution, ALPHA suffices */
                int *bb = malloc(sizeof(int) * n); int gi = inv[g];
                for (int u = 0; u < n; u++) bb[u] = gmul(gmul(g, beta[u]), gi);
                /* psi(x) = c'^-1 beta'(x)^-1 must be an involution */
                int invo = 1, cpi = inv[cp]; for (int u = 0; u < n && invo; u++) { int pu = gmul(cpi, inv[bb[u]]); if (gmul(cpi, inv[bb[pu]]) != u) invo = 0; }
                if (!invo) { fprintf(stderr, "internal: psi not an involution (rec skipped)\n"); free(bb); continue; }
                rkind[nrec] = cp != 0; rc[nrec] = cp; rbeta[nrec] = bb; rorder[nrec] = elorder(g) ;
                char cg[48], cc2[48]; coords(g, cg); coords(cp, cc2);
                snprintf(rdesc[nrec], 200, "%s; c0 %d; t' = (%s) t0, t'^2 = (%s)", cand[c].desc, cc, cg, cc2);
                nrec++; }
            free(rp); }
        free(cl); }
    free(beta); free(b2); free(tmp); free(gam); free(gami); free(Z); free(cls);
}

/* ---------- energy, full check ---------- */
static uint32_t *stA, *mk, *mkK, *bst; static uint32_t sA = 0, sM = 0, sK = 0, bS = 0;
static int pp_uncov(const int *S, int k, int left) {
    int X[512], nx = 0; sM++;
    for (int i = 0; i < k; i++) for (int j = 0; j < k; j++) {
        int x = left ? gmul(inv[S[i]], S[j]) : gmul(S[i], inv[S[j]]);
        if (mk[x] != sM) { mk[x] = sM; X[nx++] = x; } }
    sA++; int cov = 0;
    for (int i = 0; i < nx; i++) for (int j = 0; j < nx; j++) { int z = gmul(X[i], X[j]); if (stA[z] != sA) { stA[z] = sA; cov++; } }
    return n - cov;
}
static int pp_uncov2(const int *S, int k) {          /* = pp_uncov(S, k, 1): X = X^-1, so X X = {x y^-1} */
    int X[512], XI[512], nx = 0; sM++;
    for (int i = 0; i < k; i++) for (int j = 0; j < k; j++) { int x = gmul(inv[S[i]], S[j]); if (mk[x] != sM) { mk[x] = sM; X[nx++] = x; } }
    for (int t = 0; t < nx; t++) XI[t] = inv[X[t]];
    sA++; int cov = 1; stA[0] = sA;
    for (int i = 0; i < nx; i++) for (int t = i + 1; t < nx; t++) { int z = gmul(X[i], XI[t]);
        if (stA[z] != sA) { stA[z] = sA; cov++; int zi = inv[z]; if (stA[zi] != sA) { stA[zi] = sA; cov++; } } }
    return n - cov;
}
static int fullcheck(const int *S, int k) {
    for (int i = 0; i < k; i++) for (int j = i + 1; j < k; j++) if (S[i] == S[j]) return 0;
    if (pp_uncov(S, k, 1) || pp_uncov(S, k, 0)) return 0;
    int Y[512], ny = 0; sM++;
    for (int i = 0; i < k; i++) for (int j = 0; j < k; j++) { int x = gmul(S[i], inv[S[j]]); if (mk[x] != sM) { mk[x] = sM; Y[ny++] = x; } }
    char *yy = calloc(n, 1), *odd = calloc(n, 1);
    for (int i = 0; i < ny; i++) for (int j = 0; j < ny; j++) yy[gmul(Y[i], Y[j])] = 1;
    for (int z = 0; z < n; z++) if (yy[z]) for (int i = 0; i < k; i++) odd[gmul(z, S[i])] = 1;
    int ok = 1; for (int z = 0; z < n; z++) if (!odd[z]) ok = 0;
    free(yy); free(odd); return ok;
}

/* ---------- tabu ---------- */
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int *psi, *fl, nfl, (*ol)[2], nol, *orbof;
static void setup(int r) {
    int *be = rbeta[r], c = rc[r], ci = inv[c];
    for (int i = 0; i < n; i++) psi[i] = gmul(ci, inv[be[i]]);
    for (int i = 0; i < n; i++) if (psi[psi[i]] != i) { fprintf(stderr, "record %d: psi is not an involution\n", r); exit(1); }
    nfl = nol = 0;
    for (int i = 0; i < n; i++) {
        if (psi[i] == i) { orbof[i] = -1; if (i != 0) fl[nfl++] = i; }
        else if (i < psi[i]) { ol[nol][0] = i; ol[nol][1] = psi[i]; orbof[i] = orbof[psi[i]] = nol; nol++; } }
}
static int nf_, nm_, it[64], nit, fixed0, S[64];
static long long *tabu_until, step;
static int build(void) {
    int at = 0;
    if (fixed0 >= 0) { S[at++] = ol[fixed0][0]; S[at++] = ol[fixed0][1]; } else S[at++] = 0;
    for (int i = 0; i < nit; i++) { int x = it[i]; if (x < nfl) S[at++] = fl[x]; else { S[at++] = ol[x - nfl][0]; S[at++] = ol[x - nfl][1]; } }
    return at;
}
static int used(int x) { for (int i = 0; i < nit; i++) if (it[i] == x) return 1; if (fixed0 >= 0 && x == nfl + fixed0) return 1; return 0; }
static int rand_item(int isfix) {
    for (int t = 0; t < 1000; t++) { int x = isfix ? (int)(rnd() % nfl) : nfl + (int)(rnd() % nol); if (!used(x)) return x; }
    return -1;
}
static void randomize(void) {                       /* rand_item reads nit: call it before the increment */
    nit = 0;
    for (int i = 0; i < nf_; i++) { int x = rand_item(1); it[nit++] = x; }
    for (int i = 0; i < nm_; i++) { int x = rand_item(0); it[nit++] = x; }
}
static int XK[512], XKI[512], nxk, covbase, Sk[64], nsk;
static void base_for(int i) {                       /* coverage of X_keep X_keep, X_keep = S'^-1 S', S' = S minus item i */
    nsk = 0;
    if (fixed0 >= 0) { Sk[nsk++] = ol[fixed0][0]; Sk[nsk++] = ol[fixed0][1]; } else Sk[nsk++] = 0;
    for (int q = 0; q < nit; q++) if (q != i) { int x = it[q]; if (x < nfl) Sk[nsk++] = fl[x]; else { Sk[nsk++] = ol[x - nfl][0]; Sk[nsk++] = ol[x - nfl][1]; } }
    sK++; nxk = 0;
    for (int a = 0; a < nsk; a++) for (int b = 0; b < nsk; b++) { int x = gmul(inv[Sk[a]], Sk[b]); if (mkK[x] != sK) { mkK[x] = sK; XK[nxk++] = x; } }
    for (int t = 0; t < nxk; t++) XKI[t] = inv[XK[t]];
    bS++; covbase = 1; bst[0] = bS;
    for (int a = 0; a < nxk; a++) for (int t = a + 1; t < nxk; t++) { int z = gmul(XK[a], XKI[t]);
        if (bst[z] != bS) { bst[z] = bS; covbase++; int zi = inv[z]; if (bst[zi] != bS) { bst[zi] = bS; covbase++; } } }
}
static int cand_energy(int x) {                     /* energy of S' + item x (after base_for) */
    int Nn[2], nn = 0, NX[512], NXI[512], nnx = 0;
    if (x < nfl) Nn[nn++] = fl[x]; else { Nn[nn++] = ol[x - nfl][0]; Nn[nn++] = ol[x - nfl][1]; }
    sM++;
    for (int u = 0; u < nn; u++) { int sv = Nn[u];
        for (int b = 0; b < nsk + nn; b++) { int bv = b < nsk ? Sk[b] : Nn[b - nsk];
            int x1 = gmul(inv[sv], bv), x2 = gmul(inv[bv], sv);
            if (mkK[x1] != sK && mk[x1] != sM) { mk[x1] = sM; NX[nnx++] = x1; }
            if (mkK[x2] != sK && mk[x2] != sM) { mk[x2] = sM; NX[nnx++] = x2; } } }
    for (int t = 0; t < nnx; t++) NXI[t] = inv[NX[t]];
    sA++; int cov = covbase;
    for (int a = 0; a < nnx; a++) { int xa = NX[a];
        for (int t = 0; t < nxk; t++) { int z = gmul(xa, XKI[t]);
            if (bst[z] != bS && stA[z] != sA) { stA[z] = sA; cov++; int zi = inv[z]; if (bst[zi] != bS && stA[zi] != sA) { stA[zi] = sA; cov++; } } }
        for (int t = a + 1; t < nnx; t++) { int z = gmul(xa, NXI[t]);
            if (bst[z] != bS && stA[z] != sA) { stA[z] = sA; cov++; int zi = inv[z]; if (bst[zi] != bS && stA[zi] != sA) { stA[zi] = sA; cov++; } } } }
    return n - cov;
}
static const char *edges_out; static int nsol = 0;
static double deep_secs = 0; static int deep_thr = 0;
static void print_sol(const char *tag, const int *Sv, int k) {
    char b[64]; printf("SOL %s |", tag); for (int i = 0; i < k; i++) printf(" %d", Sv[i]); printf(" |");
    for (int i = 0; i < k; i++) { coords(Sv[i], b); printf(" %s", b); } printf("\n"); fflush(stdout);
}
static void run(int r, int f, int mm, double secs, int NB, int TEN, int STALL, int MAXSOL) {
    setup(r);
    if (rkind[r]) { fixed0 = orbof[0]; nf_ = 0; nm_ = mm - 1; } else { fixed0 = -1; nf_ = f - 1; nm_ = mm; }
    char tag[96]; snprintf(tag, sizeof tag, "rec %d %s f %d m %d", r, rkind[r] ? "ext" : "alpha", f, mm);
    if (nf_ > nfl || nm_ > nol - (fixed0 >= 0) || (nf_ == 0 && nm_ == 0)) return;
    tabu_until = calloc(nfl + nol, sizeof(long long)); step = 0;
    clock_t c0 = clock(); int best = 1 << 30, sols = 0, restarts = 0;
    randomize(); int k = build(); int e = pp_uncov2(S, k), runbest = e; long long last_imp = 0; int extended = 0;
    for (;;) {
        double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
        if (sols >= MAXSOL) break;
        if (el >= secs) { if (!extended && deep_secs > 0 && best <= deep_thr) { secs += deep_secs; extended = 1; } else break; }
        step++;
        int bi = -1, bx = -1, be = 1 << 30, ci[256], cx[256], ce[256], nc = 0;
        for (int t = 0; t < NB && t < 256; t++) { int i = (int)(rnd() % nit), isfix = it[i] < nfl; int x = rand_item(isfix); if (x < 0) continue; ci[nc] = i; cx[nc] = x; nc++; }
        for (int q = 0; q < nit; q++) { int any = 0; for (int c = 0; c < nc; c++) if (ci[c] == q) { if (!any) { base_for(q); any = 1; } ce[c] = cand_energy(cx[c]); } }
        for (int c = 0; c < nc; c++) { if (tabu_until[cx[c]] > step && ce[c] >= best) continue; if (ce[c] < be) { be = ce[c]; bi = ci[c]; bx = cx[c]; } }
        if (bi < 0) continue;
        tabu_until[it[bi]] = step + TEN; it[bi] = bx; e = be;
        if (e < runbest) { runbest = e; last_imp = step; }
        if (e < best) best = e;
        if (e == 0) { k = build();
            if (fullcheck(S, k)) { sols++; nsol++; print_sol(tag, S, k);
                if (edges_out && nsol == 1) { FILE *o = fopen(edges_out, "w"); fprintf(o, "%d\n", 2 * n);
                    for (int g = 0; g < n; g++) for (int i = 0; i < k; i++) fprintf(o, "%d %d\n", g, n + gmul(S[i], g)); fclose(o); } }
            else fprintf(stderr, "WARNING %s: energy 0 but the full check fails\n", tag);
            randomize(); k = build(); e = pp_uncov2(S, k); runbest = e; last_imp = step; restarts++; continue; }
        if (step - last_imp > STALL) { randomize(); k = build(); e = pp_uncov2(S, k); runbest = e; last_imp = step; restarts++; }
    }
    printf("TABU rec %d %s f %d m %d best %d sols %d steps %lld restarts %d secs %.1f%s\n", r, rkind[r] ? "ext" : "alpha", f, mm,
           best, sols, step, restarts, (double)(clock() - c0) / CLOCKS_PER_SEC, extended ? " DEEP" : "");
    fflush(stdout); free(tabu_until);
}
static int intype(const char *types, int f) {
    const char *p = types;
    while (*p) { if (*p >= '0' && *p <= '9') { int v = atoi(p); if (v == f) return 1; while (*p >= '0' && *p <= '9') p++; } else p++; }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 4) { fprintf(stderr, "usage: fsd meta m k r n3 | psl p n3 | sl p n3\n"); return 2; }
    if (getenv("K")) K = atoi(getenv("K"));
    if (getenv("MAXREC")) MAXREC_ = atoi(getenv("MAXREC"));
    double secs = getenv("SECS") ? atof(getenv("SECS")) : 10;
    int NB = getenv("NB") ? atoi(getenv("NB")) : 48, TEN = getenv("TEN") ? atoi(getenv("TEN")) : 12;
    int STALL = getenv("STALL") ? atoi(getenv("STALL")) : 2000, MAXSOL = getenv("MAXSOL") ? atoi(getenv("MAXSOL")) : 2;
    if (getenv("SEED")) { rs ^= (uint64_t)atoll(getenv("SEED")) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 10; i++) rnd(); }
    edges_out = getenv("EDGES");
    if (getenv("DEEP")) sscanf(getenv("DEEP"), "%d,%lf", &deep_thr, &deep_secs);
    build_group(argc, argv);
    stA = calloc(n, 4); mk = calloc(n, 4); mkK = calloc(n, 4); bst = calloc(n, 4);
    if (!strcmp(argv[1], "meta")) printf("GROUP meta m %d k %d r %d n3 %d n %d K %d\n", m_, k_, r_, n3, n, K);
    else printf("GROUP %s p %d n3 %d n %d K %d\n", argv[1], p_, n3, n, K);
    if (getenv("CHECK")) { int Sv[64], k = 0; char *s = getenv("CHECK"), *tok = strtok(s, " ");
        while (tok && k < 64) { Sv[k++] = atoi(tok); tok = strtok(NULL, " "); }
        printf("CHECK k %d energyA %d energyB %d full %d\n", k, pp_uncov(Sv, k, 1), pp_uncov(Sv, k, 0), fullcheck(Sv, k));
        if (edges_out) { FILE *o = fopen(edges_out, "w"); fprintf(o, "%d\n", 2 * n);
            for (int g = 0; g < n; g++) for (int i = 0; i < k; i++) fprintf(o, "%d %d\n", g, n + gmul(Sv[i], g)); fclose(o); }
        return 0; }
    clock_t t0 = clock(); make_records();
    printf("RECORDS %d (%.1f s)\n", nrec, (double)(clock() - t0) / CLOCKS_PER_SEC);
    for (int r = 0; r < nrec; r++) printf("REC %d %s order(g) %d | %s\n", r, rkind[r] ? "EXT" : "ALPHA", rorder[r], rdesc[r]);
    fflush(stdout);
    if (getenv("RECS")) return 0;
    psi = malloc(sizeof(int) * n); fl = malloc(sizeof(int) * n); ol = malloc(sizeof(int) * 2 * n); orbof = malloc(sizeof(int) * n);
    const char *types = getenv("TYPES"); int only = getenv("REC") ? atoi(getenv("REC")) : -1;
    for (int r = 0; r < nrec; r++) { if (only >= 0 && r != only) continue;
        if (rkind[r]) { if (K % 2 == 0 && (!types || strchr(types, 'x'))) run(r, 0, K / 2, secs, NB, TEN, STALL, MAXSOL); continue; }
        for (int f = (K % 2 ? 1 : 2); f <= K; f += 2) { if (types && !intype(types, f)) continue; run(r, f, (K - f) / 2, secs, NB, TEN, STALL, MAXSOL); } }
    printf("DONE sols %d\n", nsol);
    return 0;
}
