/* udesign.c: place many "units" in the polygon cover GH(q) + j matchings over Z_m (DGQ lift, polygon voltages 0,
   matching t has voltage HT[t]) and repair their coverage by designed matching assignments.
   A unit (p,t) deletes the lifted edges ((p,c),(l,c+h_t)), l = sigma_t(p), and adds z ~ {(p,c)}, z' ~ {(l,c)}.
   Only routes from the unit endpoints can break (DGQ routes of every other pair avoid the deleted edges as long as
   no line has all its points, and no point all its lines, deleted in one matching). Missed targets from (p,0) are
   points opposite p in copy h_t; they are repaired by a route (p,0) -4 GH-> (x,0) -hop-> (L,h_t) -1-> (y,h_t), i.e.
   by setting sigma_t(x) = L for a point x at distance 4 from p and a line L through y. Missed targets from (l,0) are
   lines opposite l in copy -h_t, repaired by (l,0) -4-> (l'',0) -hop-> (P,-h_t) -1-> (y,-h_t): sigma_t(P) = l''.
   Every assignment used by a repair is locked; repairs swap only unlocked assignments.
   Usage: udesign GHFILE STATE_IN REQUEST OUT_STATE OUT_UNITS [SEED] [ROUNDS]
     REQUEST: lines "p t l" (unit point, matching 1..j, requested line index for sigma_t(p)).
   Compile: gcc -O3 -march=native -fopenmp -o udesign udesign.c */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <omp.h>
typedef uint64_t u64;
static int P, q, J, m, NV, deg, NU, D = 7;
static int *lines, *ptl, *ptk, *sig, *sinv, *hv;
static int *nbr, *vin;
static char *dele, *lockP, *lockL;   /* per matching t: dele[t*P+p] unit deletion at point p; locks */
static int *up, *ut, *ul;           /* units: point, matching index (0-based), line index (not offset) */
static u64 FULL;
static u64 rs = 88172645463325252ULL;
static u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline u64 rot(u64 x, int h) { if (!h) return x; return ((x << h) | (x >> (m - h))) & FULL; }

static void set_point_slots(int p) {
    for (int s = 0; s <= q; s++) { int l = ptl[p * (q + 1) + s]; nbr[(size_t)p * deg + s] = P + l; vin[(size_t)p * deg + s] = 0; }
    for (int t = 0; t < J; t++) { int l = sig[t * P + p];
        nbr[(size_t)p * deg + q + 1 + t] = dele[t * P + p] ? -1 : P + l; vin[(size_t)p * deg + q + 1 + t] = (m - hv[t * P + p]) % m; }
}
static void set_line_slots(int l) {
    int w = P + l;
    for (int k = 0; k <= q; k++) { nbr[(size_t)w * deg + k] = lines[l * (q + 1) + k]; vin[(size_t)w * deg + k] = 0; }
    for (int t = 0; t < J; t++) { int p = sinv[t * P + l];
        nbr[(size_t)w * deg + q + 1 + t] = dele[t * P + p] ? -1 : p; vin[(size_t)w * deg + q + 1 + t] = hv[t * P + p]; }
}
static void swap_sigma(int t, int x, int x2) { /* exchange sigma_t(x) and sigma_t(x2) */
    int l1 = sig[t * P + x], l2 = sig[t * P + x2];
    sig[t * P + x] = l2; sig[t * P + x2] = l1; sinv[t * P + l2] = x; sinv[t * P + l1] = x2;
    set_point_slots(x); set_point_slots(x2); set_line_slots(l1); set_line_slots(l2);
}

/* propagation from one source: kind 0 base vertex (element 0), 1 z_i, 2 z'_i. Records up to maxk misses. */
static int run_source(int kind, int src, int *mw, int *mg, int maxk, long long *nmiss, u64 *A, u64 *B, char *ZA, char *ZB) {
    memset(A, 0, 8 * (size_t)NV); memset(ZA, 0, 2 * NU);
    int side;
    if (kind == 0) { A[src] = 1; side = src < P ? 0 : 1; }
    else if (kind == 1) { ZA[2 * src] = 1; side = 1; }
    else { ZA[2 * src + 1] = 1; side = 0; }
    u64 *cur = A, *nxt = B; char *zc = ZA, *zn = ZB; int k2 = 0; long long miss = 0;
    for (int k = 1; k <= D; k++) {
        int ns = side ^ (k & 1); int lo = ns ? P : 0, hi = ns ? NV : P;
        memset(zn, 0, 2 * NU);
        for (int w = lo; w < hi; w++) { const int *nb = nbr + (size_t)w * deg; const int *vi = vin + (size_t)w * deg; u64 r = 0;
            for (int s = 0; s < deg; s++) { int x = nb[s]; if (x >= 0) { u64 v = cur[x]; if (v) r |= rot(v, vi[s]); } } nxt[w] = r; }
        for (int i = 0; i < NU; i++) { if (ns == 1) { if (cur[up[i]]) zn[2 * i] = 1; } else { if (cur[P + ul[i]]) zn[2 * i + 1] = 1; } }
        for (int i = 0; i < NU; i++) { if (ns == 0 && zc[2 * i]) nxt[up[i]] = FULL; if (ns == 1 && zc[2 * i + 1]) nxt[P + ul[i]] = FULL; }
        u64 *t = cur; cur = nxt; nxt = t; char *tz = zc; zc = zn; zn = tz;
        if (k >= D - 1) {
            for (int w = lo; w < hi; w++) { u64 mm = FULL & ~cur[w]; while (mm) { int g = __builtin_ctzll(mm); mm &= mm - 1; miss++;
                if (k2 < maxk) { mw[k2] = w; mg[k2] = g; k2++; } } }
            for (int i = 0; i < NU; i++) { if (ns == 1 && !zc[2 * i]) { miss++; if (k2 < maxk) { mw[k2] = -1 - 2 * i; mg[k2] = 0; k2++; } }
                                           if (ns == 0 && !zc[2 * i + 1]) { miss++; if (k2 < maxk) { mw[k2] = -2 - 2 * i; mg[k2] = 0; k2++; } } }
        }
    }
    *nmiss = miss; return k2;
}
/* GH-only BFS distances */
static void gh_bfs(int s, int *dist, int *qu) {
    for (int i = 0; i < NV; i++) dist[i] = -1;
    int h = 0, t = 0; dist[s] = 0; qu[t++] = s;
    while (h < t) { int x = qu[h++];
        if (x < P) { for (int k = 0; k <= q; k++) { int y = P + ptl[x * (q + 1) + k]; if (dist[y] < 0) { dist[y] = dist[x] + 1; qu[t++] = y; } } }
        else { int l = x - P; for (int k = 0; k <= q; k++) { int y = lines[l * (q + 1) + k]; if (dist[y] < 0) { dist[y] = dist[x] + 1; qu[t++] = y; } } } }
}


/* vertices of the opposite colour at distance 1 or 3 from v (GH only), via a stamped BFS of depth 3 */
static int *stampv; static int stampc = 0; static int *levv;
static void nb3(int v, int *out, int *cnt, int *qq) {
    if (!stampv) { stampv = calloc(NV, sizeof(int)); levv = malloc(sizeof(int) * 70000); }
    stampc++; int h = 0, t = 0, n = 0; qq[t] = v; levv[t] = 0; t++; stampv[v] = stampc;
    while (h < t) { int x = qq[h]; int lx = levv[h]; h++;
        if (lx & 1) out[n++] = x;
        if (lx >= 3) continue;
        if (x < P) { for (int k = 0; k <= q; k++) { int y = P + ptl[x * (q + 1) + k]; if (stampv[y] != stampc) { stampv[y] = stampc; levv[t] = lx + 1; qq[t++] = y; } } }
        else { int l = x - P; for (int k = 0; k <= q; k++) { int y = lines[l * (q + 1) + k]; if (stampv[y] != stampc) { stampv[y] = stampc; levv[t] = lx + 1; qq[t++] = y; } } } }
    *cnt = n;
}

int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: udesign GHFILE STATE_IN REQUEST OUT_STATE OUT_UNITS [SEED] [ROUNDS]\n"); return 2; }
    FILE *f = fopen(argv[1], "r"); if (!f || fscanf(f, "%d %d", &P, &q) != 2) return 2;
    lines = malloc(sizeof(int) * (size_t)P * (q + 1));
    for (size_t i = 0; i < (size_t)P * (q + 1); i++) if (fscanf(f, "%d", &lines[i]) != 1) return 2;
    fclose(f);
    int dd; char gbuf[256];
    f = fopen(argv[2], "r"); if (!f || fscanf(f, "glift %d %d %d %d\n", &dd, &J, &m, &dd) != 4) return 2;
    if (!fgets(gbuf, sizeof gbuf, f)) return 2;
    sig = malloc(sizeof(int) * (size_t)J * P); sinv = malloc(sizeof(int) * (size_t)J * P); hv = malloc(sizeof(int) * (size_t)J * P);
    for (int p = 0; p < P; p++) for (int t = 0; t < J; t++) if (fscanf(f, "%d %d", &sig[t * P + p], &hv[t * P + p]) != 2) return 2;
    fclose(f);
    for (int t = 0; t < J; t++) for (int p = 0; p < P; p++) sinv[t * P + sig[t * P + p]] = p;
    if (argc > 6) rs ^= strtoull(argv[6], 0, 10) * 0x9E3779B97F4A7C15ULL;
    int rounds = argc > 7 ? atoi(argv[7]) : 30;
    NV = 2 * P; deg = q + 1 + J; FULL = (1ULL << m) - 1;
    ptl = malloc(sizeof(int) * P * (q + 1)); ptk = malloc(sizeof(int) * P * (q + 1));
    { int *c = calloc(P, sizeof(int)); for (int l = 0; l < P; l++) for (int k = 0; k <= q; k++) { int p = lines[l * (q + 1) + k]; ptl[p * (q + 1) + c[p]] = l; ptk[p * (q + 1) + c[p]] = k; c[p]++; } free(c); }
    dele = calloc((size_t)J * P, 1); lockP = calloc((size_t)J * P, 1); lockL = calloc((size_t)J * P, 1);
    /* units */
    f = fopen(argv[3], "r"); int cap = 4096; up = malloc(sizeof(int) * cap); ut = malloc(sizeof(int) * cap); ul = malloc(sizeof(int) * cap);
    NU = 0; int a, b, c; while (f && fscanf(f, "%d %d %d", &a, &b, &c) == 3) { up[NU] = a; ut[NU] = b - 1; ul[NU] = c; NU++; }
    if (f) fclose(f);
    for (int i = 0; i < NU; i++) {
        int t = ut[i], p = up[i], l = ul[i];
        if (lockP[t * P + p] || lockL[t * P + l]) { fprintf(stderr, "unit %d conflicts with an earlier unit\n", i); return 1; }
        int x2 = sinv[t * P + l]; if (x2 != p) { int lp = sig[t * P + p]; sig[t * P + p] = l; sig[t * P + x2] = lp; sinv[t * P + l] = p; sinv[t * P + lp] = x2; }
        dele[t * P + p] = 1; lockP[t * P + p] = 1; lockL[t * P + l] = 1;
    }
    nbr = malloc(sizeof(int) * (size_t)NV * deg); vin = malloc(sizeof(int) * (size_t)NV * deg);
    for (int p = 0; p < P; p++) set_point_slots(p);
    for (int l = 0; l < P; l++) set_line_slots(l);
    int *dist = malloc(sizeof(int) * NV), *dist2 = malloc(sizeof(int) * NV), *qu = malloc(sizeof(int) * NV);
    int *cand = malloc(sizeof(int) * 70000), *cand2 = malloc(sizeof(int) * 70000), *qu3 = malloc(sizeof(int) * 70000), *qu3b = malloc(sizeof(int) * 70000);
    int *score = calloc(NV, sizeof(int)), *seen3 = calloc(NV, sizeof(int)); int stampE = 1;
    int *free2 = malloc(sizeof(int) * P), *free4 = malloc(sizeof(int) * P);
    char *missmark = calloc(NV, 1);
    long long totfix = 0;
    int NE = 2 * NU, MK = 30000;
    int *emw = malloc(sizeof(int) * (size_t)NE * MK), *emg = malloc(sizeof(int) * (size_t)NE * MK), *ek = malloc(sizeof(int) * NE);
    long long *enm = malloc(sizeof(long long) * NE);
    int nth = getenv("THREADS") ? atoi(getenv("THREADS")) : 3;
    for (int r = 0; r < rounds; r++) {
        double t0 = omp_get_wtime();
        long long totmiss = 0, other = 0, zmiss = 0; int fixes = 0;
        #pragma omp parallel num_threads(nth)
        {
            u64 *A = malloc(8 * (size_t)NV), *B = malloc(8 * (size_t)NV); char *ZA = malloc(2 * NU + 2), *ZB = malloc(2 * NU + 2);
            #pragma omp for schedule(dynamic, 1)
            for (int e = 0; e < NE; e++) { int i = e >> 1, side = e & 1; int src = side == 0 ? up[i] : P + ul[i];
                ek[e] = run_source(0, src, emw + (size_t)e * MK, emg + (size_t)e * MK, MK, &enm[e], A, B, ZA, ZB); }
            free(A); free(B); free(ZA); free(ZB);
        }
        for (int e = 0; e < NE; e++) totmiss += enm[e];
        double t1 = omp_get_wtime();
        for (int e = 0; e < NE; e++) {
            if (!enm[e]) continue;
            int i = e >> 1, side = e & 1, t = ut[i], h = hv[t * P + up[i]];
            int src = side == 0 ? up[i] : P + ul[i];
            int k = ek[e]; int *mw = emw + (size_t)e * MK, *mg = emg + (size_t)e * MK;
            gh_bfs(src, dist, qu);
            int target_g = side == 0 ? h : (m - h) % m;
            /* free slots at distance 2 and 4 from the source (points for side 0, lines for side 1) */
            int nf2 = 0, nf4 = 0;
            for (int y = 0; y < P; y++) {
                if (side == 0) { if (lockP[t * P + y] || dele[t * P + y]) continue; if (dist[y] == 2) free2[nf2++] = y; else if (dist[y] == 4) free4[nf4++] = y; }
                else { if (lockL[t * P + y] || lockP[t * P + sinv[t * P + y]]) continue; if (dist[P + y] == 2) free2[nf2++] = y; else if (dist[P + y] == 4) free4[nf4++] = y; }
            }
            for (int z = 0; z < k; z++) {
                int w = mw[z];
                if (w < 0) { other++; continue; }
                if (side == 0 && w < P && mg[z] == target_g && dist[w] == 6) missmark[w] = 1;
                else if (side == 1 && w >= P && mg[z] == target_g && dist[w] == 6) missmark[w] = 1;
                else other++;
            }
            /* S2 repair: one assignment sigma_t(x) = L, x at distance 2 from the source, covers every marked target
               within distance 3 of L (point side; dually on the line side). score[v] = marked targets within distance 3 of v. */
            {
                int nmark = 0;
                for (int z = 0; z < k; z++) { int y = mw[z]; if (y < 0 || !missmark[y] || seen3[y] == stampE + 1) continue; seen3[y] = stampE + 1; nmark++;
                    int n2 = 0; nb3(y, cand2, &n2, qu3b); for (int u = 0; u < n2; u++) score[cand2[u]]++; }
                while (nmark > 0) {
                    int best = -1, bestc = 1;
                    int lo = side == 0 ? P : 0, hi = side == 0 ? NV : P;
                    for (int v = lo; v < hi; v++) { if (score[v] <= bestc) continue;
                        if (side == 0) { if (lockL[t * P + (v - P)] || lockP[t * P + sinv[t * P + (v - P)]]) continue; }
                        else { if (lockP[t * P + v] || dele[t * P + v]) continue; }
                        bestc = score[v]; best = v; }
                    if (best < 0) break;
                    int done1 = 0;
                    while (nf2 > 0 && !done1) {
                        int ii = (int)(rnd() % (u64)nf2); int y = free2[ii]; free2[ii] = free2[--nf2];
                        if (side == 0) { if (lockP[t * P + y] || dele[t * P + y]) continue;
                            int L = best - P, x2 = sinv[t * P + L]; if (lockP[t * P + x2]) { nf2++; free2[nf2 - 1] = y; break; }
                            if (x2 != y) swap_sigma(t, y, x2);
                            lockP[t * P + y] = 1; lockL[t * P + L] = 1; done1 = 1; }
                        else { if (lockL[t * P + y] || lockP[t * P + sinv[t * P + y]]) continue;
                            int Pt = best, x2 = sinv[t * P + y]; if (x2 != Pt) swap_sigma(t, Pt, x2);
                            lockP[t * P + Pt] = 1; lockL[t * P + y] = 1; done1 = 1; }
                    }
                    if (nf2 == 0 && !done1) break;
                    if (!done1) { score[best] = 0; continue; }
                    fixes++;
                    int n2 = 0; nb3(best, cand, &n2, qu3);
                    for (int z = 0; z < n2; z++) { int y = cand[z]; if (!missmark[y]) continue; missmark[y] = 0; nmark--;
                        int n3 = 0; nb3(y, cand2, &n3, qu3b); for (int u = 0; u < n3; u++) score[cand2[u]]--; }
                }
                /* clear scores of the targets left for the distance-4 repair */
                for (int z = 0; z < k; z++) { int y = mw[z]; if (y < 0 || !missmark[y] || seen3[y] != stampE + 1) continue; seen3[y] = 0;
                    int n2 = 0; nb3(y, cand2, &n2, qu3b); for (int u = 0; u < n2; u++) score[cand2[u]]--; }
                stampE += 2;
            }
            /* greedy repair */
            for (int z = 0; z < k; z++) {
                int w = mw[z]; if (w < 0 || !missmark[w]) continue;
                if (side == 0) {
                    /* choose a line L through w (unlocked) maximizing marked points on it */
                    int bestL = -1, bestc = -1;
                    for (int s = 0; s <= q; s++) { int L = ptl[w * (q + 1) + s]; if (lockL[t * P + L]) continue;
                        int cnt = 0; for (int kk = 0; kk <= q; kk++) cnt += missmark[lines[L * (q + 1) + kk]];
                        if (cnt > bestc) { bestc = cnt; bestL = L; } }
                    int x = -1, x2 = -1;
                    if (bestL >= 0 && !lockP[t * P + sinv[t * P + bestL]]) {
                        x2 = sinv[t * P + bestL];
                        while (nf4 > 0 && x < 0) { int ii = (int)(rnd() % (u64)nf4); int y = free4[ii]; free4[ii] = free4[--nf4]; if (!lockP[t * P + y] && !dele[t * P + y] && y != x2) x = y; }
                    }
                    if (x < 0) continue;
                    if (x != x2) swap_sigma(t, x, x2);
                    lockP[t * P + x] = 1; lockL[t * P + bestL] = 1; fixes++;
                    for (int kk = 0; kk <= q; kk++) missmark[lines[bestL * (q + 1) + kk]] = 0;
                } else {
                    int wl = w - P;
                    /* choose a point Pt on line w (unlocked) maximizing marked lines through it */
                    int bestP = -1, bestc = -1;
                    for (int kk = 0; kk <= q; kk++) { int Pt = lines[wl * (q + 1) + kk]; if (lockP[t * P + Pt] || dele[t * P + Pt]) continue;
                        int cnt = 0; for (int s = 0; s <= q; s++) cnt += missmark[P + ptl[Pt * (q + 1) + s]];
                        if (cnt > bestc) { bestc = cnt; bestP = Pt; } }
                    int l2 = -1;
                    if (bestP >= 0)
                        while (nf4 > 0 && l2 < 0) { int ii = (int)(rnd() % (u64)nf4); int y = free4[ii]; free4[ii] = free4[--nf4]; if (!lockL[t * P + y] && !lockP[t * P + sinv[t * P + y]]) l2 = y; }
                    if (l2 < 0) continue;
                    int x2 = sinv[t * P + l2];
                    if (x2 != bestP) swap_sigma(t, bestP, x2);
                    lockP[t * P + bestP] = 1; lockL[t * P + l2] = 1; fixes++;
                    for (int s = 0; s <= q; s++) missmark[P + ptl[bestP * (q + 1) + s]] = 0;
                }
            }
            for (int z = 0; z < k; z++) if (mw[z] >= 0) missmark[mw[z]] = 0;
        }
        double t2 = omp_get_wtime();
        #pragma omp parallel num_threads(nth) reduction(+:zmiss)
        {
            u64 *A = malloc(8 * (size_t)NV), *B = malloc(8 * (size_t)NV); char *ZA = malloc(2 * NU + 2), *ZB = malloc(2 * NU + 2);
            int dmw[1], dmg[1];
            #pragma omp for schedule(dynamic, 1)
            for (int e = 0; e < NE; e++) { long long nm; run_source(1 + (e & 1), e >> 1, dmw, dmg, 0, &nm, A, B, ZA, ZB); zmiss += nm; }
            free(A); free(B); free(ZA); free(ZB);
        }
        totfix += fixes;
        fprintf(stderr, "round %d: endpoint misses %lld (not repairable here %lld), unit-vertex misses %lld, repairs %d  [%.0fs prop, %.0fs repair, %.0fs z]\n",
                r, totmiss, other, zmiss, fixes, t1 - t0, t2 - t1, omp_get_wtime() - t2);
        if (totmiss == 0 && zmiss == 0) break;
        if (fixes == 0) break;
    }
    /* write state and units */
    f = fopen(argv[4], "w");
    fprintf(f, "glift %d %d %d 7\ncyc %d\n", q, J, m, m);
    for (int p = 0; p < P; p++) { for (int t = 0; t < J; t++) fprintf(f, "%s%d %d", t ? " " : "", sig[t * P + p], hv[t * P + p]); fprintf(f, "\n"); }
    for (int l = 0; l < P; l++) { for (int k = 0; k <= q; k++) fprintf(f, k ? " 0" : "0"); fprintf(f, "\n"); }
    fclose(f);
    f = fopen(argv[5], "w"); for (int i = 0; i < NU; i++) fprintf(f, "%d %d\n", up[i], ut[i] + 1); fclose(f);
    long long nl = 0; for (int t = 0; t < J; t++) for (int p = 0; p < P; p++) nl += lockP[t * P + p];
    fprintf(stderr, "done: %d units, %lld locked assignments, %lld repairs\n", NU, nl, totfix);
    return 0;
}
