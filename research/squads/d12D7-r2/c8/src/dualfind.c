/* dualfind.c: a duality of the split Cayley hexagon H(q), q = 3^e, built from a polarity of the subhexagon H(3).
   d10D7 job (Opus), 2026-10-24.  Why: in X(M) (research/squads/exp2/hexd7) a freed flag (p, l) is covered exactly
   when M maps S'(p) onto S(l); a duality phi with phi(p) = l, phi(l) = p does this for ALL such absolute flags at once.
   Method: H(3) = points with coordinates in GF(3) (hexgen2 encodes GF(9) as a0 + 3 a1) and the lines meeting it twice.
   1. A polarity theta of H(3): fix an apartment A (12-cycle) and a type-swapping reflection of it; two extra points
      kill the torus; propagate the map along edges, choosing for each new vertex the unique candidate neighbour of the
      image whose distances to the image frame equal the vertex's distances to the frame. Keep a map with theta^2 = 1.
   2. Extend theta to H(q) the same way (frame inside H(3); the Frobenius ambiguity is fixed by one extra choice).
   3. Verify incidence is preserved, list the absolute flags, write them and phi.
   Usage: dualfind HEXBIN OUTPREFIX     (writes OUTPREFIX.phi: 2N ints, phi of point p at p, of line l at N+l;
                                         OUTPREFIX.abs: absolute flags "p l") */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

static int q, N, Q1, *LP, *PL; static uint8_t *coord;
static int nbr(int v, int k) { return v < N ? N + PL[v * Q1 + k] : LP[(v - N) * Q1 + k]; }
static void bfs(int s, uint8_t *d, const uint8_t *allow) {   /* distances in the graph induced on allowed vertices */
    int *qq = malloc(sizeof(int) * 2 * N), h = 0, t = 0;
    memset(d, 255, 2 * N); d[s] = 0; qq[t++] = s;
    while (h < t) { int v = qq[h++]; for (int k = 0; k < Q1; k++) { int w = nbr(v, k); if (allow && !allow[w]) continue; if (d[w] == 255) { d[w] = d[v] + 1; qq[t++] = w; } } }
    free(qq);
}
/* propagate phi (phi[v] = -1 undetermined) on allowed vertices; frame f[0..nf) with images phi[f[i]] known.
   distances: df[i][v] from f[i], dg[i][w] from phi(f[i]). returns number determined, -1 on contradiction */
static int propagate(int *phi, int *used, const uint8_t *allow, int nf, uint8_t **df, uint8_t **dg) {
    int *qq = malloc(sizeof(int) * 2 * N), h = 0, t = 0, cnt = 0;
    for (int v = 0; v < 2 * N; v++) if (phi[v] >= 0) { qq[t++] = v; cnt++; }
    int progress = 1;
    while (progress) {
        progress = 0;
        while (h < t) {
            int u = qq[h++];
            for (int k = 0; k < Q1; k++) {
                int v = nbr(u, k); if (allow && !allow[v]) continue; if (phi[v] >= 0) continue;
                int cand = -1, nc = 0;
                for (int k2 = 0; k2 < Q1; k2++) {
                    int w = nbr(phi[u], k2); if (allow && !allow[w]) continue; if (used[w]) continue;
                    int ok = 1; for (int i = 0; i < nf && ok; i++) if (df[i][v] != dg[i][w]) ok = 0;
                    if (!ok) continue;
                    /* consistency with other determined neighbours of v */
                    for (int k3 = 0; k3 < Q1 && ok; k3++) { int x = nbr(v, k3); if (allow && !allow[x]) continue; if (phi[x] < 0) continue;
                        int adj = 0; for (int k4 = 0; k4 < Q1; k4++) if (nbr(w, k4) == phi[x]) adj = 1; if (!adj) ok = 0; }
                    if (ok) { cand = w; nc++; }
                }
                if (nc == 0) { free(qq); return -1; }
                if (nc == 1) { phi[v] = cand; used[cand] = 1; qq[t++] = v; cnt++; progress = 1; }
            }
        }
        if (progress) { h = 0; t = 0; for (int v = 0; v < 2 * N; v++) if (phi[v] >= 0) qq[t++] = v; }
    }
    free(qq); return cnt;
}

/* propagate, and when stuck add determined vertices (far from the frame) to the frame and continue */
static int propagate_grow(int *phi, int *used, const uint8_t *allow, int *fr, int *nfp, uint8_t **df, uint8_t **dg, int maxf, int total) {
    int got = propagate(phi, used, allow, *nfp, df, dg);
    while (got >= 0 && got < total && *nfp < maxf) {
        int added = 0;
        for (int rep = 0; rep < 6 && *nfp < maxf; rep++) {
            int best = -1, bd = -1;
            for (int v = 0; v < 2 * N; v++) {
                if (phi[v] < 0 || (allow && !allow[v])) continue;
                int m = 255; for (int i = 0; i < *nfp; i++) if (df[i][v] < m) m = df[i][v];
                if (m > bd) { bd = m; best = v; }
            }
            if (best < 0 || bd == 0) break;
            fr[*nfp] = best; bfs(best, df[*nfp], allow); bfs(phi[best], dg[*nfp], allow); (*nfp)++; added++;
        }
        if (!added) break;
        int g2 = propagate(phi, used, allow, *nfp, df, dg);
        if (g2 < 0) return -1;
        if (g2 == got) break;
        got = g2;
    }
    return got;
}
static int check_dual(const int *phi, const uint8_t *allow) {   /* type swap + incidence preserved on allowed edges */
    for (int v = 0; v < 2 * N; v++) { if (allow && !allow[v]) continue; if (phi[v] < 0) return 0; if ((v < N) == (phi[v] < N)) return 0; }
    for (int p = 0; p < N; p++) { if (allow && !allow[p]) continue;
        for (int k = 0; k < Q1; k++) { int l = N + PL[p * Q1 + k]; if (allow && !allow[l]) continue;
            int a = phi[p], b = phi[l], adj = 0; for (int k2 = 0; k2 < Q1; k2++) if (nbr(a, k2) == b) adj = 1; if (!adj) return 0; } }
    return 1;
}

/* depth-first search: propagate, then branch on an undetermined vertex adjacent to a determined one */
static int nbranch = 0;
static int solve(int *phi, int *used, const uint8_t *allow, int *fr, int nf, uint8_t **df, uint8_t **dg, int total, int depth) {
    int got = propagate(phi, used, allow, nf, df, dg);
    if (got < 0) return 0;
    if (got == total) return check_dual(phi, allow);
    if (depth > 12) return 0;
    /* choose the undetermined vertex with fewest candidates */
    int bv = -1, bu = -1, bn = 99, cands[64], nc;
    for (int u = 0; u < 2 * N; u++) {
        if (phi[u] < 0 || (allow && !allow[u])) continue;
        for (int k = 0; k < Q1; k++) {
            int v = nbr(u, k); if (allow && !allow[v]) continue; if (phi[v] >= 0) continue;
            nc = 0;
            for (int k2 = 0; k2 < Q1; k2++) { int w = nbr(phi[u], k2); if (allow && !allow[w]) continue; if (used[w]) continue;
                int ok = 1; for (int i = 0; i < nf && ok; i++) if (df[i][v] != dg[i][w]) ok = 0; if (ok) nc++; }
            if (nc < bn) { bn = nc; bv = v; bu = u; }
        }
    }
    if (bv < 0 || bn == 0) return 0;
    nc = 0;
    for (int k2 = 0; k2 < Q1; k2++) { int w = nbr(phi[bu], k2); if (allow && !allow[w]) continue; if (used[w]) continue;
        int ok = 1; for (int i = 0; i < nf && ok; i++) if (df[i][bv] != dg[i][w]) ok = 0; if (ok) cands[nc++] = w; }
    int *phi2 = malloc(sizeof(int) * 2 * N), *used2 = malloc(sizeof(int) * 2 * N);
    for (int c = 0; c < nc; c++) {
        nbranch++;
        memcpy(phi2, phi, sizeof(int) * 2 * N); memcpy(used2, used, sizeof(int) * 2 * N);
        phi2[bv] = cands[c]; used2[cands[c]] = 1;
        if (solve(phi2, used2, allow, fr, nf, df, dg, total, depth + 1)) { memcpy(phi, phi2, sizeof(int) * 2 * N); memcpy(used, used2, sizeof(int) * 2 * N); free(phi2); free(used2); return 1; }
    }
    free(phi2); free(used2); return 0;
}
int main(int argc, char **argv) {
    FILE *f = fopen(argv[1], "rb"); int32_t hdr[3]; if (!f || fread(hdr, 4, 3, f) != 3) return 1;
    q = hdr[0]; N = hdr[1]; Q1 = q + 1;
    LP = malloc(sizeof(int) * N * Q1); if (fread(LP, 4, (size_t)N * Q1, f) != (size_t)N * Q1) return 1;
    coord = malloc((size_t)N * 7); if (fread(coord, 1, (size_t)N * 7, f) != (size_t)N * 7) return 1; fclose(f);
    PL = malloc(sizeof(int) * N * Q1); int *c = calloc(N, sizeof(int));
    for (int l = 0; l < N; l++) for (int k = 0; k < Q1; k++) { int p = LP[l * Q1 + k]; PL[p * Q1 + c[p]++] = l; }
    /* subhexagon H(3) */
    uint8_t *inS = calloc(2 * N, 1); int nsp = 0, nsl = 0;
    for (int p = 0; p < N; p++) { int ok = 1; for (int j = 0; j < 7; j++) if (coord[p * 7 + j] >= 3) ok = 0; if (ok) { inS[p] = 1; nsp++; } }
    for (int l = 0; l < N; l++) { int k3 = 0; for (int k = 0; k < Q1; k++) k3 += inS[LP[l * Q1 + k]]; if (k3 >= 2) { inS[N + l] = 1; nsl++; } }
    fprintf(stderr, "q=%d N=%d; subhexagon: %d points, %d lines\n", q, N, nsp, nsl);
    /* apartment in S */
    int p0 = -1; for (int p = 0; p < N; p++) if (inS[p]) { p0 = p; break; }
    uint8_t *d0 = malloc(2 * N); bfs(p0, d0, inS);
    int p3 = -1; for (int p = 0; p < N; p++) if (inS[p] && d0[p] == 6) { p3 = p; break; }
    uint8_t *d3 = malloc(2 * N); bfs(p3, d3, inS);
    int A[12]; A[0] = p0; A[6] = p3;
    int la = -1, lb = -1; for (int k = 0; k < Q1; k++) { int l = N + PL[p0 * Q1 + k]; if (!inS[l]) continue; if (la < 0) la = l; else if (lb < 0) lb = l; }
    A[1] = la; for (int i = 2; i < 6; i++) { int u = A[i - 1]; for (int k = 0; k < Q1; k++) { int w = nbr(u, k); if (inS[w] && d3[w] == d3[u] - 1) { A[i] = w; break; } } }
    A[11] = lb; for (int i = 10; i > 6; i--) { int u = A[i + 1]; for (int k = 0; k < Q1; k++) { int w = nbr(u, k); if (inS[w] && d3[w] == d3[u] - 1) { A[i] = w; break; } } }
    for (int i = 0; i < 12; i++) { int a = A[i], b = A[(i + 1) % 12], adj = 0; for (int k = 0; k < Q1; k++) if (nbr(a, k) == b) adj = 1; if (!adj) { fprintf(stderr, "apartment broken at %d\n", i); return 1; } }
    /* extra frame points: S-points on A[1] and A[3] not in A */
    int xs[2], ys[2], nx = 0, ny = 0;
    for (int k = 0; k < Q1; k++) { int w = nbr(A[1], k); if (inS[w] && w != A[0] && w != A[2] && nx < 2) xs[nx++] = w; }
    for (int k = 0; k < Q1; k++) { int w = nbr(A[3], k); if (inS[w] && w != A[2] && w != A[4] && ny < 2) ys[ny++] = w; }
    int *phi = malloc(sizeof(int) * 2 * N), *used = malloc(sizeof(int) * 2 * N), *theta = NULL;
    uint8_t *df[200], *dg[200]; for (int i = 0; i < 200; i++) { df[i] = malloc(2 * N); dg[i] = malloc(2 * N); }
    for (int cc = 1; cc < 12 && !theta; cc += 2) {       /* reflection v_i -> v_{cc - i}: fixes the flags (A[(cc-1)/2], A[(cc+1)/2]) */
        int img[12]; for (int i = 0; i < 12; i++) img[i] = A[((cc - i) % 12 + 12) % 12];
        /* image candidates for xs[0] (S-point on A[1]): S-lines through img[1] not in A, likewise ys[0] on A[3] */
        int cx[8], ncx = 0, cy[8], ncy = 0;
        for (int k = 0; k < Q1; k++) { int w = nbr(img[1], k); if (inS[w] && w != img[0] && w != img[2]) cx[ncx++] = w; }
        for (int k = 0; k < Q1; k++) { int w = nbr(img[3], k); if (inS[w] && w != img[2] && w != img[4]) cy[ncy++] = w; }
        for (int a = 0; a < ncx && !theta; a++) for (int b = 0; b < ncy && !theta; b++) {
            int fr[200], fi[200], nf = 0;
            for (int i = 0; i < 12; i++) { fr[nf] = A[i]; fi[nf] = img[i]; nf++; }
            fr[nf] = xs[0]; fi[nf] = cx[a]; nf++; fr[nf] = ys[0]; fi[nf] = cy[b]; nf++;
            for (int v = 0; v < 2 * N; v++) { phi[v] = -1; used[v] = 0; }
            int bad = 0; for (int i = 0; i < nf; i++) { if (phi[fr[i]] >= 0 && phi[fr[i]] != fi[i]) bad = 1; if (used[fi[i]] && phi[fr[i]] != fi[i]) bad = 1; phi[fr[i]] = fi[i]; used[fi[i]] = 1; }
            if (bad) continue;
            for (int i = 0; i < nf; i++) { bfs(fr[i], df[i], inS); bfs(fi[i], dg[i], inS); }
            int ok = solve(phi, used, inS, fr, nf, df, dg, nsp + nsl, 0); int got = 0; for (int v = 0; v < 2 * N; v++) got += phi[v] >= 0;
            int invol = 0;
            if (ok) { invol = 1; for (int v = 0; v < 2 * N; v++) if (inS[v] && phi[phi[v]] != v) { invol = 0; break; } }
            fprintf(stderr, "reflection c=%d x-choice %d y-choice %d: determined %d of %d, duality %d, involution %d\n", cc, a, b, got, nsp + nsl, ok, invol);
            if (ok && invol) { theta = malloc(sizeof(int) * 2 * N); memcpy(theta, phi, sizeof(int) * 2 * N); }
        }
    }
    if (!theta) { fprintf(stderr, "no polarity of the subhexagon found\n"); return 1; }
    int nabsS = 0; for (int p = 0; p < N; p++) if (inS[p]) { int l = theta[p]; if (theta[l] == p) { int inc = 0; for (int k = 0; k < Q1; k++) if (N + PL[p * Q1 + k] == l) inc = 1; nabsS += inc; } }
    fprintf(stderr, "polarity of H(3): %d absolute flags\n", nabsS);
    if (q == 3) { phi = theta; }
    else {
        /* extend to H(q): frame = 40 S-elements spread out; Frobenius ambiguity: try the choices for one outside point */
        int fr[200], nf = 0; for (int v = 0; v < 2 * N && nf < 40; v += 97) { int u = v; while (u < 2 * N && !inS[u]) u++; if (u < 2 * N) { int dup = 0; for (int i = 0; i < nf; i++) if (fr[i] == u) dup = 1; if (!dup) fr[nf++] = u; } }
        for (int i = 0; i < nf; i++) { bfs(fr[i], df[i], NULL); bfs(theta[fr[i]], dg[i], NULL); }
        int z = -1; for (int k = 0; k < Q1; k++) { int w = nbr(A[1], k); if (!inS[w]) { z = w; break; } }   /* non-S point on an S-line */
        int found = 0;
        for (int k2 = 0; k2 < Q1 && !found; k2++) {
            int cand = nbr(theta[A[1]], k2); if (inS[cand]) continue;
            for (int v = 0; v < 2 * N; v++) { phi[v] = inS[v] ? theta[v] : -1; used[v] = 0; }
            for (int v = 0; v < 2 * N; v++) if (phi[v] >= 0) used[phi[v]] = 1;
            phi[z] = cand; used[cand] = 1;
            int ok = solve(phi, used, NULL, fr, nf, df, dg, 2 * N, 0); int got = 0; for (int v = 0; v < 2 * N; v++) got += phi[v] >= 0;
            fprintf(stderr, "extension choice %d: determined %d of %d, duality %d\n", k2, got, 2 * N, ok);
            if (ok) found = 1;
        }
        if (!found) { fprintf(stderr, "no extension found\n"); return 1; }
    }
    /* absolute flags */
    char fn[512]; snprintf(fn, sizeof fn, "%s.abs", argv[2]); FILE *fa = fopen(fn, "w"); int nabs = 0;
    for (int p = 0; p < N; p++) { int l = phi[p]; if (phi[l] != p) continue; int inc = 0; for (int k = 0; k < Q1; k++) if (N + PL[p * Q1 + k] == l) inc = 1; if (inc) { fprintf(fa, "%d %d\n", p, l - N); nabs++; } }
    fclose(fa);
    int ninv = 0; for (int v = 0; v < 2 * N; v++) if (phi[phi[v]] == v) ninv++;
    snprintf(fn, sizeof fn, "%s.phi", argv[2]); FILE *fp = fopen(fn, "wb"); fwrite(phi, sizeof(int), 2 * N, fp); fclose(fp);
    printf("duality of H(%d) found: %d absolute flags, phi^2 fixes %d of %d elements\n", q, nabs, ninv, 2 * N);
    return 0;
}
