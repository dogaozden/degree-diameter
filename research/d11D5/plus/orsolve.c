/* orsolve.c: find Z2 flag voltages nu satisfying zcons's OR-constraints (each: the listed classes are not all
   equal, class value = constant xor sum of its variables) and its linear equations.  WalkSAT-style local search
   with single-variable flips; cost = violated OR + W * violated equations.
   usage: orsolve prefix nvars out.txt   env: SEED, SECS, W (default 4), NOISE (default 0.2) */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#include <math.h>
typedef struct { uint8_t nb, nv; int v[5]; } cls_t;
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline double urand(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
long nor, neq; int *oroff, *eqoff, *eqv; cls_t *orc; uint8_t *eqrhs; int NV;
uint8_t *x, *cval; int *ones; uint8_t *eqval;           /* per class value; per OR count of classes = 1 */
int *vo_off, *vo;   /* var -> list of entries: class index (>=0) or -(eq+1) */
static inline int orbad(long o) { int k = oroff[o + 1] - oroff[o]; return ones[o] == 0 || ones[o] == k; }
int main(int argc, char **argv) {
    if (getenv("SEED")) { rs ^= (uint64_t)atoll(getenv("SEED")) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 20; i++) rnd(); }
    double secs = getenv("SECS") ? atof(getenv("SECS")) : 120, noise = getenv("NOISE") ? atof(getenv("NOISE")) : 0.2; int W = getenv("W") ? atoi(getenv("W")) : 4;
    char fn[512]; NV = atoi(argv[2]);
    sprintf(fn, "%s.or", argv[1]); FILE *f = fopen(fn, "rb"); if (fread(&nor, 8, 1, f) != 1) return 1;
    oroff = malloc(4 * (nor + 1)); if (fread(oroff, 4, nor + 1, f) != (size_t)(nor + 1)) return 1; long nc = oroff[nor];
    orc = malloc(sizeof(cls_t) * nc); if (fread(orc, sizeof(cls_t), nc, f) != (size_t)nc) return 1; fclose(f);
    sprintf(fn, "%s.eq", argv[1]); f = fopen(fn, "rb"); if (fread(&neq, 8, 1, f) != 1) return 1;
    eqoff = malloc(4 * (neq + 1)); if (fread(eqoff, 4, neq + 1, f) != (size_t)(neq + 1)) return 1;
    eqv = malloc(4L * (eqoff[neq] + 1)); if (fread(eqv, 4, eqoff[neq], f) != (size_t)eqoff[neq]) return 1;
    eqrhs = malloc(neq + 1); if (fread(eqrhs, 1, neq, f) != (size_t)neq) return 1; fclose(f);
    printf("OR-constraints %ld (classes %ld), equations %ld, vars %d\n", nor, nc, neq, NV);
    int *cnt = calloc(NV, 4);
    for (long c = 0; c < nc; c++) for (int t = 0; t < orc[c].nv; t++) cnt[orc[c].v[t]]++;
    for (long e = 0; e < neq; e++) for (int k = eqoff[e]; k < eqoff[e + 1]; k++) cnt[eqv[k]]++;
    vo_off = malloc(4L * (NV + 1)); vo_off[0] = 0; for (int i = 0; i < NV; i++) vo_off[i + 1] = vo_off[i] + cnt[i];
    vo = malloc(4L * vo_off[NV]); memset(cnt, 0, 4L * NV);
    for (long c = 0; c < nc; c++) for (int t = 0; t < orc[c].nv; t++) { int v = orc[c].v[t]; vo[vo_off[v] + cnt[v]++] = (int)c; }
    for (long e = 0; e < neq; e++) for (int k = eqoff[e]; k < eqoff[e + 1]; k++) { int v = eqv[k]; vo[vo_off[v] + cnt[v]++] = -(int)(e + 1); }
    long *corc = malloc(8 * nc); for (long o = 0; o < nor; o++) for (int k = oroff[o]; k < oroff[o + 1]; k++) corc[k] = o;
    x = malloc(NV); for (int i = 0; i < NV; i++) x[i] = rnd() & 1;
    cval = malloc(nc); ones = calloc(nor, 4); eqval = malloc(neq + 1);
    for (long c = 0; c < nc; c++) { int v = orc[c].nb; for (int t = 0; t < orc[c].nv; t++) v ^= x[orc[c].v[t]]; cval[c] = v; ones[corc[c]] += v; }
    long cost = 0; for (long o = 0; o < nor; o++) cost += orbad(o);
    for (long e = 0; e < neq; e++) { int v = eqrhs[e]; for (int k = eqoff[e]; k < eqoff[e + 1]; k++) v ^= x[eqv[k]]; eqval[e] = v; cost += W * v; }
    printf("start cost %ld\n", cost); fflush(stdout);
    /* bad list */
    long best = cost; uint8_t *bx = malloc(NV); memcpy(bx, x, NV);
    clock_t t0 = clock(); long it = 0;
    int *touch = malloc(4 * 4096); (void)touch;
    if (getenv("SA")) {
        double T0 = getenv("T0") ? atof(getenv("T0")) : 1.5, T1 = getenv("T1") ? atof(getenv("T1")) : 0.1;
        while (cost > 0) {
            if ((it & 4095) == 0) { double el = (double)(clock() - t0) / CLOCKS_PER_SEC; if (el > secs) break;
                if ((it & ((1 << 20) - 1)) == 0) { printf("t=%.0f it=%ld cost=%ld best=%ld\n", el, it, cost, best); fflush(stdout); } }
            double el = (double)(clock() - t0) / CLOCKS_PER_SEC; double T = T0 * pow(T1 / T0, el / secs);
            it++;
            int v = rnd() % NV; long d = 0;
            for (int j = vo_off[v]; j < vo_off[v + 1]; j++) { int c = vo[j]; if (c >= 0) { long oo = corc[c]; int k = oroff[oo + 1] - oroff[oo]; int b0 = ones[oo] == 0 || ones[oo] == k; int n1 = ones[oo] + (cval[c] ? -1 : 1); int b1 = n1 == 0 || n1 == k; d += b1 - b0; ones[oo] = n1; } else { long ee = -c - 1; d += W * (eqval[ee] ? -1 : 1); } }
            if (d <= 0 || urand() < exp(-d / T)) {
                x[v] ^= 1; for (int j = vo_off[v]; j < vo_off[v + 1]; j++) { int c = vo[j]; if (c >= 0) cval[c] ^= 1; else { long ee = -c - 1; eqval[ee] ^= 1; } }
                cost += d; if (cost < best) { best = cost; memcpy(bx, x, NV); }
            } else for (int j = vo_off[v]; j < vo_off[v + 1]; j++) { int c = vo[j]; if (c >= 0) { long oo = corc[c]; ones[oo] -= (cval[c] ? -1 : 1); } }
        }
    }
    while (!getenv("SA") && cost > 0) {
        if ((it & 1023) == 0 && (double)(clock() - t0) / CLOCKS_PER_SEC > secs) break;
        it++;
        /* pick a violated constraint by random probing */
        long o = -1, e = -1;
        for (int tries = 0; tries < 200000; tries++) { if (neq && (rnd() & 1)) { long ee = rnd() % neq; if (eqval[ee]) { e = ee; break; } } else { long oo = rnd() % nor; if (orbad(oo)) { o = oo; break; } } }
        int cand[64], nc2 = 0;
        if (o >= 0) { for (int k = oroff[o]; k < oroff[o + 1] && nc2 < 60; k++) for (int t = 0; t < orc[k].nv && nc2 < 60; t++) cand[nc2++] = orc[k].v[t]; }
        else if (e >= 0) { for (int k = eqoff[e]; k < eqoff[e + 1] && nc2 < 60; k++) cand[nc2++] = eqv[k]; }
        else break;
        if (!nc2) continue;
        int pick = -1; long bestd = 1L << 60;
        if (urand() < noise) pick = cand[rnd() % nc2];
        else for (int ci = 0; ci < nc2; ci++) { int v = cand[ci]; long d = 0;
            for (int j = vo_off[v]; j < vo_off[v + 1]; j++) { int c = vo[j]; if (c >= 0) { long oo = corc[c]; int k = oroff[oo + 1] - oroff[oo]; int b0 = ones[oo] == 0 || ones[oo] == k; int n1 = ones[oo] + (cval[c] ? -1 : 1); int b1 = n1 == 0 || n1 == k; d += b1 - b0; ones[oo] = n1; } else { long ee = -c - 1; d += W * (eqval[ee] ? -1 : 1); } }
            for (int j = vo_off[v]; j < vo_off[v + 1]; j++) { int c = vo[j]; if (c >= 0) { long oo = corc[c]; ones[oo] -= (cval[c] ? -1 : 1); } }
            if (d < bestd || (d == bestd && (rnd() & 1))) { bestd = d; pick = v; } }
        /* apply */
        int v = pick; x[v] ^= 1;
        for (int j = vo_off[v]; j < vo_off[v + 1]; j++) { int c = vo[j]; if (c >= 0) { long oo = corc[c]; int k = oroff[oo + 1] - oroff[oo]; int b0 = ones[oo] == 0 || ones[oo] == k; ones[oo] += cval[c] ? -1 : 1; cval[c] ^= 1; int b1 = ones[oo] == 0 || ones[oo] == k; cost += b1 - b0; }
            else { long ee = -c - 1; cost += W * (eqval[ee] ? -1 : 1); eqval[ee] ^= 1; } }
        if (cost < best) { best = cost; memcpy(bx, x, NV); }
    }
    if (cost < best) { best = cost; memcpy(bx, x, NV); }
    printf("RESULT best=%ld iters=%ld\n", best, it);
    FILE *g = fopen(argv[3], "w"); for (int i = 0; i < NV; i++) fprintf(g, "%d\n", bx[i]); fclose(g);
    return 0;
}
