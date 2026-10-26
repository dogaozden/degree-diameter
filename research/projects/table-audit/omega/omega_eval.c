/* omega_eval.c (table-audit): build Omega H(q) with a given labelling (omega_model.h) and count pairs at distance > D.
   usage: omega_eval HEX TYPES INNER LAB D SOURCES [OUT_EDGES]
     LAB: a labelling file (see omega_model.h) or "id" (P_c[t] = L_c[t] = t: the thesis's same-label wiring with the
          index pairing).  SOURCES: all | hubs | hubs0 (hubs (t,0), (t,0bar) only) | first:K (vertices 0..K-1) | one:V (vertex V only).
   Prints vertices, edges, degree range, far pairs from the sources, max eccentricity of the sources, one witness. */
#include "omega_model.h"
int main(int argc, char **argv) {
    if (argc < 7) { fprintf(stderr, "usage: omega_eval HEX TYPES INNER LAB D SOURCES [OUT_EDGES]\n"); return 2; }
    Omega o; if (om_load_hex(&o, argv[1])) return 2;
    om_alloc(&o, argv[2], argv[3]);
    if (strcmp(argv[4], "id") && om_read_lab(&o, argv[4])) return 2;
    int D = atoi(argv[5]); om_build(&o);
    long ns = 0, *src = malloc(sizeof(long) * o.NV);
    if (!strcmp(argv[6], "all")) for (long v = 0; v < o.NV; v++) src[ns++] = v;
    else if (!strcmp(argv[6], "hubs")) for (long v = o.base; v < o.NV; v++) src[ns++] = v;
    else if (!strcmp(argv[6], "hubs0")) for (int t = 0; t < o.n; t++) { src[ns++] = om_hub(&o, t, 0, 0); src[ns++] = om_hub(&o, t, 1, 0); }
    else if (!strncmp(argv[6], "first:", 6)) { long K = atol(argv[6] + 6); for (long v = 0; v < K; v++) src[ns++] = v; }
    else if (!strncmp(argv[6], "one:", 4)) src[ns++] = atol(argv[6] + 4);
    int mind = 1 << 30, maxd = 0; long ne = 0;
    for (long v = 0; v < o.NV; v++) { if (o.deg[v] < mind) mind = o.deg[v]; if (o.deg[v] > maxd) maxd = o.deg[v]; ne += o.deg[v]; }
    int ecc; long wu = -1, wv = -1;
    long bad = om_far(&o, src, (int)ns, D, &ecc, &wu, &wv);
    printf("q=%d types=%s inner=%s lab=%s n=%ld edges=%ld degree min=%d max=%d sources=%ld far(>%d)=%ld maxecc=%d",
           o.q, o.types, o.inner, argv[4], o.NV, ne / 2, mind, maxd, ns, D, bad, ecc);
    if (bad) printf(" witness d(%ld,%ld)>%d", wu, wv, D);
    printf("\n");
    if (argc > 7) om_write_edges(&o, argv[7]);
    return 0;
}
