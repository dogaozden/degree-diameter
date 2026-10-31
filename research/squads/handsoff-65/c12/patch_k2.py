import sys
src = open(sys.argv[1]).read()
anchor = '                if (getenv("VERB")) fprintf(stderr, "steps %ld\\n", steps);\n'
assert src.count(anchor) == 1
new = anchor + r'''                if (getenv("K2") && best > 0) {  /* exhaustive two-move neighbourhood of the best state */
                    memcpy(chosen, bestch, sizeof chosen);
                    for (int k = 0; k < nblk; k++) { memset(isch[k], 0, m); for (int c = 0; c < nab[k]; c++) isch[k][chosen[k][c]] = 1; }
                    long n2 = 0; int b2 = best;
                    for (int k1 = 0; k1 < nblk && best > 0; k1++) for (int c1 = 0; c1 < nab[k1]; c1++) {
                        int o1 = chosen[k1][c1];
                        for (int i1 = 0; i1 < nfull[k1] && best > 0; i1++) { int d1 = fulllist[k1][i1]; if (isch[k1][d1]) continue;
                            chosen[k1][c1] = d1; isch[k1][o1] = 0; isch[k1][d1] = 1;
                            for (int k2 = 0; k2 < nblk && best > 0; k2++) for (int c2 = 0; c2 < nab[k2]; c2++) {
                                int o2 = chosen[k2][c2];
                                for (int i2 = 0; i2 < nfull[k2]; i2++) { int d2 = fulllist[k2][i2]; if (isch[k2][d2]) continue;
                                    chosen[k2][c2] = d2; isch[k2][o2] = 0; isch[k2][d2] = 1;
                                    int v = cost_eval(); evals++; n2++;
                                    if (v < best) { best = v; memcpy(bestch, chosen, sizeof bestch);
                                        if (best < gbest) { gbest = best; if (EDGES) write_edges(EDGES); } }
                                    chosen[k2][c2] = o2; isch[k2][d2] = 0; isch[k2][o2] = 1;
                                }
                            }
                            chosen[k1][c1] = o1; isch[k1][d1] = 0; isch[k1][o1] = 1;
                        }
                    }
                    if (getenv("VERB")) fprintf(stderr, "k2 pairs %ld before %d after %d\n", n2, b2, best);
                }
'''
src = src.replace(anchor, new)
open(sys.argv[2], 'w').write(src)
