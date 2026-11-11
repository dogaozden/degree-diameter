#!/usr/bin/env python3
"""w14: subgroups of order h inside a point stabiliser (fixing point 0), classes in G, then kbi scan of pairs.
Usage: python3 stab_scan.py GROUP h [PAIRS] [CONJ]. Used for PSU34 h=24 (the generic sampler finds none)."""
import sys, os, random, subprocess, time, json
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import grp14, kgrp
def main():
    name = sys.argv[1]; h = int(sys.argv[2])
    pairs = int(sys.argv[3]) if len(sys.argv) > 3 else 20000
    t0 = time.time()
    G = grp14.Grp(grp14.group_gens(name))
    S0 = np.nonzero(G.P[:, 0] == 0)[0].tolist()
    print(f"{name} order {G.N}, point stabiliser {len(S0)}", flush=True)
    rnd = random.Random(5)
    found = {}
    for _ in range(pairs):
        x = S0[rnd.randrange(len(S0))]; y = S0[rnd.randrange(len(S0))]
        H = G.gen_sub([x, y], h)
        if H is None or len(H) != h:
            # try a third generator sometimes (non-2-generated groups)
            if rnd.random() < 0.3:
                z = S0[rnd.randrange(len(S0))]
                H = G.gen_sub([x, y, z], h)
                if H is None or len(H) != h:
                    continue
            else:
                continue
        fs = tuple(H)
        if fs not in found:
            found[fs] = H
    print(f"distinct subgroups of order {h} in stabiliser: {len(found)} ({time.time()-t0:.1f}s)", flush=True)
    classes = {}
    for H in found.values():
        key = G.canon(H)
        if key not in classes:
            classes[key] = H
    classes = list(classes.values())
    print(f"classes in G: {len(classes)} {[G.describe(H) for H in classes][:5]}", flush=True)
    os.makedirs(os.path.join(HERE, "runs"), exist_ok=True)
    for hc in range(len(classes)):
        for kc in range(len(classes)):
            H = classes[hc]; K = classes[kc]
            tag = f"{name}_h{h}_S_H{hc}_K{kc}_c0"
            binp = os.path.join(HERE, "runs", "K_" + tag + ".bin")
            M, nD, cnt = kgrp.build(G, H, K, binp)
            edges = os.path.join(HERE, "runs", "K_" + tag + ".edges")
            r = subprocess.run(["nice", "-n", "10", os.path.join(HERE, "kbi"), binp, "exh", "0", edges],
                               capture_output=True, text=True, timeout=540)
            line = r.stdout.strip().splitlines()[-1] if r.stdout.strip() else "ERR " + r.stderr[-200:]
            print(f"{tag} n={2*M} usable={cnt[1:]} {line}", flush=True)
            with open(os.path.join(HERE, "results14K.tsv"), "a") as fh:
                fh.write(f"{tag}\tn={2*M}\tdelta1-4={cnt[1:]}\t{line}\n")
    print("done", f"{time.time()-t0:.1f}s", flush=True)
if __name__ == "__main__":
    main()
