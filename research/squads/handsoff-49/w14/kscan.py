#!/usr/bin/env python3
"""w14: scan all pairs of subgroup classes (H, K) of order h (and random conjugates of K) with kbi (exact search).
Usage: python3 kscan.py GROUP h [TRIALS] [NCONJ]   -> appends lines to results14K.tsv"""
import sys, os, random, subprocess, time, json
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import grp14, kgrp

def main():
    name = sys.argv[1]; h = int(sys.argv[2])
    trials = int(sys.argv[3]) if len(sys.argv) > 3 else 800
    nconj = int(sys.argv[4]) if len(sys.argv) > 4 else 0
    t0 = time.time()
    G = grp14.Grp(grp14.group_gens(name))
    classes = G.subgroup_classes(h, trials)
    print(f"{name} h={h} n={2*G.N//h}: {len(classes)} classes, sampling {time.time()-t0:.1f}s", flush=True)
    rnd = random.Random(7)
    for hc in range(len(classes)):
        for kc in range(len(classes)):
            for c in range(nconj + 1):
                H = classes[hc]; K = classes[kc]
                if c > 0:
                    K = kgrp.conj_subgroup(G, K, rnd.randrange(G.N))
                tag = f"{name}_h{h}_H{hc}_K{kc}_c{c}"
                binp = os.path.join(HERE, "runs", "K_" + tag + ".bin")
                os.makedirs(os.path.join(HERE, "runs"), exist_ok=True)
                M, nD, cnt = kgrp.build(G, H, K, binp)
                edges = os.path.join(HERE, "runs", "K_" + tag + ".edges")
                r = subprocess.run(["nice", "-n", "10", os.path.join(HERE, "kbi"), binp, "exh", "0", edges],
                                   capture_output=True, text=True, timeout=540)
                line = r.stdout.strip().splitlines()[-1] if r.stdout.strip() else "ERR " + r.stderr[-200:]
                print(f"{tag} n={2*M} usable={cnt[1:]} {line}", flush=True)
                with open(os.path.join(HERE, "results14K.tsv"), "a") as fh:
                    fh.write(f"{tag}\tn={2*M}\tdelta1-4={cnt[1:]}\t{line}\t{json.dumps(G.describe(H))}\t{json.dumps(G.describe(K))}\n")
    print("done", f"{time.time()-t0:.1f}s", flush=True)

if __name__ == "__main__":
    main()
