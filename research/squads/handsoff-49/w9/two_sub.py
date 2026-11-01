#!/usr/bin/env python3
"""w9: two-subgroup bi-coset family S = K S H (H, K of equal order). Usage:
   python3 two_sub.py GROUP h HCLASS NK CAP [SEED]   HCLASS = index into subgroup_classes(h) (seed 1, 3000 trials)
   K ranges over NK random subgroups of order h (random conjugates of H and random other subgroups from sampler)."""
import sys, os, random, subprocess, time
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__))
import grp9

def main():
    name, h, hcls, nk, cap = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5])
    seed = int(sys.argv[6]) if len(sys.argv) > 6 else 7
    G = grp9.Grp(grp9.group_gens(name))
    classes = G.subgroup_classes(h, int(os.environ.get("TRIALS", "3000")))
    H = classes[hcls]
    print(f"{name} h={h} H class {hcls} orders {G.describe(H)}  classes={len(classes)}", flush=True)
    rnd = random.Random(seed)
    # candidate K: all subgroups of order h that are sampled (any class) plus random conjugates of H
    pool = []
    for c in classes:
        pool.append(c)
    Ks = []
    for _ in range(nk):
        if rnd.random() < 0.5:
            g = rnd.randrange(G.N)
            Hc = sorted(int(G.conj_all(x)[g]) for x in H)     # g^-1 H g
            Ks.append(("conj", Hc))
        else:
            Ks.append(("class", pool[rnd.randrange(len(pool))]))
    best = (10**9, None, None)
    t0 = time.time()
    for n, (kind, K) in enumerate(Ks):
        if len(K) != h:
            continue
        binp = os.path.join(HERE, "runs", f"two_{name}_h{h}_c{hcls}_{n}.bin")
        M, hh = grp9.build_bin2(G, H, K, binp)
        r = subprocess.run(["nice", "-n", "10", os.path.join(HERE, "bi9b"), binp, "exh", "0", os.path.join(HERE, "runs", f"two_{name}_h{h}_c{hcls}_{n}.edges")],
                           capture_output=True, text=True, env=dict(os.environ, CAP=str(cap)), timeout=540)
        line = [l for l in r.stdout.splitlines() if l.startswith("RESULT_EXH")]
        cost = int(line[0].split("best_cost=")[1].split()[0]) if line else 10**9
        print(f"K{n} ({kind}, orders {G.describe(K)}): {line[0] if line else r.stderr[-200:]}", flush=True)
        if cost < best[0]:
            best = (cost, n, K)
            import shutil
            shutil.copy(os.path.join(HERE, "runs", f"two_{name}_h{h}_c{hcls}_{n}.edges"), os.path.join(HERE, "runs", f"two_best_{name}_h{h}_c{hcls}.edges"))
    print(f"BEST two-subgroup cost {best[0]} (K index {best[1]}) time {time.time()-t0:.0f}s", flush=True)

if __name__ == "__main__":
    main()
