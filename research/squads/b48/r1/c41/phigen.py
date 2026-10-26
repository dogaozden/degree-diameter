# c41: build group table (groups.py) and a Z2-valued homomorphism phi (kernel of index 2 exists iff G/K even order,
# K = <squares, commutators>). Writes OUT.bin (table) and OUT.phi (N lines, 0/1). Usage: phigen.py SPEC OUT
import sys
sys.path.insert(0, "/home/user/degree-diameter/research/squads/b48/tools")
import numpy as np, groups

def subgroup(T, gens):
    H = {0}; frontier = [0]
    gens = list(gens)
    while frontier:
        new = []
        for h in frontier:
            for g in gens:
                x = int(T[h, g])
                if x not in H:
                    H.add(x); new.append(x)
        frontier = new
    return H

def main(spec, out):
    T = groups.table(spec)
    N = len(T)
    inv = [int(np.where(T[g] == 0)[0][0]) for g in range(N)]
    # generators of K = <g^2, [g,h]>
    cand = set()
    for g in range(N):
        cand.add(int(T[g, g]))
    for g in range(N):
        for h in range(N):
            cand.add(int(T[T[inv[g], inv[h]], T[g, h]]))
    K = {0}
    for x in sorted(cand):
        if x not in K:
            K = subgroup(T, list(K) + [x]) if len(K) > 1 else subgroup(T, [x])
    idx = N // len(K)
    if idx == 1:
        print("no index-2 subgroup (G/K trivial)"); sys.exit(1)
    # basis of G/K (elementary abelian 2-group): greedy choice of coset reps
    reps = []; span = set(K)
    for g in range(N):
        if g not in span:
            reps.append(g)
            # new span = span * <g>
            new = set(span); cur = set(span)
            while True:
                nxt = set()
                for s in cur:
                    t = int(T[s, g])
                    if t not in new:
                        nxt.add(t)
                if not nxt: break
                new |= nxt; cur = nxt
            span = new
    r = len(reps)
    # label every element by its coordinate vector: g in rep_v * K
    lab = [-1] * N
    Kl = sorted(K)
    for v in range(1 << r):
        rep = 0
        for i in range(r):
            if (v >> i) & 1: rep = int(T[rep, reps[i]])
        for k in Kl:
            x = int(T[rep, k])
            if lab[x] < 0: lab[x] = v
    assert min(lab) >= 0
    phi = [lab[g] & 1 for g in range(N)]   # first coordinate
    assert sum(phi) == N // 2
    groups.write_bin(T, out + ".bin")
    with open(out + ".phi", "w") as f:
        f.write("\n".join(map(str, phi)) + "\n")
    print(f"spec={spec} N={N} |K|={len(K)} r={r} index2_subgroup_ok")

if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2])
