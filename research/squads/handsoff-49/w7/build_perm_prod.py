"""Direct products as permutation groups on disjoint supports (low memory). Usage: python3 build_perm_prod.py SPEC
SPEC examples: 'PSL2_2^3*cyc 15', 'A7*cyc 3', 'A6*cyc 21', 'PSL2_7*cyc 45', 'S5*cyc 42'. Writes tabs/<name>.bin."""
import sys, os
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, "/home/user/degree-diameter/research/squads/handsoff-49/tools")
import pgen, groups

def gens_of(name):
    """returns (list of generator permutations as tuples, number of points)"""
    if name.startswith("cyc"):
        k = int(name.split()[1])
        return [tuple(list(range(1, k)) + [0])], k
    if name.startswith("PSL2_") or name.startswith("PGL2_"):
        pgl = name.startswith("PGL2_")
        spec = name.split("_")[1]
        p, k = (int(x) for x in spec.split("^")) if "^" in spec else (int(spec), 1)
        poly = {(2, 1): [0], (3, 1): [0], (5, 1): [0], (7, 1): [0], (11, 1): [0], (13, 1): [0], (17, 1): [0],
                (19, 1): [0], (23, 1): [0], (2, 2): [1, 1], (3, 2): [2, 0], (5, 2): [2, 0], (2, 3): [1, 1, 0],
                (2, 4): [1, 1, 0, 0], (3, 3): [1, 1, 0]}[(p, k)]
        g = pgen.pl_gens(p, k, poly, pgl)
        return [tuple(x) for x in g], len(g[0])
    if name in ("S5", "A5", "S6", "A6", "S7", "A7"):
        n = int(name[1])
        if name[0] == "S":
            return [tuple([1, 0] + list(range(2, n))), tuple(list(range(1, n)) + [0])], n
        # A_n = <(0 1 2), (0 1 ... n-1) if n odd, (1 2 ... n-1) if n even>
        three = tuple([1, 2, 0] + list(range(3, n)))
        cyc = tuple(list(range(1, n)) + [0]) if n % 2 == 1 else tuple([0] + list(range(2, n)) + [1])
        return [three, cyc], n
    raise SystemExit("unknown " + name)

def direct(gA, nA, gB, nB):
    out = []
    for g in gA:
        out.append(tuple(list(g) + list(range(nA, nA + nB))))
    for g in gB:
        out.append(tuple(list(range(nA)) + [nA + x for x in g]))
    return out, nA + nB

if __name__ == "__main__":
    spec = sys.argv[1]
    a, b = spec.split("*")
    gA, nA = gens_of(a.strip())
    gB, nB = gens_of(b.strip())
    gens, n = direct(gA, nA, gB, nB)
    T = pgen.perm_table(gens)
    N = len(T)
    out = os.path.join(os.path.dirname(os.path.abspath(__file__)), "tabs", spec.replace("*", "x").replace(" ", "_") + ".bin")
    groups.write_bin(T, out)
    print(spec, N, out)
