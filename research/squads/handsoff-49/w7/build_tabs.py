"""Build group tables for bicos (w7). Usage: python3 build_tabs.py NAME [NAME...]  -> tabs/NAME.bin"""
import sys, os
import numpy as np
sys.path.insert(0, "/home/user/degree-diameter/research/squads/handsoff-49/tools")
import groups
import pgen

HERE = os.path.dirname(os.path.abspath(__file__))

def perm_named(name):
    spec = {"S5": "S5", "A5": "A5", "S6": "S6", "A6": "A6", "S7": "S7", "A7": "A7"}[name]
    if spec == "S5":
        gens = [tuple([1, 0] + list(range(2, 5))), tuple(list(range(1, 5)) + [0])]
    elif spec == "A5":
        gens = [(1, 2, 0, 3, 4), (1, 2, 3, 4, 0)]
    elif spec == "S6":
        gens = [tuple([1, 0] + list(range(2, 6))), tuple(list(range(1, 6)) + [0])]
    elif spec == "A6":
        gens = [(1, 2, 0, 3, 4, 5), (0, 2, 3, 4, 5, 1)]
    elif spec == "S7":
        gens = [tuple([1, 0] + list(range(2, 7))), tuple(list(range(1, 7)) + [0])]
    elif spec == "A7":
        gens = [(1, 2, 0, 3, 4, 5, 6), (1, 2, 3, 4, 5, 6, 0)]
    return pgen.perm_table(gens)

def pl_table(name):
    # PSL2_p^k, PGL2_p^k
    pgl = name.startswith("PGL2_")
    spec = name.split("_")[1]
    if "^" in spec:
        p, k = (int(x) for x in spec.split("^"))
    else:
        p, k = int(spec), 1
    poly = {(2, 1): [0], (3, 1): [0], (5, 1): [0], (7, 1): [0], (11, 1): [0], (13, 1): [0], (17, 1): [0],
            (19, 1): [0], (23, 1): [0], (2, 2): [1, 1], (3, 2): [2, 0], (5, 2): [2, 0], (2, 3): [1, 1, 0],
            (2, 4): [1, 1, 0, 0], (3, 3): [1, 1, 0]}[(p, k)]
    return pgen.perm_table(pgen.pl_gens(p, k, poly, pgl))

def build(name):
    if "*" in name:
        a, b = name.split("*")
        return groups.t_prod(build(a.strip()), build(b.strip()))
    if name in ("S5", "A5", "S6", "A6", "S7", "A7"):
        return perm_named(name)
    if name.startswith("PSL2_") or name.startswith("PGL2_"):
        return pl_table(name)
    if " x " in name or name.startswith(("psl2", "pgl2", "sl2", "meta", "cyc", "agl1", "heis", "semi")):
        return groups.table(name)
    # products "BASE*CYC" like S5*cyc42
    if "*" in name:
        a, b = name.split("*")
        T1 = build(a)
        T2 = build(b)
        return groups.t_prod(T1, T2)
    raise SystemExit("unknown " + name)

if __name__ == "__main__":
    for name in sys.argv[1:]:
        T = build(name) if "*" not in name else build(name)
        N = len(T)
        out = os.path.join(HERE, "tabs", name.replace("*", "x").replace(" ", "_") + ".bin")
        groups.write_bin(T, out)
        print(name, N, out, flush=True)
