#!/usr/bin/env python3
"""Covering certificates for the lift record nb_4_10_12416 (job d4D10b).

  D4D10b: delta 4, diameter 10, 12,416 vertices. G = Z_97 x|_19 Z_64 (order 6,208); S = the 4 elements of
          research/lifts/sols/d4D10_n12416_haar_meta97_64_19.txt. Diameter by Haar/Diam10.lean
          (haar_isBipartiteDegDiam10_of_equiv), as for nb_4_10_12246 in LiftA/D4D10.

The templates are those of research/lean-haarD/gen_lift58410.py (the D4D10 record of job lift58410). This script
imports them and writes the same stage layout under lean/BipartiteDD/Haar/D4D10b/, with the group module
`D4D10b/Meta97.lean` in place of `LiftA/Meta157.lean`. Every word is re-checked by direct multiplication
(find_codes), so a failed certificate stops the script before anything is written.

Usage: python3 research/lean-haarD/gen_d4D10b.py [OUT]
(default OUT = lean/BipartiteDD/Haar/D4D10b). Axioms.lean and Axioms.out.txt are written by hand.
"""
import importlib.util
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
_spec = importlib.util.spec_from_file_location("gen_lift58410", os.path.join(HERE, "gen_lift58410.py"))
G = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(G)

RECORD = dict(
    sol="d4D10_n12416_haar_meta97_64_19.txt", m=97, k=64, r=19, ns=4, N=6208,
    nrec=12416, delta=4, D=10, stages=16, bits=18, base=4,
    covers=[("D", 9, "B")],
    grp="Meta97", mod="D4D10b",
)


def ns(text):
    """Namespaces and file names of the new layout (the templates say LiftA)."""
    text = text.replace("BipartiteDD.Haar.LiftA.Meta97", "BipartiteDD.Haar.D4D10b.Meta97")
    text = text.replace("BipartiteDD.Haar.LiftA.D4D10b", "BipartiteDD.Haar.D4D10b")
    return text.replace("gen_lift58410.py", "gen_d4D10b.py")


def main():
    out_root = sys.argv[1] if len(sys.argv) > 1 else os.path.join(G.REPO, "lean", "BipartiteDD", "Haar", "D4D10b")
    spec = RECORD
    mul, inv = G.group(spec["m"], spec["k"], spec["r"])
    S = G.parse_sol(os.path.join(G.SOLS, spec["sol"]), spec)
    print("S =", S)
    codes = {}
    for cname, L, side in spec["covers"]:
        codes[cname] = G.find_codes(mul, inv, S, spec, L, side)
        print(" cover", cname, "letters", L, "entries", len(codes[cname]), "max code", max(codes[cname]),
              "< base^L", spec["base"] ** L)
    G.write(os.path.join(out_root, f"{spec['grp']}.lean"), ns(G.meta_module(spec)))
    G.write(os.path.join(out_root, "Check.lean"), ns(G.check_module(spec, S)))
    size = spec["N"] // spec["stages"]
    assert size * spec["stages"] == spec["N"]
    for cname, _, _ in spec["covers"]:
        for s in range(spec["stages"]):
            G.write(os.path.join(out_root, f"Stage{cname}{s:02d}.lean"),
                    ns(G.stage_module(spec, cname, s, codes[cname][s * size:(s + 1) * size])))
    G.write(os.path.join(out_root, "Cover.lean"), ns(G.cover_module(spec)))
    G.write(os.path.join(out_root, "Record.lean"), ns(G.record_module(spec)))


if __name__ == "__main__":
    main()
