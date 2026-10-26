# Random-voltage screen: for each 3+3 base and each group, score NS random voltage assignments with lift eval.
import subprocess, glob, os, sys
import numpy as np
T = "/home/user/degree-diameter/research/squads/b48/tools"
HERE = "/home/user/degree-diameter/research/squads/b48/r1/c20"
NS = int(os.environ.get("NS", "2000"))
META = [("meta_96_4_7", "meta:96:4:7", 384), ("meta_48_8_5", "meta:48:8:5", 384),
        ("meta_65_6_4", "meta:65:6:4", 390), ("meta_35_12_2", "meta:35:12:2", 420),
        ("meta_25_16_7", "meta:25:16:7", 400), ("meta_41_10_4", "meta:41:10:4", 410),
        ("meta_97_4_22", "meta:97:4:22", 388), ("meta_127_3_19", "meta:127:3:19", 381),
        ("meta_49_8_48", "meta:49:8:48", 392)]
NONMETA = [("sl2_3x16", "groups/sl2_3x16.bin", 384), ("s4x16", "groups/s4x16.bin", 384),
           ("a4x32", "groups/a4x32.bin", 384), ("agl1_5x20", "groups/agl1_5x20.bin", 400),
           ("heis3x14", "groups/heis3x14.bin", 378), ("a5x7", "groups/a5x7.bin", 420),
           ("semi7_8", "groups/semi7_8.bin", 392), ("sl2_3x17", "groups/sl2_3x17.bin", 408),
           ("s4x17", "groups/s4x17.bin", 408)]
groups_all = [(nm, g, N) for nm, g, N in META] + [(nm, os.path.join(HERE, g), N) for nm, g, N in NONMETA]
bases = sorted(glob.glob(os.path.join(HERE, "bases", "b33_*.txt")))
rng = np.random.default_rng(int(os.environ.get("SEED", "1")))
out = open(os.path.join(HERE, "screen.tsv"), "w")
out.write("base\tgroup\tN\tvalid\tmin_cost\tmedian_cost\n")
for bp in bases:
    for gname, gspec, N in groups_all:
        V = rng.integers(0, N, size=(NS, 12))
        inp = "\n".join(" ".join(map(str, row)) for row in V) + "\n"
        r = subprocess.run([f"{T}/lift", bp, gspec, "4", "8", "eval"], input=inp, capture_output=True, text=True)
        vals = [l.strip() for l in r.stdout.split("\n") if l.strip()]
        costs = [int(v) for v in vals if v != "invalid"]
        if not costs:
            out.write(f"{os.path.basename(bp)}\t{gname}\t{N}\t0\tNA\tNA\n"); continue
        out.write(f"{os.path.basename(bp)}\t{gname}\t{N}\t{len(costs)}\t{min(costs)}\t{int(np.median(costs))}\n")
        out.flush()
out.close()
print("done")
