"""Compare haarcheck_pq output (X.pq.out) with build_haar2.py output (X.b2.out) for each test file."""
import re, sys, glob, os
def parse_pq(path):
    t = open(path).read()
    m = re.search(r"from \(e,A\): ecc=(\d+) unreached=(\d+)", t)
    k = re.search(r"from \(e,B\): ecc=(\d+) unreached=(\d+)", t)
    v = re.findall(r"^(VALID|INVALID) .*vertices=(\d+) eccA=(-?\d+) eccB=(-?\d+)", t, re.M)
    if not (m and k and v):
        return None
    verdict, verts, ea, eb = v[-1]
    return dict(verdict=verdict, vertices=int(verts), eccA=int(ea), eccB=int(eb),
                uA=int(m.group(2)), uB=int(k.group(2)))
def parse_b2(path):
    t = open(path).read()
    m = re.search(r"ecc from A = (\d+) unreached (\d+)", t)
    k = re.search(r"ecc from B = (\d+) unreached (\d+)", t)
    v = re.findall(r"^(VALID|INVALID) .*vertices=(\d+)", t, re.M)
    if not (m and k and v):
        return None
    verdict, verts = v[-1]
    return dict(verdict=verdict, vertices=int(verts), eccA=int(m.group(1)), eccB=int(k.group(1)),
                uA=int(m.group(2)), uB=int(k.group(2)))
bad = 0
for pq in sorted(glob.glob("*.pq.out") + glob.glob("tests/*.pq.out")):
    base = pq[:-len(".pq.out")]
    b2 = base + ".b2.out"
    a = parse_pq(pq) if os.path.exists(pq) else None
    b = parse_b2(b2) if os.path.exists(b2) else None
    if a is None or b is None:
        print("NOPARSE", base, "pq:", a is not None, "b2:", b is not None); bad += 1; continue
    same = a == b
    bad += (not same)
    print("MATCH   " if same else "MISMATCH", base, "verdict", a["verdict"], b["verdict"], "vertices", a["vertices"],
          "ecc", (a["eccA"], a["eccB"]), (b["eccA"], b["eccB"]), "unreached", (a["uA"], a["uB"]), (b["uA"], b["uB"]))
print("mismatches or unparsed:", bad)
