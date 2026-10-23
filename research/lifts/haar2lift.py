"""Convert a haar_gen3 solution file (sl/psl/pgl p prime, meta, cyc; times Z_n) to a lift.c solution file
(dipole base), so that lift check / verify_lift.py / apsp can check it.

Usage: python3 haar2lift.py HAARSOL > LIFTSOL
haar_gen3 convention (g,A) ~ (s g, B) is lift.c's (0,g) ~ (1, a g) with a = s.
"""
import re
import sys


def main():
    lines = open(sys.argv[1]).read().split("\n")
    head = lines[0].split()
    d, D = int(head[0]), int(head[1])
    i = head.index("n")
    spec, n = head[2:i], int(head[i + 1])
    kind = spec[0]
    if kind in ("sl", "psl", "pgl"):
        assert len(spec) == 2, "only prime fields are supported by lift.c"
        group = f"{kind} {spec[1]}"
    elif kind == "meta":
        group = " ".join(spec)
    elif kind == "cyc":
        group = None
    else:
        sys.exit("unsupported group family " + kind)
    parts = ([group] if group else []) + ([f"cyc {n}"] if n > 1 or not group else [])
    print(f"# converted from haar_gen3 solution {sys.argv[1]}")
    print(f"lift D {D} Delta {d} k 2 N 0 n 0 cost 0")
    print("group " + " x ".join(parts))
    print("k 2")
    for l in lines[1:]:
        if not l.strip():
            continue
        z = re.search(r"z=(\d+)", l).group(1)
        m = re.search(r"mat\(([-\d,]+)\)", l)
        mm = re.search(r"meta\(a=(\d+),j=(\d+)\)", l)
        if m:
            comp = m.group(1)
        elif mm:
            comp = f"{mm.group(1)},{mm.group(2)}"
        else:
            comp = None
        elem = "|".join(([comp] if comp is not None else []) + ([z] if (n > 1 or comp is None) else []))
        print(f"e 0 1 = {elem}")


if __name__ == "__main__":
    main()
