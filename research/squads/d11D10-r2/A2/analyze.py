# Analyse DUMP lines of haar_sym_A2 RANDORB runs: properties of the orbit generator x = orbit[0]
import re, sys, collections
sys.path.insert(0, "/home/user/degree-diameter/research/squads/d11D10-r2/A2")
import gf
from gf import MUL, ADD, NEG, INV, mmul, pnorm, frob, pow_order, trace, det, in_gf3, poly_str, disc_class, sub, digits

def parse(path):
    rows = []
    for line in open(path):
        if not line.startswith("DUMP"):
            continue
        head, *orbs = line.rstrip("\n").split(" | ")
        m = re.match(r"DUMP (\d+) cost (\d+)", head)
        t, cost = int(m.group(1)), int(m.group(2))
        orbit = []
        for o in orbs:
            f = o.split()
            a, b, c, d = map(int, f[:4]); z = int(f[4][1:])
            orbit.append(((a, b, c, d), z))
        rows.append((t, cost, orbit))
    return rows

def features(orbit):
    x, zx = orbit[0]
    F = {}
    F["tr"] = trace(x)
    F["tr_gf3"] = in_gf3(trace(x))
    F["disc"] = disc_class(x)
    F["ord"] = pow_order(x)
    F["det1"] = det(x) == 1
    F["entries_gf3"] = all(in_gf3(v) for v in x)
    y = orbit[1][0]
    F["comm_alpha"] = pnorm(mmul(x, y)) == pnorm(mmul(y, x))
    F["tr_alpha_eq_frobtr"] = trace(y) == frob((trace(x), 0, 0, 1), 1)[0]
    F["traces_orbit"] = tuple(trace(o[0]) for o in orbit)
    F["z0"] = zx
    return F

if __name__ == "__main__":
    rows = parse(sys.argv[1])
    print("samples", len(rows), "cost min/max", min(r[1] for r in rows), max(r[1] for r in rows))
    thr = int(sys.argv[2]) if len(sys.argv) > 2 else 10**5
    deg = [r for r in rows if r[1] >= thr]
    print("degenerate (cost >= %d): %d of %d = %.3f" % (thr, len(deg), len(rows), len(deg) / max(1, len(rows))))
    for name, grp in (("degenerate", deg), ("normal", [r for r in rows if r[1] < thr])):
        print("==", name, "costs:", sorted(collections.Counter(r[1] for r in grp).items())[:12])
    cnt = collections.defaultdict(collections.Counter)
    for t, cost, orbit in rows:
        F = features(orbit)
        tag = "DEG" if cost >= thr else "OK "
        for key in ("tr_gf3", "disc", "ord", "entries_gf3", "comm_alpha", "tr_alpha_eq_frobtr"):
            cnt[key][(tag, F[key])] += 1
    for key in cnt:
        print(key, sorted(cnt[key].items(), key=lambda kv: str(kv)))
