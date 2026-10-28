"""Independent certifier for card e05: disjoint totally singular lines of Q(6,16).

usage: python3 -I certify.py SETS_COORDS.txt [HEX_FILE]
SETS_COORDS.txt: one set per line, 17 points, each point written as 7 hex digits (GF(16) coordinates,
element a0+2a1+4a2+8a3, bit i = coefficient of x^i, modulus x^4+x+1, addition = XOR).
Checks (GF(16) arithmetic here is by discrete-log tables of the generator x, not the search code's multiplication):
 1. every point is nonzero and singular: Q(x) = x0x4 + x1x5 + x2x6 + x3^2 = 0 (char 2);
 2. each set is exactly the 17 points of the projective line spanned by two of its points (rank 2, spans match);
 3. pairwise orthogonal inside each set for b(x,y) = x0y4+x4y0+x1y5+x5y1+x2y6+x6y2 + 2 x3y3 (last term computed
    literally and equal to 0 in characteristic 2);
 4. the 17K normalised points are pairwise distinct (sets pairwise disjoint);
 5. (optional HEX_FILE) every point is a point of the hexagon file H(16) (same point set as Q(6,16)).
Prints one JSON line."""
import sys, json

EXP = [0] * 30
LOG = [0] * 16
v = 1
for i in range(15):
    EXP[i] = v
    LOG[v] = i
    v <<= 1
    if v & 16:
        v ^= 0b10011          # x^4 = x + 1
assert len(set(EXP[:15])) == 15 and set(EXP[:15]) == set(range(1, 16)), "x is not primitive"
for i in range(15, 30):
    EXP[i] = EXP[i - 15]


def mul(a, b):
    if a == 0 or b == 0:
        return 0
    return EXP[LOG[a] + LOG[b]]


def inv(a):
    return EXP[(15 - LOG[a]) % 15]


def add(a, b):
    return a ^ b


def normalise(p):
    for c in p:
        if c:
            s = inv(c)
            return tuple(mul(s, t) for t in p)
    raise ValueError("zero vector")


def Q(p):
    x0, x1, x2, x3, x4, x5, x6 = p
    s = add(mul(x0, x4), mul(x1, x5))
    s = add(s, mul(x2, x6))
    return add(s, mul(x3, x3))


def b(p, r):
    s = 0
    s = add(s, mul(p[0], r[4])); s = add(s, mul(p[4], r[0]))
    s = add(s, mul(p[1], r[5])); s = add(s, mul(p[5], r[1]))
    s = add(s, mul(p[2], r[6])); s = add(s, mul(p[6], r[2]))
    t = mul(p[3], r[3])
    s = add(s, add(t, t))             # 2 x3 y3 = 0 in characteristic 2
    return s


def span_points(u, w):
    out = {normalise(u)}
    for t in range(16):
        out.add(normalise(tuple(add(mul(t, a), c) for a, c in zip(u, w))))
    return out


def main():
    path = sys.argv[1]
    hexpath = sys.argv[2] if len(sys.argv) > 2 else None
    sets = []
    bad = []
    with open(path) as f:
        for ln, line in enumerate(f):
            toks = line.split()
            if not toks:
                continue
            if len(toks) != 17 or any(len(t) != 7 for t in toks):
                bad.append(("format", ln)); continue
            pts = [tuple(int(ch, 16) for ch in t) for t in toks]
            sets.append((ln, pts))
    seen = {}
    nbad_quadric = nbad_span = nbad_orth = nbad_dup = 0
    allpts = []
    for ln, pts in sets:
        npts = []
        ok = True
        for p in pts:
            if not any(p):
                ok = False; break
            n = normalise(p)
            if Q(n) != 0:
                nbad_quadric += 1; ok = False
            npts.append(n)
        if not ok:
            bad.append(("zero-or-quadric", ln)); continue
        if len(set(npts)) != 17:
            nbad_span += 1; bad.append(("repeated point", ln)); continue
        u, w = npts[0], npts[1]          # distinct projective points: span is a line if the sets agree
        if set(span_points(u, w)) != set(npts):
            nbad_span += 1; bad.append(("not a projective line", ln)); continue
        orth = True
        for i in range(17):
            for j in range(i + 1, 17):
                if b(npts[i], npts[j]) != 0:
                    orth = False
        if not orth:
            nbad_orth += 1; bad.append(("not orthogonal", ln)); continue
        for p in npts:
            if p in seen:
                nbad_dup += 1; bad.append(("point reused", ln, seen[p])); break
            seen[p] = ln
        allpts.extend(npts)
    valid_lines = len(sets) - len({x[1] for x in bad if x[0] != "format"})
    hex_ok = None
    if hexpath:
        import numpy as np
        with open(hexpath, "rb") as f:
            q, N, L = np.frombuffer(f.read(12), dtype="<i4")
            f.seek(12 + 4 * int(L) * (int(q) + 1))
            co = np.frombuffer(f.read(int(N) * 7), dtype=np.uint8).reshape(int(N), 7)
        keys = set(int(sum(int(c) * 16 ** i for i, c in enumerate(row))) for row in co)
        hex_ok = all(sum(c * 16 ** i for i, c in enumerate(p)) in keys for p in allpts)
    res = {
        "file": path,
        "sets_read": len(sets),
        "valid_sets": valid_lines,
        "points_distinct": len(seen),
        "points_expected": 17 * valid_lines,
        "bad_quadric_points": nbad_quadric,
        "bad_line_structure": nbad_span,
        "non_orthogonal_sets": nbad_orth,
        "reused_points": nbad_dup,
        "all_points_in_hex_file": hex_ok,
        "problems": bad[:5],
    }
    res["valid"] = (len(bad) == 0 and len(seen) == 17 * len(sets) and (hex_ok is None or hex_ok))
    res["K_certified"] = len(sets) if res["valid"] else valid_lines
    print(json.dumps(res))


if __name__ == "__main__":
    main()
