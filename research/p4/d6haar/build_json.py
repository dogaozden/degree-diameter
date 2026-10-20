"""Build the Haar graph of a haar_dd solution as record JSON (records/bipartite_dd format).

Usage: python3 build_json.py SOLUTION.txt OUT.json
Solution file: "D d N c table" then d lines with element indices x of G = G0 x Z_c, x = g*c + z, where g indexes the
table of G0 (groups.py). Vertex (x, A) is x, (x, B) is N + x; edge (x, A) ~ (s*x, B) for s in S.
The group is rebuilt from its name with groups.py (not read from the table file), then checked against the table.
"""
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import groups  # noqa: E402


def main(sol, out):
    lines = [l.split() for l in open(sol) if l.strip()]
    D, d, N, c = map(int, lines[0][:4])
    table_path = lines[0][4]
    second = lines[0][5] if len(lines[0]) > 5 else str(c)   # haar_dd2: a number (Z_c) or a second table file
    name = os.path.basename(table_path)[:-4]
    T0 = groups.build(name)
    els = groups.LAST_ELEMENTS if "__x__" not in name else None   # read before building the second factor
    N0 = len(T0)
    groups.check_table(T0, trials=20000)
    with open(os.path.join(HERE, table_path) if not os.path.isabs(table_path) else table_path) as f:
        assert int(f.readline()) == N0
        for g in range(N0):
            assert list(map(int, f.readline().split())) == T0[g], "table file differs from groups.py"
    assert N == N0 * c
    S = [int(l[0]) for l in lines[1:1 + d]]
    assert len(set(S)) == d

    if second.isdigit():
        T1 = [[(z + w) % c for w in range(c)] for z in range(c)]
        name1 = f"Z_{c}"
    else:
        name1 = os.path.basename(second)[:-4]
        T1 = groups.build(name1)
        groups.check_table(T1, trials=20000)
        assert len(T1) == c

    def mul(x, y):
        return T0[x // c][y // c] * c + T1[x % c][y % c]

    edges = [[x, N + mul(s, x)] for x in range(N) for s in S]
    desc = [[x // c, x % c] for x in S]
    con = {"group": f"{name} x {name1}" if c > 1 else name, "group_order": N, "D": D,
           "edges": "(x, A) ~ (s x, B), vertex (x, A) = x, (x, B) = N + x, x = g*c + z",
           "S_index": S, "S_as_(g0_index, z)": desc}
    if els is not None:
        con["S_g0_elements"] = [repr(els[x // c]) for x in S]
    json.dump({"case": f"d{d}D{D}", "value": 2 * N, "output": [2 * N, edges], "construction": con}, open(out, "w"))
    print(out, 2 * N, len(edges))


if __name__ == "__main__":
    main(*sys.argv[1:3])
