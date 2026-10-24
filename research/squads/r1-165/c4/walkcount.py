import itertools
def counts(mult):
    # base vertices: A1=0, A2=1, B1=2, B2=3; mult[a][b] parallel darts a->b (b indexes B1,B2)
    darts = []
    for a in range(2):
        for b in range(2):
            for j in range(mult[a][b]):
                darts.append((a, 2 + b))
    nd = len(darts)
    res = {}
    for s in range(4):
        cnt = {}
        for d1 in range(nd):
            if s not in darts[d1]: continue
            x1 = darts[d1][1] if darts[d1][0] == s else darts[d1][0]
            for d2 in range(nd):
                if d2 == d1 or x1 not in darts[d2]: continue
                x2 = darts[d2][1] if darts[d2][0] == x1 else darts[d2][0]
                for d3 in range(nd):
                    if d3 == d2 or x2 not in darts[d3]: continue
                    x3 = darts[d3][1] if darts[d3][0] == x2 else darts[d3][0]
                    for d4 in range(nd):
                        if d4 == d3 or x3 not in darts[d4]: continue
                        t = darts[d4][1] if darts[d4][0] == x3 else darts[d4][0]
                        cnt[t] = cnt.get(t, 0) + 1
        res[s] = dict(sorted(cnt.items()))
    return res
for name, mult in [("type1 (1,3,3,1)", [[1,3],[3,1]]), ("type2 (2,2,2,2)", [[2,2],[2,2]])]:
    print(name, counts(mult))
