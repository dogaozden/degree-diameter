import sys
for path in sys.argv[1:]:
    tok = open(path).read().split()
    m = int(tok[0]); vals = list(map(int, tok[1:]))
    assert len(vals) == m*m, (path, len(vals), m)
    T = [vals[i*m:(i+1)*m] for i in range(m)]
    ok = all(T[0][j] == j and T[j][0] == j for j in range(m))
    ok = ok and all(sorted(r) == list(range(m)) for r in T) and all(sorted(T[i][j] for i in range(m)) == list(range(m)) for j in range(m))
    # associativity
    ok = ok and all(T[T[a][b]][c] == T[a][T[b][c]] for a in range(m) for b in range(m) for c in range(m))
    print(path, m, "GROUP" if ok else "BAD")
