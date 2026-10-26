import sys
# usage: mkbase.py NAME  -> writes NAME.base from a multiplicity matrix given in MATS
MATS = {
 "B3a": [[3,3,3],[3,3,3],[3,3,3]],
 "B3b": [[4,3,2],[3,2,4],[2,4,3]],
 "B3c": [[5,2,2],[2,5,2],[2,2,5]],
 "B4a": [[3,2,2,2],[2,3,2,2],[2,2,3,2],[2,2,2,3]],
 "B4b": [[3,3,2,1],[3,2,3,1],[2,3,1,3],[1,1,3,4]],
 "B4c": [[4,4,1,0],[4,4,0,1],[1,0,4,4],[0,1,4,4]],
 "B4d": [[5,2,1,1],[2,5,1,1],[1,1,4,3],[1,1,3,4]],
 "B2a": [[1,8],[8,1]],
 "B2b": [[2,7],[7,2]],
 "B2c": [[3,6],[6,3]],
 "B2d": [[4,5],[5,4]],
}
for name, M in MATS.items():
    k = len(M)
    assert all(sum(r)==9 for r in M) and all(sum(M[i][j] for i in range(k))==9 for j in range(k)), name
    edges = [(i, k+j) for i in range(k) for j in range(k) for _ in range(M[i][j])]
    with open(name + ".base", "w") as f:
        f.write(f"{2*k} {len(edges)}\n")
        for u, v in edges:
            f.write(f"{u} {v}\n")
    print(name, 2*k, len(edges))
