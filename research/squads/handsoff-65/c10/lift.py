# lift.py BASE GTABLE > edges : lift a vl base (voltages as indices of GTABLE) to an edge list; vertex (v,h) = v*m+h
import sys
def main():
    base, gtab = sys.argv[1], sys.argv[2]
    with open(gtab) as f:
        m = int(f.readline()); T = [list(map(int, f.readline().split())) for _ in range(m)]
    with open(base) as f:
        toks = f.read().split('\n')
    B, E = map(int, toks[0].split())
    E_lines = [l.split() for l in toks[2:2 + E]]
    out = [str(B * m)]
    for l in E_lines:
        u, w, v = int(l[0]), int(l[1]), (int(l[2]) if len(l) > 2 else 0)
        for h in range(m):
            out.append("%d %d" % (u * m + h, w * m + T[h][v]))
    print("\n".join(out))
main()
