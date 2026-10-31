# usage: haar.py TABLE S1,S2,...  -> edge list on stdout: Haar graph H(G,S): (g,0)~(g*s,1); side1 vertex = m + index
import sys
def load(path):
    with open(path) as f:
        m = int(f.readline())
        T = [list(map(int, f.readline().split())) for _ in range(m)]
    return m, T
if __name__ == "__main__":
    m, T = load(sys.argv[1])
    S = [int(x) for x in sys.argv[2].split(',')]
    E = []
    for g in range(m):
        for s in S:
            E.append((g, m + T[g][s]))
    out = [str(2 * m)] + ["%d %d" % e for e in E]
    print("\n".join(out))
