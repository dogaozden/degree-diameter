# c5 helper: parse the .hubs3 layout and the hub graph (no edits to any shared file)
import sys
HUBS3 = "/home/user/degree-diameter/research/frontier/sols/d12D7_hex9_spread730_clhaarPSL9x40_n693100.hubs3"
N = 66430; B = 132860; NV = 10 * N   # main vertices 0..664299; line-side hubs 664300.., point-side after
def load():
    L = open(HUBS3).read().split("\n")
    HL, HP, m = map(int, L[0].split())
    oL = [list(map(int, L[1 + j].split())) for j in range(HL)]
    oP = [list(map(int, L[1 + HL + k].split())) for k in range(HP)]
    E = []
    for e in range(m):
        j, k = map(int, L[1 + HL + HP + e].split())
        E.append((j, k))
    return HL, HP, oL, oP, E
def adjacency(HL, HP, E):
    aL = [[] for _ in range(HL)]; aP = [[] for _ in range(HP)]
    for j, k in E:
        aL[j].append(k); aP[k].append(j)
    return aL, aP
