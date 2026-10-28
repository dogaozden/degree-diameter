"""Rebuild a run's graph with levels.build, write edges, run ./apsp, and test (E1)-(E3) per transition."""
import sys, os, json, subprocess
HERE = os.path.dirname(os.path.abspath(__file__))
TH = os.path.join(HERE, '..', '..', '..', 'theorems', 'd5gq')
sys.path.insert(0, TH)
import numpy as np
from gqlib import Q4
from levels import build, write_edges
from repair import exact_conditions, brute_bad

def to_graph(d):
    G = Q4(3); s = d['s']; M = d['M']; Bs = d['Bs']; As = d['As']; alpha = d['alpha']
    types = ['H', 'H', 'H']
    Md = {}; R = {}
    for j in range(3):
        Md[(j, 1)] = np.array(M[j]); R[(j, 1)] = set(Bs[j])
    Bh = [[(j, Bs[j][h], (j, 1)) for j in range(3)] for h in range(s)]
    Ah = [[(j, M[(j - 1) % 3][As[(j - 1) % 3][g]], ((j - 1) % 3, 1)) for j in range(3)] for g in range(s)]
    Y = []
    if s >= 2:
        for h in range(s):
            for g in {alpha[h], alpha[(h + 1) % s]}:
                Y.append((h, g))
    elif s == 1:
        Y = [(0, 0)]
    n, E = build(G, types, Md, R, Bh, Ah, Y)
    return G, types, Md, R, n, E

if __name__ == '__main__':
    d = json.load(open(sys.argv[1]))
    out = sys.argv[2] if len(sys.argv) > 2 else sys.argv[1].replace('.json', '.edges')
    G, types, Md, R, n, E = to_graph(d)
    write_edges(out, n, E)
    res = subprocess.run([os.path.join(TH, 'apsp'), out, '5', '5'], capture_output=True, text=True).stdout.strip()
    print('n=%d hubs=%d' % (n, n - 240), res.splitlines()[-1] if res else 'NO OUTPUT')
    for j in range(3):
        t = (j, 1)
        ok, fails = exact_conditions(G, 'H', 'H', Md[t], R[t])
        print('transition', t, 'E1-E3 hold' if ok else 'E1-E3 FAIL', fails[:4], 'brute_bad(2 levels)=', brute_bad(G, 'H', 'H', Md[t], R[t]))
