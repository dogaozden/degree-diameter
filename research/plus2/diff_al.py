"""Compare each found +2 graph with lib.araujo_lopez_graph(q) under the identity labelling."""
import json, sys
sys.path.insert(0, str(__import__('pathlib').Path(__file__).resolve().parents[2]) + '/problems/bipartite_dd')
import lib

FILES = {9: 'records/bipartite_dd/d11D3/192-c-d3fam-g001-c00.json',
         11: 'records/bipartite_dd/d13D3/276-c-d3fam-g003-c19.json',
         13: 'records/bipartite_dd/d15D3/376-c-d3fam-w2-g002-c12.json'}
ROOT = str(__import__('pathlib').Path(__file__).resolve().parents[2]) + '/'

def norm(edges):
    return {(min(u, v), max(u, v)) for u, v in edges}

if __name__ == '__main__':
  for q, f in FILES.items():
    n0, e0 = lib.araujo_lopez_graph(q)
    n1, e1 = json.load(open(ROOT + f))['output']
    A, B = norm(e0), norm(e1)
    print(f'q={q}: AL n={n0} m={len(A)}; found n={n1} m={len(B)}')
    print('  removed from AL:', len(A - B), ' added:', len(B - A))
