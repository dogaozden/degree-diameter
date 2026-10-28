"""Explicit hub graph generator (see construction.md).

usage: python3 gen_hubs.py KA KB DELTA OUT.edges
  Writes an edge file (first line "n m", then "u v" lines; A = colour 0 = first vertex class) and prints the
  class sizes. Uses, in order:
    1. PG(2,s) incidence + pendants      (any s prime power, s+1 <= delta, N_s <= KA,KB <= N_s*(delta-s))
    2. W(q) incidence + line/point pendants (q=2..5, same pendant rule on one line and one pencil)
    3. clique of PG(2,s_k) cores with cross edges (sizes and seeds from cliques_d{delta}.json)
"""
import sys, json, os
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from hubgen import pg_window_graph, gq_window_graph, pg2
from clique import build_graph

PRIME_POWERS = [2, 3, 4, 5, 7, 8, 9]

def window_graph(KA, KB, delta):
    for s in PRIME_POWERS:
        if s + 1 > delta: continue
        N = s * s + s + 1
        if N <= min(KA, KB) and max(KA, KB) <= N * (delta - s):
            return pg_window_graph(s, KA, KB, delta), f"PG(2,{s})+pendants"
    for q in [2, 3, 4, 5]:
        if q + 1 > delta: continue
        N = (q + 1) * (q * q + 1)
        if N <= min(KA, KB) and max(KA, KB) <= N + (q + 1) * (delta - q - 1):
            return gq_window_graph(q, KA, KB, delta), f"W({q})+pendants"
    return None, None

def clique_graph(K, delta):
    table = os.path.join(HERE, f"cliques_d{delta}.json")
    if not os.path.exists(table): return None, None
    t = json.load(open(table))
    if str(K) not in t: return None, None
    rec = t[str(K)]
    G = build_graph(rec["sizes"], delta, seed=rec["seed"])
    return G, f"clique {rec['sizes']} seed {rec['seed']}"

def generate(KA, KB, delta):
    G, label = window_graph(KA, KB, delta)
    if G is None and KA == KB:
        G, label = clique_graph(KA, delta)
    return G, label

if __name__ == "__main__":
    KA, KB, delta, out = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
    G, label = generate(KA, KB, delta)
    if G is None:
        print("NOT COVERED"); sys.exit(1)
    G.write(out)
    print(f"wrote {out}: {label}; classes A={KA} B={KB}; edges={len(G.edges)}")
