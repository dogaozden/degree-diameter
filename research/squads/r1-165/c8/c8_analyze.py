#!/usr/bin/env python3
"""C8: where does the diameter defect come from? Pure-Python BFS (depth 5) from one source per type,
counting vertices NOT reached within 5 steps, by target type. Two graphs are compared:
  'with solids'  : the moved graph (solid orbit attached)
  'removal only' : the same moves, but the solid edges deleted (solids isolated), so that damage
                   to the flag graph itself is separated from the cost of attaching the solids.
Usage: c8_analyze.py [moves.json]"""
import json, os, sys
from collections import deque
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import c8_lift as C


def build_adj(NB):
    adj = [[] for _ in range(C.NTOT)]
    for a in range(C.NA):
        for b in NB[a]:
            adj[a].append(b)
            adj[b].append(a)
    return adj


def ball_defect(adj, src, D=5):
    dist = {src: 0}
    dq = deque([src])
    while dq:
        x = dq.popleft()
        if dist[x] == D:
            continue
        for y in adj[x]:
            if y not in dist:
                dist[y] = dist[x] + 1
                dq.append(y)

    def cnt(lo, hi):
        return (hi - lo) - sum(1 for v in dist if lo <= v < hi)
    return dict(A=cnt(0, C.NA), Bflags=cnt(C.OFF_B, C.OFF_S), solids=cnt(C.OFF_S, C.NTOT))


def main():
    S = C.setup()
    path = sys.argv[1] if len(sys.argv) > 1 else os.path.join(C.OUT, 'c8_best_moves.json')
    mv = [tuple(m) for m in json.load(open(path))['moves']]
    print('moves (orbit, dropped neighbour index, solid voltage):', mv)
    NB = C.apply_moves(S, mv)
    NB_rm = [[b for b in row if b < C.OFF_S] for row in NB]
    srcs = {'A-rep': S['cycA'][0][0], 'B-flag-rep': C.OFF_B + S['cycB'][0][0]}
    for label, G in (('with solids', NB), ('removal only', NB_rm)):
        adj = build_adj(G)
        for name, s in srcs.items():
            print(f'{label:13s} {name:12s} unreached within 5: {ball_defect(adj, s)}', flush=True)
        if label == 'with solids':
            ss = C.OFF_S + S['sol'][0]
            print(f'{label:13s} {"solid-rep":12s} unreached within 5: {ball_defect(adj, ss)}', flush=True)
    deg_s = [len(build_adj(NB)[C.OFF_S + s]) for s in range(1)]
    print('solid degree (base solid, with solids):', deg_s)


if __name__ == '__main__':
    main()
