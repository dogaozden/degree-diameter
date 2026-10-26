"""Enumerate cyclic subgroups of the spread-stabiliser group G (group.npy) and save generators with orders."""
import numpy as np, json, collections
G = np.load('/home/user/degree-diameter/research/squads/gqd5-r3/c2/group.npy').astype(np.int32)
n = G.shape[1]
ident = np.arange(n, dtype=np.int32)
keyof = {g.tobytes(): i for i, g in enumerate(G)}
def order_and_powers(g):
    pw = [ident]; cur = g
    while cur.tobytes() != ident.tobytes():
        pw.append(cur); cur = g[cur]
    return pw
seen = {}
orders = collections.Counter()
for i, g in enumerate(G):
    pw = order_and_powers(g)
    orders[len(pw)] += 1
    k = frozenset(p.tobytes() for p in pw)
    if k not in seen:
        seen[k] = (len(pw), i)
print('element order histogram', sorted(orders.items()))
cyc = sorted(seen.values(), key=lambda t: t[0])
print('cyclic subgroups by order', sorted(collections.Counter(o for o, _ in cyc).items()))
json.dump([{'order': o, 'gen': int(i)} for o, i in cyc], open('/home/user/degree-diameter/research/squads/gqd5-r3/c2/cyclic_subgroups.json', 'w'))
