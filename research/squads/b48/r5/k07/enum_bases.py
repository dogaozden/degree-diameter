# Enumerate connected cubic bases with edges, loops (L) and semi-edges (S) on b = 2..6 vertices, up to isomorphism.
# Output: one base per line as JSON: {"b":..,"items":[["e",u,v],["l",u],["s",u]...]}
import itertools, json, sys

def structures(b):
    # per vertex: loop count L in {0,1}, semi count S; residual degree r = 3 - 2L - S >= 0 must be realised by non-loop edges
    out = []
    for L in itertools.product([0, 1], repeat=b):
        for S in itertools.product(range(4), repeat=b):
            res = [3 - 2 * L[u] - S[u] for u in range(b)]
            if min(res) < 0 or sum(res) % 2: continue
            pairs = [(u, v) for u in range(b) for v in range(u + 1, b)]
            # enumerate multiplicities x_p in 0..3 on pairs with degree sums == res
            def rec(i, res_left, mult):
                if i == len(pairs):
                    if all(x == 0 for x in res_left):
                        yield list(mult)
                    return
                u, v = pairs[i]
                for x in range(0, min(res_left[u], res_left[v], 3) + 1):
                    res_left[u] -= x; res_left[v] -= x; mult.append(x)
                    yield from rec(i + 1, res_left, mult)
                    mult.pop(); res_left[u] += x; res_left[v] += x
            for mult in rec(0, list(res), []):
                items = []
                for (u, v), x in zip(pairs, mult):
                    items += [("e", u, v)] * x
                for u in range(b):
                    if L[u]: items.append(("l", u, u))
                    items += [("s", u, u)] * S[u]
                out.append(items)
    return out

def connected(b, items):
    adj = {u: set() for u in range(b)}
    for t, u, v in items:
        if t == "e": adj[u].add(v); adj[v].add(u)
    seen = {0}; st = [0]
    while st:
        x = st.pop()
        for y in adj[x]:
            if y not in seen: seen.add(y); st.append(y)
    return len(seen) == b

def canon(b, items):
    best = None
    for p in itertools.permutations(range(b)):
        key = tuple(sorted((t, min(p[u], p[v]), max(p[u], p[v])) for t, u, v in items))
        if best is None or key < best: best = key
    return best

def parity_patterns(b, items):
    # chi(g_e) = 1 + c(u) + c(v) mod 2 for edges, 1 for loops and semi-edges; c(0) = 0 (complement gives same)
    pats = set()
    for cbits in itertools.product([0, 1], repeat=b - 1):
        c = (0,) + cbits
        pat = tuple(((1 + c[u] + c[v]) % 2) if t == "e" else 1 for t, u, v in items)
        pats.add(pat)
    return sorted(pats)

if __name__ == "__main__":
    bmax = int(sys.argv[1]) if len(sys.argv) > 1 else 6
    res = []
    for b in range(2, bmax + 1):
        seen = set(); cnt = 0
        for items in structures(b):
            if not connected(b, items): continue
            key = canon(b, items)
            if key in seen: continue
            seen.add(key)
            pats = parity_patterns(b, items)
            res.append({"b": b, "items": items, "patterns": pats})
            cnt += 1
        print("b", b, "bases", cnt, "patterns", sum(len(r["patterns"]) for r in res if r["b"] == b), file=sys.stderr)
    with open(sys.argv[2] if len(sys.argv) > 2 else "bases.jsonl", "w") as f:
        for r in res: f.write(json.dumps(r) + "\n")
