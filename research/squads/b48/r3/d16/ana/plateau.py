import sys, importlib.util
sys.argv = ["x", "104", "24", "7"]
spec = importlib.util.spec_from_file_location("hz", "/home/user/degree-diameter/research/squads/b48/r3/d16/ana/hz.py")
hz = importlib.util.module_from_spec(spec); spec.loader.exec_module(hz)
N = hz.N
rows = [l.split() for l in open("/home/user/degree-diameter/research/squads/b48/r3/d16/ana/nb1.volt")]
out = open("/home/user/degree-diameter/research/squads/b48/r3/d16/ana/nb1.out").read().split()
zs = 52; zfar = 0; n4 = 0; kinds = {}
for line, c in zip(rows, out):
    if int(c) != 4: continue
    n4 += 1
    S = list(map(int, line))
    cc, f = hz.cost(S)
    key = tuple(sorted(hz.lab(x) for x in f["A"] + [x - N for x in f["B"]]))
    kinds[key] = kinds.get(key, 0) + 1
print("cost-4 neighbours", n4, "distinct far patterns", len(kinds))
for k, v in sorted(kinds.items(), key=lambda t: -t[1])[:8]: print(v, k)
