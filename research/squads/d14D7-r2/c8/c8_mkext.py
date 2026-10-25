"""c8: write an uhcheck EXTRAS file with super-hubs. Usage: python3 c8_mkext.py NU HUBX OUT SUPER...  where each SUPER is
a comma list of hub indices (0..2NU-1) it joins; a super-hub's side is the opposite of its hubs' side (line-side hub = even)."""
import sys
NU, HUBX, OUT = int(sys.argv[1]), sys.argv[2], sys.argv[3]
sups = [[int(x) for x in s.split(',')] for s in sys.argv[4:]]
hx = open(HUBX).read().split()
base_edges = [(hx[1 + 2 * k], hx[2 + 2 * k]) for k in range((len(hx) - 1) // 2)]
deg = {}
for a, b in base_edges:
    deg[int(a)] = deg.get(int(a), 0) + 1; deg[int(b)] = deg.get(int(b), 0) + 1
with open(OUT, 'w') as f:
    f.write('%d\n' % len(sups))
    for a, b in base_edges: f.write('%s %s\n' % (a, b))
    for s, hubs in enumerate(sups):
        for h in hubs:
            assert len(set(x % 2 for x in hubs)) == 1, 'super-hub must attach to one side only'
            f.write('%d %d\n' % (2 * NU + s, h))
            deg[h] = deg.get(h, 0) + 1
over = [h for h, d in deg.items() if d + 5 > 8]
print('super-hubs', len(sups), 'max hub degree (m=5 + links)', max(deg.values()) + 5, 'over Delta=8:', over, file=sys.stderr)
