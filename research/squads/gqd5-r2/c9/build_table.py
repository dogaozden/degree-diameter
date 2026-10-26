"""Assemble cliques_d8.json (K -> sizes, seed) from the verified sweep logs."""
import json, glob, sys
delta = int(sys.argv[1])
table = {}
for fn in sys.argv[2:]:
    for line in open(fn):
        line = line.strip()
        if not line: continue
        r = json.loads(line)
        if r.get('valid') == 1 and r.get('seed') is not None:
            table[str(r['K'])] = {'sizes': r['sizes'], 'seed': r['seed']}
json.dump(dict(sorted(table.items(), key=lambda kv: int(kv[0]))), open(f'cliques_d{delta}.json', 'w'), indent=0)
print(len(table), 'entries; K range', min(map(int, table)), max(map(int, table)))
