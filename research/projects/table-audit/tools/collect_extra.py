"""Collect results found after audit_results.py was written (table-audit): exact-order Haar graphs (exact_haar.py
results.jsonl files whose .sol was copied to ../graphs/ and checked in ../checks/small.txt) and the group-order notes
for Loz cells.  Writes extra.json for audit_results.py.  Usage: collect_extra.py LOZ_NOTES.json RESULTS.jsonl ..."""
import json, os, sys
HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
small = open(os.path.join(HERE, 'checks/small.txt')).read()
extra = {}
for k, v in json.load(open(sys.argv[1])).items():
    extra.setdefault(k, {})['notes'] = v
for path in sys.argv[2:]:
    for line in open(path):
        r = json.loads(line)
        if not r['ok']:
            continue
        sol = os.path.basename(r['sol'])
        ok = any(sol in l and 'RESULT VALID' in l for l in small.splitlines())
        if not ok or not os.path.exists(os.path.join(HERE, 'graphs', sol)):
            print('not yet checked:', sol)
            continue
        key = f"{r['d']},{r['D']}"
        e = extra.setdefault(key, {})
        grp = r['spec'] + (f' x Z_{r["zn"]}' if r['zn'] > 1 else '')
        e.update(rebuilt='order', check='build_haar2.py + apsp.c VALID (checks/small.txt)',
                 construction=f'Haar graph of {grp} found here (graphs/{sol}); not necessarily the holder\'s graph',
                 flag='holder\'s construction lost; order reproduced')
json.dump(extra, open(os.path.join(HERE, 'extra.json'), 'w'), indent=1)
print('extra.json', len(extra))
