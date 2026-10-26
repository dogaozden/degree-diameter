"""Add exact-order Haar reproductions found in round 2 to extra.json (table-audit-2).  Same rule as collect_extra.py:
an entry is added only if its .sol is in ../graphs/ and checks/haar_huge.txt has a line naming the .sol with
"RESULT VALID" from two independent checkers.  usage: add_extra.py d D SOLNAME [d D SOLNAME ...]"""
import json, os, re, sys
HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
log = open(os.path.join(HERE, 'checks/haar_huge.txt')).read().splitlines()
extra = json.load(open(os.path.join(HERE, 'extra.json')))
a = sys.argv[1:]
for i in range(0, len(a), 3):
    d, D, sol = int(a[i]), int(a[i + 1]), a[i + 2]
    lines = [l for l in log if l.startswith(sol + ':')]
    if not lines or lines[-1].count('VALID') < 2 or 'INVALID' in lines[-1] or not os.path.exists(os.path.join(HERE, 'graphs', sol)):
        print('not added (no two VALID checks or no .sol):', sol); continue
    m = re.search(r'meta_(\d+)_(\d+)_(\d+)_x1', sol)
    checkers = ' + '.join(c for c in ('build_haar2.py', 'meta_haar_check.c', 'meta_haar_bits.c') if c in lines[-1])
    e = extra.setdefault(f'{d},{D}', {})
    e.update(rebuilt='order', check=f'{checkers} VALID, two-BFS (checks/haar_huge.txt)',
             construction=f'Haar graph of meta {m.group(1)} {m.group(2)} {m.group(3)} found here (round 2; graphs/{sol}); '
                          'not necessarily the holder\'s graph',
             flag='holder\'s construction lost; order reproduced')
    print('added', d, D, sol)
json.dump(extra, open(os.path.join(HERE, 'extra.json'), 'w'), indent=1)
