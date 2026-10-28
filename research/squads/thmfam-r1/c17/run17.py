import sys, json, subprocess, time
sys.path.insert(0, '/home/user/degree-diameter/research/squads/thmfam-r1/c17')
from common17 import *
X = (-2, -1, 1, 0); Y = (0, -1, 1, 1)     # top m=1 pair from screen17 (entries in [-2,2])
out = open('/home/user/degree-diameter/research/squads/thmfam-r1/c17/results.jsonl', 'a')
GEN = '/home/user/degree-diameter/research/squads/thmfam-r1/c17/gen17.py'
RAND = '/home/user/degree-diameter/research/theorems/haar_families/gen_random_orb.py'
def gen(q, m, mode):
    return subprocess.run(['python3', GEN, str(q), str(m), '%d,%d,%d,%d' % X, '%d,%d,%d,%d' % Y, mode],
                          capture_output=True, text=True, timeout=60).stdout
for q in primes(23, 61):
    m_eq = mrule(q); m_any = mrule_any(q)
    rows = []
    t0 = time.time()
    # m = 1 same S, and E and N labelled versions with m = m(q)
    cases = [('m1_same_S', 1, 'Z'), ('E_m', m_eq, 'E'), ('N_m', m_any, 'N')]
    for name, m, mode in cases:
        lines = gen(q, m, mode).strip().split('\n')
        e = excess_of(q, m, lines)
        rows.append({'name': name, 'q': q, 'm': m, 'res': e})
    # random baseline, m = 1, 5 seeds (sl)
    rs = []
    for seed in range(1, 6):
        lines = subprocess.run(['python3', RAND, str(q), '0', '2', str(seed)], capture_output=True, text=True).stdout.strip().split('\n')
        e = excess_of(q, 1, lines)
        if e: rs.append(e['excess'])
    rows.append({'name': 'random_m1', 'q': q, 'm': 1, 'excess_list': rs})
    for r in rows:
        out.write(json.dumps(r) + '\n')
    out.flush()
    print(q, m_eq, m_any, [ (r['name'], round(r['res']['excess'],3) if r.get('res') else None) for r in rows[:3]],
          'rand', [round(x,2) for x in rs], round(time.time()-t0,1), flush=True)
