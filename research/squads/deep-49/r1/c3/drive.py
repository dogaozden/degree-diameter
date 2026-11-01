#!/usr/bin/env python3
# Resumable driver for card c3: exact minimum cost of Haar graphs H(Z_p x| Z_k, S), |S| = 4, diameter 9.
# Escalates LIMIT 0,1,2,4,6,8,10; each level is covered by x-representative chunks (CH reps each).
# One invocation stops launching work after BUDGET seconds; every hx call is capped so the shell call stays < 100 s.
import json, os, re, subprocess, sys, time
HERE = os.path.dirname(os.path.abspath(__file__))
G = os.path.join(HERE, 'g')
os.makedirs(G, exist_ok=True)
RES = os.path.join(HERE, 'res.jsonl')
FIN = os.path.join(HERE, 'final.jsonl')
SB = '/home/user/degree-diameter/research/squads/deep-49/r1/scoreboard.jsonl'
BUDGET = float(sys.argv[1]) if len(sys.argv) > 1 else 70.0
T0 = time.time()
LEVELS = [0, 1, 2, 4, 6, 8, 10]
CH = 2
APSP = '/home/user/degree-diameter/research/squads/deep-49/tools/apsp'
HAAR = '/home/user/degree-diameter/research/squads/deep-49/tools/haar_edges.py'

def load(path):
    out = []
    if os.path.exists(path):
        for line in open(path):
            line = line.strip()
            if line:
                out.append(json.loads(line))
    return out

groups = []
for line in open(os.path.join(HERE, 'groups.txt')):
    N, p, k, r = map(int, line.split())
    groups.append((N, p, k, r))
recs = load(RES)
fins = {(f['p'], f['k'], f['r']): f for f in load(FIN)}

def key(p, k, r):
    return f'{p}_{k}_{r}'

def elapsed():
    return time.time() - T0

def good(rc):
    return (not rc['timeout']) and rc['rc'] == 0 and rc['min'] != 'bad'

def pending_ranges(kk, L, k):
    covered = [False] * (k + 2)
    for rc in recs:
        if rc['g'] == kk and rc['L'] == L and good(rc):
            for i in range(rc['xf'], rc['xt'] + 1):
                covered[i] = True
    ranges = []; i = 1
    while i <= k:
        if covered[i]:
            i += 1; continue
        j = i
        while j <= k and not covered[j] and j - i < CH:
            j += 1
        ranges.append((i, j - 1)); i = j
    return ranges

def parse_min(text):
    m = re.search(r'^MIN (\d+) hits (\d+)', text, re.M)
    if m:
        return int(m.group(1)), int(m.group(2))
    m = re.search(r'^MIN >(\d+)', text, re.M)
    if m:
        return None, None
    return 'bad', None

def ensure_table(p, k, r):
    kk = key(p, k, r)
    tab = os.path.join(G, kk + '.tab')
    aut = os.path.join(G, kk + '.aut')
    if not (os.path.exists(tab) and os.path.exists(aut)):
        subprocess.run(['nice', '-n', '10', 'python3', os.path.join(HERE, 'mkmeta.py'), str(p), str(k), str(r),
                        os.path.join(G, kk)], check=True, timeout=60)
    return tab, aut

def run_chunk(N, p, k, r, L, xf, xt):
    kk = key(p, k, r)
    tab, aut = ensure_table(p, k, r)
    base = os.path.join(G, f'{kk}_L{L}_x{xf}-{xt}')
    out_file = base + '.hits'
    if os.path.exists(out_file):
        os.remove(out_file)
    cmd = ['nice', '-n', '10', os.path.join(HERE, 'hx'), tab, aut, str(L), '9', str(xf), str(xt), out_file]
    tl = max(5.0, 90.0 - elapsed())
    t1 = time.time()
    try:
        cp = subprocess.run(cmd, capture_output=True, text=True, timeout=tl)
        so, rc, timed = cp.stdout, cp.returncode, False
    except subprocess.TimeoutExpired as e:
        so = e.stdout.decode() if isinstance(e.stdout, bytes) else (e.stdout or '')
        rc, timed = -9, True
    secs = time.time() - t1
    open(base + '.stdout', 'w').write(so)
    mn, hits = parse_min(so) if not timed else ('bad', None)
    rec = {'g': kk, 'p': p, 'k': k, 'r': r, 'N': N, 'L': L, 'xf': xf, 'xt': xt, 'min': mn, 'hits': hits,
           'secs': round(secs, 2), 'rc': rc, 'timeout': timed, 'hits_file': out_file}
    with open(RES, 'a') as f:
        f.write(json.dumps(rec) + '\n')
    recs.append(rec)
    return rec

def finalize(N, p, k, r, mn, L):
    kk = key(p, k, r)
    cur = [rc for rc in recs if rc['g'] == kk and rc['L'] == L and good(rc)]
    sets = set()
    raw_hits = 0
    first = None
    for rc in cur:
        raw_hits += rc['hits'] or 0
        if os.path.exists(rc['hits_file']):
            for line in open(rc['hits_file']):
                parts = line.split()
                if len(parts) == 4 and int(parts[0]) == mn:
                    sets.add(tuple(sorted(map(int, parts[1:]))))
                    if mn == 0 and first is None:
                        first = tuple(map(int, parts[1:]))
    valid = False
    apsp_txt = ''
    if mn == 0 and first is not None:
        hits0 = os.path.join(G, kk + '_hit0.edges')
        tab = os.path.join(G, kk + '.tab')
        subprocess.run(['nice', '-n', '10', 'python3', HAAR, tab, hits0, '0', *map(str, first)],
                       check=True, timeout=60)
        ap = subprocess.run([APSP, hits0, '4', '9'], capture_output=True, text=True, timeout=60).stdout
        apsp_txt = ap.strip().splitlines()[-1] if ap.strip() else ''
        valid = 'RESULT VALID' in ap
    fin = {'p': p, 'k': k, 'r': r, 'N': N, 'min': mn, 'hits_at_min': len(sets), 'hx_hits_raw': raw_hits,
           'exact': True, 'valid': valid, 'apsp': apsp_txt, 'L_used': L}
    with open(FIN, 'a') as f:
        f.write(json.dumps(fin) + '\n')
    fins[(p, k, r)] = fin
    cmd_txt = f'python3 mkmeta.py {p} {k} {r} g/{kk}; ./hx g/{kk}.tab g/{kk}.aut LIMIT 9 (LIMIT escalation 0,1,2,4,6,8,10; x-chunks)'
    idea = f'Frobenius Z_{p} x| Z_{k} (r={r}, order {k}, N={N}): luck-curve point, exact min cost by hx'
    line = {'card': 'c3', 'idea': idea, 'code': 'research/squads/deep-49/r1/c3/drive.py', 'command': cmd_txt,
            'n': 2 * N, 'score': mn, 'exact': True, 'valid': valid,
            'next': f'hits at minimum: {len(sets)} distinct sets (hx raw {raw_hits})' + (f'; apsp: {apsp_txt}' if apsp_txt else '')}
    with open(SB, 'a') as f:
        f.write(json.dumps(line) + '\n')
    print('FINAL', json.dumps(fin), flush=True)

def finalize_gt(N, p, k, r):
    fin = {'p': p, 'k': k, 'r': r, 'N': N, 'min': '>10', 'hits_at_min': None, 'hx_hits_raw': None, 'exact': True,
           'valid': False, 'apsp': '', 'L_used': 10}
    with open(FIN, 'a') as f:
        f.write(json.dumps(fin) + '\n')
    fins[(p, k, r)] = fin
    line = {'card': 'c3', 'idea': f'Frobenius Z_{p} x| Z_{k} (r={r}, order {k}, N={N}): luck-curve point, exact min cost by hx',
            'code': 'research/squads/deep-49/r1/c3/drive.py',
            'command': f'python3 mkmeta.py {p} {k} {r} g/{key(p,k,r)}; ./hx LIMIT 10 over all x-reps',
            'n': 2 * N, 'score': '>10', 'exact': True, 'valid': False, 'next': 'min > 10 (exhaustive at LIMIT 10)'}
    with open(SB, 'a') as f:
        f.write(json.dumps(line) + '\n')
    print('FINAL', json.dumps(fin), flush=True)

def process_group(N, p, k, r):
    kk = key(p, k, r)
    for L in LEVELS:
        for xf, xt in pending_ranges(kk, L, k):
            if elapsed() > BUDGET:
                return 'budget'
            rec = run_chunk(N, p, k, r, L, xf, xt)
            if not good(rec):
                print('PROBLEM', json.dumps(rec), flush=True)
                return 'problem'
            print(f'{kk} L{L} x{xf}-{xt} MIN {rec["min"]} hits {rec["hits"]} t={rec["secs"]}s', flush=True)
        if pending_ranges(kk, L, k):
            return 'budget'
        mins = [rc['min'] for rc in recs if rc['g'] == kk and rc['L'] == L and good(rc) and rc['min'] is not None]
        if mins:
            finalize(N, p, k, r, min(mins), L)
            return 'done'
    finalize_gt(N, p, k, r)
    return 'done'

for (N, p, k, r) in groups:
    if (p, k, r) in fins:
        continue
    st = process_group(N, p, k, r)
    if st != 'done':
        print('STOP', st, 'at', key(p, k, r), 'elapsed', round(elapsed(), 1), flush=True)
        sys.exit(0)
print('ALL DONE elapsed', round(elapsed(), 1), flush=True)
