# driver.py (own-small r2 card q1): body of the gated job. Exports GAP groups of the (4,8) orders, checks the
# degree-4 annealer against flift and score48, screens every exported group, refines the best, writes edges.
import os, re, time, random, struct, subprocess
from array import array

Q = '/home/user/degree-diameter/research/squads/own-small/r2/q1'
TOOLS = '/home/user/degree-diameter/research/squads/own-small/tools'
GTXT = '/home/user/degree-diameter/research/squads/own-small/runs/gtxt'
SAL = f'{Q}/salift4'
SCORE = f'{TOOLS}/bin/score48'
FLIFT = f'{TOOLS}/bin/flift'
GDIR, RUN, EDG, TST = f'{Q}/groups/', f'{Q}/runs', f'{Q}/edges', f'{Q}/test'
for d in (GDIR, RUN, EDG, TST):
    os.makedirs(d, exist_ok=True)
D = 8
ORDERS = list(range(183, 192)) + list(range(219, 231)) + list(range(274, 288)) + list(range(365, 384))
T_START = time.time()
LOGF = open(f'{Q}/driver.log', 'a')

def el():
    return time.time() - T_START

def log(*a):
    s = f'[{el():7.1f}] ' + ' '.join(str(x) for x in a)
    print(s, flush=True)
    LOGF.write(s + '\n'); LOGF.flush()

def p_of(N):
    return 6 if N <= 191 else 5 if N <= 230 else 4 if N <= 287 else 3

def export_groups(export_secs):
    man = GDIR + 'manifest.txt'
    if os.path.exists(man):
        os.remove(man)
    prog = (f'DIR := "{GDIR}";;\n'
            f'ORD := Filtered({ORDERS}, N -> NrSmallGroups(N) <= 60);;\n'
            'ORD := List(ORD, N -> [NrSmallGroups(N), N]);;\n'
            'Sort(ORD);;\n'
            'ORD := List(ORD, x -> x[2]);;\n'
            f'Read("{Q}/export4.g");;\n'
            'QUIT;\n')
    t = el()
    try:
        r = subprocess.run(['gap', '-q', '-o', '2g'], input=prog, capture_output=True, text=True, timeout=export_secs)
        log('gap rc', r.returncode, 'stderr tail:', r.stderr[-300:].replace('\n', ' | '))
    except subprocess.TimeoutExpired:
        log('gap export stopped by timeout', export_secs)
    for f in os.listdir(GDIR):
        if f.endswith('.tmp'):
            os.remove(GDIR + f)
    log('export wall', round(el() - t, 1))

def validate_entries():
    ents = []
    man = GDIR + 'manifest.txt'
    if not os.path.exists(man):
        return ents
    rnd = random.Random(99)
    for line in open(man):
        s = line.split()
        if len(s) < 3:
            continue
        N, gid = int(s[0]), int(s[1])
        fn = f'{GDIR}{N}_{gid}.txt'
        if not os.path.exists(fn):
            continue
        L = open(fn).read().split('\n')
        h = L[0].split()
        rows = [list(map(int, x.split())) for x in L[1:1 + N]]
        ok = h[:3] == ['G', str(N), str(gid)] and len(rows) == N and all(len(r) == N for r in rows)
        if ok:
            ok = rows[0] == list(range(N)) and all(rows[a][0] == a for a in range(N))
            ok = ok and all(sorted(r) == list(range(N)) for r in rows)
            for _ in range(400):
                if not ok:
                    break
                a, b, c = rnd.randrange(N), rnd.randrange(N), rnd.randrange(N)
                ok = rows[rows[a][b]][c] == rows[a][rows[b][c]]
        if not ok:
            log('REJECT invalid table', fn)
            continue
        ents.append(dict(N=N, id=gid, p=p_of(N), name=h[3], ab=not h[3].endswith('nab'),
                         text='\n'.join(L[:N + 1]) + '\n'))
    return ents

def write_order_files(ents):
    by = {}
    for e in ents:
        by.setdefault(e['N'], []).append(e)
    for N, es in by.items():
        with open(f'{GDIR}g{N}.txt', 'w') as f:
            for e in es:
                f.write(e['text'])
        for e in es:
            e['gfile'] = f'{GDIR}g{N}.txt'
            del e['text']

def read_gtxt_block(path, gid):
    L = open(path).read().split('\n')
    i = 0
    while i < len(L):
        h = L[i].split()
        if len(h) >= 3 and h[0] == 'G':
            N, g = int(h[1]), int(h[2])
            if g == gid:
                return N, [list(map(int, L[i + 1 + r].split())) for r in range(N)]
            i += 1 + N
        else:
            i += 1
    raise ValueError(f'group {gid} not in {path}')

def make_edges(N, p, rnd):
    E = []
    for _ in range(4):
        perm = list(range(p))
        rnd.shuffle(perm)
        for i in range(p):
            E.append((i, p + perm[i], rnd.randrange(N)))
    return E

def write_state(path, N, gid, p, E, cost=0):
    with open(path, 'w') as f:
        f.write(f'{N} {gid} {p} {cost}\n')
        for u, v, a in E:
            f.write(f'{u} {v} {a}\n')

def read_state(path):
    L = open(path).read().split('\n')
    N, gid, p = map(int, L[0].split()[:3])
    E = [tuple(map(int, x.split())) for x in L[1:] if x.strip()]
    return N, gid, p, E

def lift_edges(rows, N, p, E):
    S = set()
    for u, v, a in E:
        for g in range(N):
            x, y = u * N + g, v * N + rows[g][a]
            S.add((x, y) if x < y else (y, x))
    return sorted(S)

def write_edges(path, n, S):
    with open(path, 'w') as f:
        f.write(f'{n}\n')
        f.write(''.join(f'{x} {y}\n' for x, y in S))

def score(edgefile, d=4, DD=8):
    r = subprocess.run([SCORE, edgefile, str(d), str(DD)], capture_output=True, text=True)
    return r.stdout.strip().split('\n')[-1]

def far_of(line):
    m = re.search(r'far=(\d+)', line)
    return int(m.group(1)) if m else 0

def salift_start_cost(gfile, gid, p, state):
    env = dict(os.environ, D=str(D), START=state, CYC='30')
    r = subprocess.run([SAL, str(p), gfile, str(gid), '1', '0', '10', '0.3', f'{TST}/tmp.sol'],
                       env=env, capture_output=True, text=True, timeout=120)
    m = re.search(r'start (\d+)', r.stdout)
    return int(m.group(1)) if m else None

def flift_cost(gbin, rows, N, p, E):
    base = f'{TST}/base_{p}.txt'
    with open(base, 'w') as f:
        f.write(f'{2 * p} {4 * p}\n')
        for u, v, a in E:
            f.write(f'{u} {v}\n')
    inv = [rows[a].index(0) for a in range(N)]      # left-mult flift voltage = a^-1
    line = ' '.join(str(inv[a]) for _, _, a in E)
    r = subprocess.run([FLIFT, base, gbin, '4', str(D), 'eval'], input=line + '\n', capture_output=True, text=True,
                       timeout=120)
    return r.stdout.strip().split('\n')[-1]

def self_test():
    rnd = random.Random(2026)
    ok_all = True
    N, rows = read_gtxt_block(f'{GTXT}/g60.txt', 1)
    gbin = f'{TST}/g60_1.bin'
    with open(gbin, 'wb') as f:
        f.write(struct.pack('<i', N))
        array('H', [x for r in rows for x in r]).tofile(f)
    gtxt = f'{TST}/g60_1.txt'
    with open(gtxt, 'w') as f:
        f.write(f'G {N} 1 test\n' + ''.join(' '.join(map(str, r)) + '\n' for r in rows))
    for p in (3, 4):
        for trial in range(2):
            E = make_edges(N, p, rnd)
            st = f'{TST}/st_{p}_{trial}.in'
            write_state(st, N, 1, p, E)
            cs = salift_start_cost(gtxt, 1, p, st)
            cf = flift_cost(gbin, rows, N, p, E)
            S = lift_edges(rows, N, p, E)
            ef = f'{TST}/lift_{p}_{trial}.edges'
            write_edges(ef, 2 * p * N, S)
            line = score(ef)
            log('TEST N=60 p', p, 'salift4 cost', cs, 'flift cost', cf, 'edges', len(S), 'of', 4 * p * N,
                'score48:', line, 'far check: far =?= cost*N/2 ->', far_of(line), cs * N // 2 if cs is not None else None)
            if cs is None or cs >= (1 << 40):
                ok_all = ok_all and cf == 'invalid'
            else:
                ok_all = ok_all and str(cs) == cf and far_of(line) == cs * N // 2 and len(S) == 4 * p * N
    return ok_all

def run_sa(e, secs, seed, T0, T1, cyc, out, start=None):
    env = dict(os.environ, D=str(D), CYC=str(cyc))
    if start:
        env['START'] = start
    cmd = [SAL, str(e['p']), e['gfile'], str(e['id']), str(seed), str(secs), str(T0), str(T1), out]
    r = subprocess.run(cmd, env=env, capture_output=True, text=True, timeout=secs + 300)
    m = re.findall(r'end best (\d+)', r.stdout)
    st = os.path.exists(out + '.best')
    return dict(best=int(m[-1]) if m else None, found=('FOUND' in r.stdout),
                state=(out + '.best') if st else None, out=out)

def check_valid(state, e):
    N, gid, p, E = read_state(state)
    _, rows = read_gtxt_block(e['gfile'], gid)
    S = lift_edges(rows, N, p, E)
    n = 2 * p * N
    ef = f'{EDG}/{N}_{gid}_{os.path.basename(state)}.edges'
    write_edges(ef, n, S)
    line = score(ef)
    log('CHECK', N, gid, 'p', p, 'n', n, 'edges', len(S), line)
    return dict(valid=('RESULT VALID' in line), n=n, line=line, edges=ef, state=state, N=N, id=gid, p=p)

def main():
    log('driver start')
    export_groups(170)
    ents = validate_entries()
    write_order_files(ents)
    log('validated', len(ents), 'groups; non-abelian', sum(1 for e in ents if not e['ab']),
        'orders', sorted(set(e['N'] for e in ents)))
    try:
        ok = self_test()
    except Exception as ex:
        log('SELFTEST ERROR', repr(ex)); ok = False
    log('SELFTEST', 'PASSED' if ok else 'FAILED')
    if not ok:
        return
    res, valid = [], []
    key = lambda e: (e['N'], e['id'])
    by = {key(e): e for e in ents}
    for e in ents:
        if el() > 560:
            log('screen stop (time)')
            break
        out = f'{RUN}/{e["N"]}_{e["id"]}_s1.sol'
        r = run_sa(e, 4.0, 1, 3.0, 0.3, 4.0, out)
        res.append(dict(stage='screen', N=e['N'], id=e['id'], p=e['p'], name=e['name'], best=r['best'],
                        found=r['found'], state=r['state'], t=round(el(), 1)))
        log('screen', e['N'], e['id'], e['name'], 'p', e['p'], 'best', r['best'], 'found', r['found'])
        if r['found']:
            valid.append(check_valid(r['out'], e))
    cand = sorted([x for x in res if x['best'] is not None and x['state']], key=lambda x: x['best'])
    seen, top = set(), []
    for x in cand:
        k = (x['N'], x['id'])
        if k not in seen and len(top) < 4:
            seen.add(k); top.append(x)
    for j, x in enumerate(top):
        secs = min(25.0, 700 - el())
        if secs < 5:
            break
        e = by[(x['N'], x['id'])]
        out = f'{RUN}/{x["N"]}_{x["id"]}_r{j}.sol'
        r = run_sa(e, secs, 10 + j, 1.5, 0.2, 25.0, out, start=x['state'])
        res.append(dict(stage='refine', N=e['N'], id=e['id'], p=e['p'], name=e['name'], best=r['best'],
                        found=r['found'], state=r['state'], t=round(el(), 1)))
        log('refine', e['N'], e['id'], 'p', e['p'], 'best', r['best'], 'found', r['found'], 'from', x['best'])
        if r['found']:
            valid.append(check_valid(r['out'], e))
    cand = sorted([x for x in res if x['best'] is not None and x['state']], key=lambda x: x['best'])
    if cand and el() < 780:
        x = cand[0]
        e = by[(x['N'], x['id'])]
        j = 0
        while el() < 780 and not valid:
            secs = min(30.0, 790 - el())
            if secs < 5:
                break
            out = f'{RUN}/{x["N"]}_{x["id"]}_f{j}.sol'
            r = run_sa(e, secs, 30 + j, 1.5, 0.2, 30.0, out, start=x['state'])
            res.append(dict(stage='final', N=e['N'], id=e['id'], p=e['p'], name=e['name'], best=r['best'],
                            found=r['found'], state=r['state'], t=round(el(), 1)))
            log('final', e['N'], e['id'], 'best', r['best'], 'found', r['found'])
            if r['best'] is not None and r['state'] and r['best'] < x['best']:
                x = dict(x, best=r['best'], state=r['state'])
            if r['found']:
                valid.append(check_valid(r['out'], e))
            j += 1
    with open(f'{Q}/results.json', 'w') as f:
        import json
        json.dump(dict(results=res, valid=valid), f, indent=1)
    best = min([x for x in res if x['best'] is not None] or [dict(best=None)], key=lambda x: (x['best'] is None, x['best'] or 0))
    vv = [v for v in valid if 'RESULT VALID' in v['line']]
    log('SUMMARY screened', len(res), 'best cost', best.get('best'), 'at', best.get('N'), best.get('id'), 'p', best.get('p'),
        'valid', [(v['N'], v['id'], v['n']) for v in vv], 'max valid n', max([v['n'] for v in vv] or [None]))

if __name__ == '__main__':
    main()
