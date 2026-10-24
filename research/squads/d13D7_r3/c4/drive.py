#!/usr/bin/env python3
"""c4 (squad round 3): crossover + LNS population search for pairwise-opposite sets of H(11).

usage: python3 -I drive.py CHILDREN LNS_CPU_SECONDS SEED
  Each child: (1) region crossover of two population members (region of parent P1 kept, compatible points of P2 added
  greedily, then greedy fill), (2) LNS (c6 code, copied as ./lns) for LNS_CPU_SECONDS of CPU, (3) oppcheck,
  (4) replace the worst population member if the child is at least as large (and not a duplicate).
  State: pop/state.json (members as files pop/m*.idx), kids/ (every child and its LNS output), kids/log.jsonl.
"""
import sys, os, json, random, subprocess, time
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import numpy as np
import xlib

HEX = xlib.HEX
OPP = '/home/user/degree-diameter/research/d13D7/tools/oppcheck'
LNS = os.path.join(HERE, 'lns')
POPDIR = os.path.join(HERE, 'pop'); KIDDIR = os.path.join(HERE, 'kids')
POPSIZE = 5

def oppcheck(path):
    out = subprocess.run(['timeout', '900', 'nice', '-n', '10', OPP, HEX, 'P', path],
                         capture_output=True, text=True).stdout
    for line in out.splitlines():
        if line.startswith('RESULT'):
            parts = line.split()
            return parts[1] == 'VALID', int(parts[-1])
    return False, -1

def greedy_from(pool, cur, rng):
    """add points of pool opposite to all of cur, greedily (min conflicts inside the remaining candidates)."""
    cur = list(cur)
    cs = set(cur)
    pool = [y for y in pool if y not in cs]
    if not pool:
        return cur
    ok = xlib.opposite_to_all(pool, cur)
    C = [y for y, o in zip(pool, ok) if o]
    while C:
        if len(C) > 1:
            Mc = (xlib.coord[C] @ xlib.wmat(C).T) % 11 == 0
            deg = Mc.sum(axis=1) - 1
            noise = np.array([rng.random() for _ in C]) * 0.5
            i = int(np.argmin(deg + noise))
        else:
            i = 0
        x = C[i]
        cur.append(x)
        keep = (xlib.coord[C] @ xlib.wmat([x])[0]) % 11 != 0
        C = [y for j, y in enumerate(C) if j != i and keep[j]]
    return cur

def region_child(P1, P2, rng):
    """keep a region of P1, add the points of P2 compatible with it, fill greedily from the whole hexagon."""
    if rng.random() < 0.6:
        # ball removal: keep the points of P1 opposite to a random point z of P2 (drops P1 n perp(z))
        z = rng.choice(P2)
        opp_z = ~xlib.conflicts_row(z)
        S = [x for x in P1 if opp_z[x]]
        kind = 'ball'
    else:
        # half-space of the coordinates: keep the points of P1 whose mu.x lies in a random set T of 6 residues
        mu = np.array([rng.randrange(11) for _ in range(7)], dtype=np.int64)
        T = set(rng.sample(range(11), 6))
        vals = (xlib.coord[np.asarray(P1)] @ mu) % 11
        S = [x for x, v in zip(P1, vals) if int(v) in T]
        kind = 'half'
    cur = greedy_from(P2, S, rng)
    n_ins = len(cur) - len(S)
    cur, added = xlib.fill(cur, rng)
    return cur, kind, len(S), n_ins, len(added)

def load_state():
    with open(os.path.join(POPDIR, 'state.json')) as f:
        return json.load(f)

def save_state(st):
    with open(os.path.join(POPDIR, 'state.json'), 'w') as f:
        json.dump(st, f, indent=1)

def main():
    children, secs, seed = int(sys.argv[1]), float(sys.argv[2]), int(sys.argv[3])
    rng = random.Random(seed)
    st = load_state()
    log = open(os.path.join(KIDDIR, 'log.jsonl'), 'a')
    for k in range(children):
        members = st['members']
        # parents: two distinct members, first one biased to the larger sets
        order = sorted(range(len(members)), key=lambda i: -members[i]['size'])
        i1 = order[0] if rng.random() < 0.4 else rng.choice(range(len(members)))
        i2 = rng.choice([i for i in range(len(members)) if i != i1])
        P1 = xlib.read_set(members[i1]['file']); P2 = xlib.read_set(members[i2]['file'])
        tag = 'kid%03d_s%d' % (st['counter'], seed)
        st['counter'] += 1
        t0 = time.time()
        child, kind, nS, nIns, nFill = region_child(P1, P2, rng)
        init = os.path.join(KIDDIR, tag + '_init.idx')
        xlib.write_set(init, child, 'region child init')
        out = os.path.join(KIDDIR, tag + '_lns.idx')
        lseed = rng.randrange(1, 10**6)
        with open(os.path.join(KIDDIR, tag + '_lns.log'), 'w') as lf:
            subprocess.run(['timeout', '900', 'nice', '-n', '10', LNS, HEX, init, out, str(secs), str(lseed),
                            '0', '40', '80', '8', '0.2', '100000'], stderr=lf, stdout=subprocess.DEVNULL)
        ok, m = oppcheck(out)
        rec = {'tag': tag, 'parents': [members[i1]['name'], members[i2]['name']], 'region': kind, 'kept': nS,
               'inserted': nIns, 'filled': nFill, 'init_size': len(child), 'lns_secs': secs,
               'valid': ok, 'size': m, 'wall': round(time.time() - t0, 1)}
        log.write(json.dumps(rec) + '\n'); log.flush()
        print(json.dumps(rec), flush=True)
        if not ok:
            continue
        # population update: replace the worst member if the child is at least as large and not a duplicate
        S_child = frozenset(xlib.read_set(out))
        dup = any(frozenset(xlib.read_set(mm['file'])) == S_child for mm in members)
        worst = min(range(len(members)), key=lambda i: members[i]['size'])
        if not dup and (len(members) < POPSIZE or m >= members[worst]['size']):
            fn = os.path.join(POPDIR, 'm%03d.idx' % st['counter'])
            xlib.write_set(fn, sorted(S_child), tag)
            newm = {'name': tag, 'file': fn, 'size': m}
            if len(members) < POPSIZE:
                members.append(newm)
            else:
                members[worst] = newm
        st['members'] = members
        st['best'] = max(st.get('best', {'size': 0}), {'size': m, 'file': out, 'name': tag}, key=lambda d: d['size'])
        save_state(st)
    log.close()
    print('population', [(mm['name'], mm['size']) for mm in st['members']], 'best', st['best']['size'], flush=True)

if __name__ == '__main__':
    main()
