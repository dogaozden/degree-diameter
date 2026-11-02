#!/usr/bin/env python3
"""Time-boxed, resumable exact certifier (card r2c). Each call works for BUDGET seconds (default 80), then returns.
Per group: build the table (mkmeta.py for metacyclic keys; .tab/.aut already present for GAP keys), check every
automorphism generator exhaustively, then run hx LIMIT 0 over the x-orbit representatives in chunks.
A group is done when all reps ran ("MIN >0", exact) or when a cost-0 set is found (verified with apsp).
One scoreboard line per finished group (r2/scoreboard.jsonl, json.dumps)."""
import json, os, re, subprocess, sys, time
import numpy as np

HERE = '/home/user/degree-diameter/research/squads/deep-49/r2/c'
TOOLS = '/home/user/degree-diameter/research/squads/deep-49/tools'
SB = '/home/user/degree-diameter/research/squads/deep-49/r2/scoreboard.jsonl'
STATE = HERE + '/state.json'
BUDGET = float(os.environ.get('BUDGET', '80'))
CH = int(os.environ.get('CH', '12'))
T0 = time.time()


def left():
    return BUDGET - (time.time() - T0)


def load_state():
    try:
        return json.load(open(STATE))
    except Exception:
        return {}


def save_state(st):
    tmp = STATE + '.tmp'
    with open(tmp, 'w') as f:
        json.dump(st, f, indent=0)
    os.replace(tmp, STATE)


def run(cmd, timeout, out, err):
    fo = open(out, 'w'); fe = open(err, 'w')
    try:
        p = subprocess.run(cmd, cwd=HERE, stdin=subprocess.DEVNULL, stdout=fo, stderr=fe, timeout=max(1.0, timeout))
        return p.returncode, False
    except subprocess.TimeoutExpired:
        return -9, True
    finally:
        fo.close(); fe.close()


def check_auts(key):
    """Exhaustive check of every automorphism generator; keeps the passing ones (exact for any subgroup of Aut)."""
    with open(f"{HERE}/{key}.tab", 'rb') as f:
        N = int(np.fromfile(f, dtype=np.int32, count=1)[0])
        MT = np.fromfile(f, dtype=np.uint16, count=N * N).reshape(N, N).astype(np.int64)
    with open(f"{HERE}/{key}.aut") as f:
        na = int(f.readline())
        auts = [np.array(list(map(int, f.readline().split())), dtype=np.int64) for _ in range(na)]
    ident = np.arange(N)
    ok = [p for p in auts if p.shape[0] == N and np.array_equal(np.sort(p), ident)
          and np.array_equal(p[MT], MT[np.ix_(p, p)])]
    with open(f"{HERE}/{key}.aut", 'w') as f:
        f.write(f"{len(ok)}\n")
        for p in ok:
            f.write(" ".join(map(str, p.tolist())) + "\n")
    return N, na, len(ok)


def verify_hit(key, N, x, y, z):
    edges = f"{HERE}/{key}.edges"
    subprocess.run(['python3', TOOLS + '/haar_edges.py', f"{HERE}/{key}.tab", edges, '0', str(x), str(y), str(z)],
                   check=True, cwd=HERE, stdin=subprocess.DEVNULL, timeout=60)
    r9 = subprocess.run([TOOLS + '/apsp', edges, '4', '9'], stdin=subprocess.DEVNULL, capture_output=True,
                        text=True, timeout=60).stdout
    r8 = subprocess.run([TOOLS + '/apsp', edges, '4', '8'], stdin=subprocess.DEVNULL, capture_output=True,
                        text=True, timeout=60).stdout
    ok = 'RESULT VALID' in r9 and 'RESULT INVALID' in r8
    return ok, r9.strip().splitlines()[-1] + ' | ' + r8.strip().splitlines()[-1]


def sb_append(d):
    with open(SB, 'a') as f:
        f.write(json.dumps(d) + "\n")


def finish(key, g, e):
    N = g['N']
    if e.get('found'):
        score, valid = 0, bool(e.get('found_valid'))
        nxt = 'cost-0 set found: ' + str(e['found']) + '; apsp check: ' + e.get('apsp', '')
    else:
        score, valid = '>0', True
        nxt = 'none needed: exhaustive over x-orbits (hx LIMIT 0); no Haar set of cost 0 for this group'
    sb_append({
        "card": "r2c",
        "idea": f"{g['label']}; group order {N}; exact hx LIMIT 0 (cost-0 Haar set exists?)",
        "code": HERE + "/driver.py",
        "command": g['command'] + f" (x-orbits {e.get('K')}, aut gens {e.get('naut_ok')}/{e.get('naut')} verified)",
        "n": 2 * N,
        "score": score,
        "exact": True,
        "valid": valid,
        "next": nxt,
    })


def process(key, g, st):
    e = st.get(key, {'status': 'new', 'next': 1, 'hits': 0})
    st[key] = e
    if e['status'] == 'new':
        if left() < 15:
            return
        if g['kind'] == 'meta':
            rc, to = run(['nice', '-n', '10', 'python3', TOOLS + '/mkmeta.py', str(g['m']), str(g['k']), str(g['r']), key],
                         timeout=left() - 3, out=f"{HERE}/{key}.mk.out", err=f"{HERE}/{key}.mk.err")
            if to:
                return
            if rc != 0:
                e['status'] = 'error'; e['why'] = f'mkmeta rc={rc}'; return
        N, na, nok = check_auts(key)
        assert N == g['N'], (key, N)
        e.update(status='run', naut=na, naut_ok=nok, K=None)
        save_state(st)
        if left() < 5:
            return
    if e['status'] != 'run':
        return
    while left() > 8 and e['status'] == 'run':
        lo = e['next']
        hi = lo + CH - 1
        t_chunk = time.time()
        rc, to = run(['nice', '-n', '10', HERE + '/hx', f"{key}.tab", f"{key}.aut", '0', '9', str(lo), str(hi),
                      f"{key}.hits"], timeout=min(left() - 2, 90), out=f"{HERE}/{key}.hx.out", err=f"{HERE}/{key}.hx.err")
        if to:
            CH_ = max(1, CH // 2)
            e['note'] = f'timeout at reps {lo}..{hi}, retry smaller'
            save_state(st)
            return
        if rc != 0:
            e['status'] = 'error'; e['why'] = f'hx rc={rc} reps {lo}..{hi}'; save_state(st); return
        for line in open(f"{HERE}/{key}.hx.err"):
            mm = re.search(r'x-orbits=(\d+)', line)
            if mm:
                e['K'] = int(mm.group(1))
        out = open(f"{HERE}/{key}.hx.out").read().splitlines()
        mline = [l for l in out if l.startswith('MIN')]
        if not mline:
            e['status'] = 'error'; e['why'] = 'no MIN line'; save_state(st); return
        e['next'] = hi + 1
        e['last_chunk_s'] = round(time.time() - t_chunk, 1)
        K = e.get('K') or 0
        if '>' not in mline[-1] and mline[-1].startswith('MIN 0'):
            hits = [l.split() for l in open(f"{HERE}/{key}.hits") if l.strip()] if os.path.exists(f"{HERE}/{key}.hits") else []
            zero = [h for h in hits if int(h[0]) == 0]
            e['hits'] = len(zero)
            e['status'] = 'done'
            x, y, z = map(int, zero[0][1:4])
            ok, txt = verify_hit(key, g['N'], x, y, z)
            e['found'] = [x, y, z]; e['found_valid'] = ok; e['apsp'] = txt
            finish(key, g, e)
        elif e['next'] > K:
            e['status'] = 'done'
            e['mintext'] = mline[-1]
            finish(key, g, e)
        save_state(st)
    save_state(st)


def main():
    groups = json.load(open(HERE + '/groups.json'))
    st = load_state()
    for g in groups:
        if left() < 10:
            break
        e = st.get(g['key'], {})
        if e.get('status') in ('done', 'error'):
            continue
        process(g['key'], g, st)
        save_state(st)
    done = [g['key'] for g in groups if st.get(g['key'], {}).get('status') == 'done']
    err = [g['key'] for g in groups if st.get(g['key'], {}).get('status') == 'error']
    found = [g['key'] for g in groups if st.get(g['key'], {}).get('found')]
    print(f"done {len(done)}/{len(groups)} error {err} found {found} elapsed {time.time() - T0:.1f}s")


if __name__ == '__main__':
    main()
