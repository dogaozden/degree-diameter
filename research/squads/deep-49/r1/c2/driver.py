#!/usr/bin/env python3
"""Resumable, time-boxed certifier for split metacyclic Haar graphs (card c2).

Each call works for at most BUDGET seconds (default 85) and then returns; state.json keeps the progress, so the
driver is called again and again until every candidate group is done.  Per group:
  1. mkmeta.py m k r prefix (table + automorphism generators);
  2. every automorphism generator is checked exhaustively (bijection and N^2 homomorphism test); failing ones are
     dropped (the reduction stays exact for any subgroup of Aut);
  3. hx LIMIT 0 over the x-orbit representatives, resumed from the last finished rep (progress read from stderr);
  4. "MIN >0" = no Haar set of cost 0; any HIT0 line is checked with haar_edges.py + apsp (4 9 valid, 4 8 invalid).
One scoreboard line per finished group.
"""
import json, os, re, subprocess, sys, time
import numpy as np

C2 = '/home/user/degree-diameter/research/squads/deep-49/r1/c2'
TOOLS = '/home/user/degree-diameter/research/squads/deep-49/tools'
SB = '/home/user/degree-diameter/research/squads/deep-49/r1/scoreboard.jsonl'
RUNS = C2 + '/runs'
STATE = C2 + '/state.json'
CAND = C2 + '/candidates.json'
BUDGET = float(os.environ.get('BUDGET', '85'))
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


def run(cmd, timeout, out=None, err=None):
    """Run cmd (list) in RUNS with a hard timeout. Returns (returncode, timed_out)."""
    fo = open(out, 'w') if out else subprocess.DEVNULL
    fe = open(err, 'w') if err else subprocess.DEVNULL
    try:
        p = subprocess.run(cmd, cwd=RUNS, stdin=subprocess.DEVNULL, stdout=fo, stderr=fe, timeout=max(1.0, timeout))
        return p.returncode, False
    except subprocess.TimeoutExpired:
        return -9, True
    finally:
        if out:
            fo.close()
        if err:
            fe.close()


def read_tab(path):
    with open(path, 'rb') as f:
        N = int(np.fromfile(f, dtype=np.int32, count=1)[0])
        MT = np.fromfile(f, dtype=np.uint16, count=N * N).reshape(N, N).astype(np.int64)
    return N, MT


def check_auts(N, MT, path):
    """Return the automorphism generators (from file path) that pass an exhaustive check, and the number read."""
    with open(path) as f:
        na = int(f.readline())
        auts = [np.array(list(map(int, f.readline().split())), dtype=np.int64) for _ in range(na)]
    ident = np.arange(N)
    ok = []
    for p in auts:
        if p.shape[0] != N or not np.array_equal(np.sort(p), ident):
            continue
        if np.array_equal(p[MT], MT[np.ix_(p, p)]):
            ok.append(p)
    return ok, na


def write_auts(path, auts):
    with open(path, 'w') as f:
        f.write(f"{len(auts)}\n")
        for p in auts:
            f.write(" ".join(map(str, p.tolist())) + "\n")


def sb_append(d):
    with open(SB, 'a') as f:
        f.write(json.dumps(d) + "\n")


def verify_hit(key, N, x, y, z):
    """haar_edges + apsp 4 9 (must be valid) and 4 8 (must be invalid). Returns (ok, text)."""
    edges = f"{RUNS}/{key}.edges"
    subprocess.run(['python3', TOOLS + '/haar_edges.py', f"{RUNS}/{key}.tab", edges, '0', str(x), str(y), str(z)],
                   check=True, cwd=RUNS, stdin=subprocess.DEVNULL, timeout=60)
    r9 = subprocess.run([TOOLS + '/apsp', edges, '4', '9'], stdin=subprocess.DEVNULL, capture_output=True,
                        text=True, timeout=60).stdout
    r8 = subprocess.run([TOOLS + '/apsp', edges, '4', '8'], stdin=subprocess.DEVNULL, capture_output=True,
                        text=True, timeout=60).stdout
    ok = 'RESULT VALID' in r9 and 'RESULT INVALID' in r8
    return ok, r9.strip() + ' | ' + r8.strip()


MODE = os.environ.get('MODE', 'gap')


def gapbuild(key, m, k, r, N, timeout):
    """Build G = <a,b | a^m, b^k, b a b^-1 a^-r> in GAP (pc group), check |G| = N, export with the full Aut(G),
    and turn it into the hx table with build_tab.py. Returns (rc, timed_out)."""
    gfile = f"{RUNS}/{key}.g"
    with open(gfile, 'w') as f:
        f.write(f'm:={m}; k:={k}; r:={r};\n'
                'F := FreeGroup("a","b");\n'
                'G := F / [F.1^m, F.2^k, F.2*F.1*F.2^-1*F.1^-r];\n'
                'G := Image(IsomorphismPcGroup(G));\n'
                f'if Size(G) = {N} then\n'
                f'Read("{TOOLS}/export_group.g");\n'
                f'ExportGroup(G, "{RUNS}/{key}.exp");\n'
                'Print("GAPOK\\n");\nfi;\nQUIT;\n')
    rc, to = run(['nice', '-n', '10', 'gap', '-q', '--quitonbreak', gfile], timeout=timeout,
                 out=f"{RUNS}/{key}.gap.out", err=f"{RUNS}/{key}.gap.err")
    if rc != 0 or to or 'GAPOK' not in open(f"{RUNS}/{key}.gap.out").read():
        return (rc if rc else 1), to
    rc, to = run(['nice', '-n', '10', 'python3', TOOLS + '/build_tab.py', f"{RUNS}/{key}.exp", key],
                 timeout=timeout, out=f"{RUNS}/{key}.bt.out", err=f"{RUNS}/{key}.bt.err")
    return rc, to


def process(key, c, st):
    m, k, r, N, d, q = c['m'], c['k'], c['r'], c['N'], c['d'], c['q']
    e = st.get(key, {'status': 'new', 'next': 1})
    st[key] = e
    if e['status'] == 'new':
        if left() < 12:
            return
        if MODE == 'gap' and not e.get('gap_to'):
            rc, to = gapbuild(key, m, k, r, N, timeout=left() - 3)
            if to:
                e['gap_to'] = True; save_state(st)  # GAP too slow for this group: use mkmeta instead
                return
        else:
            rc, to = run(['nice', '-n', '10', 'python3', C2 + '/mkmeta.py', str(m), str(k), str(r), key],
                         timeout=left() - 3, out=f"{RUNS}/{key}.mk.out", err=f"{RUNS}/{key}.mk.err")
        if to:
            return  # budget ran out during the build: retry in a later call
        if rc != 0:
            e['status'] = 'error'; e['why'] = f'build rc={rc} timeout={to}'
            return
        e['build'] = 'gap' if (MODE == 'gap' and not e.get('gap_to')) else 'mkmeta'
        Nt, MT = read_tab(f"{RUNS}/{key}.tab")
        assert Nt == N
        ok, na = check_auts(N, MT, f"{RUNS}/{key}.aut")
        os.replace(f"{RUNS}/{key}.aut", f"{RUNS}/{key}.aut.orig")
        write_auts(f"{RUNS}/{key}.aut", ok)
        e.update(status='run', next=1, naut=na, naut_ok=len(ok), K=None, hits=0, stuck=0)
        save_state(st)
        if left() < 5:
            return
    if e['status'] == 'run':
        if left() < 4:
            return
        t_start = left()
        cmd = ['nice', '-n', '10', C2 + '/hx', f"{key}.tab", f"{key}.aut", '0', '9', str(e['next']), '999999',
               f"{key}.hits"]
        rc, to = run(cmd, timeout=left() - 2, out=f"{RUNS}/{key}.hx.out", err=f"{RUNS}/{key}.hx.err")
        last = None; K = e.get('K')
        with open(f"{RUNS}/{key}.hx.err") as f:
            for line in f:
                mm = re.search(r'x-orbits=(\d+)', line)
                if mm: K = int(mm.group(1))
                mm = re.match(r'rep (\d+)/(\d+) ', line)
                if mm: last = int(mm.group(1))
        e['K'] = K
        if last is not None:
            e['next'] = last + 1
            e['stuck'] = 0
        elif to and t_start > 80:
            e['stuck'] += 1
        if rc == 0:
            out = open(f"{RUNS}/{key}.hx.out").read()
            mline = [l for l in out.splitlines() if l.startswith('MIN')]
            if not mline:
                e['status'] = 'error'; e['why'] = 'no MIN line'
                save_state(st); return
            hitlines = []
            if os.path.exists(f"{RUNS}/{key}.hits"):
                hitlines = [l.split() for l in open(f"{RUNS}/{key}.hits") if l.strip()]
            zero = [h for h in hitlines if int(h[0]) == 0]
            e['hits'] = len(zero)
            e['mintext'] = mline[-1]
            e['status'] = 'done'
            if zero:
                _, x, y, z = map(int, zero[0][1:4])
                ok, txt = verify_hit(key, N, x, y, z)
                e['apsp'] = txt
                e['found'] = [x, y, z]
                e['found_valid'] = ok
            finish(key, c, st)
        elif to and e['stuck'] >= 2:
            e['status'] = 'error'; e['why'] = 'a single hx rep exceeds the budget'
        elif not to:
            e['status'] = 'error'; e['why'] = f'hx rc={rc}'
    save_state(st)


def finish(key, c, st):
    e = st[key]
    N, m, k, r, d, q = c['N'], c['m'], c['k'], c['r'], c['d'], c['q']
    found = 'found' in e
    if found:
        score = 0
        valid = bool(e.get('found_valid'))
        nxt = 'verify the cost-0 graph in apsp and report to coordinator'
    else:
        score = '>0'
        valid = True
        nxt = 'none needed: exhaustive over x-orbits; no Haar set of cost 0 for this group'
    sb_append({
        "card": "c2",
        "idea": f"split metacyclic Z_{m} x|_{r} Z_{k}, group order {N}, d={d}, |G/G'|={q}; exact hx LIMIT 0",
        "code": C2 + "/driver.py",
        "command": (f"gap -q --quitonbreak {key}.g (presentation a^{m}, b^{k}, b a b^-1 a^-{r}; |G|={N} checked; "
                    f"ExportGroup with full Aut), build_tab.py {key}.exp {key}; nice -n 10 hx {key}.tab {key}.aut 0 9 1 999999 {key}.hits"
                    f" (x-orbits {e.get('K')}, aut gens {e.get('naut_ok')}/{e.get('naut')} verified)")
                   if e.get('build') == 'gap' else
                   f"python3 mkmeta.py {m} {k} {r} {key}; nice -n 10 hx {key}.tab {key}.aut 0 9 1 999999 {key}.hits "
                   f"(x-orbits {e.get('K')}, aut gens {e.get('naut_ok')}/{e.get('naut')} verified)",
        "n": 2 * N,
        "score": score,
        "exact": True,
        "valid": valid,
        "next": nxt,
    })


def main():
    cands = [c for c in json.load(open(CAND)) if c['keep']]
    st = load_state()
    for c in cands:
        key = f"g{c['N']}_{c['m']}_{c['k']}_{c['r']}"
        c['key'] = key
    for c in cands:
        if left() < 6:
            break
        e = st.get(c['key'], {})
        if e.get('status') in ('done', 'error'):
            continue
        process(c['key'], c, st)
        save_state(st)
    n_done = sum(1 for c in cands if st.get(c['key'], {}).get('status') == 'done')
    n_err = sum(1 for c in cands if st.get(c['key'], {}).get('status') == 'error')
    found = [c['key'] for c in cands if 'found' in st.get(c['key'], {})]
    print(f"done {n_done}/{len(cands)} error {n_err} found {found} elapsed {time.time() - T0:.1f}s")


if __name__ == '__main__':
    main()
