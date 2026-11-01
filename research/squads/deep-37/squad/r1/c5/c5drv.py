#!/usr/bin/env python3
# c5drv.py (card c5, n=180): resumable driver for exact orbdfs sweeps over G-sets.
#   gen    GROUP            write G-sets for SmallGroup(GROUP) (GROUP = "20_1"), via src/gsets.g (GAP)
#   probe  GROUP BUDGET     Knuth tree-size estimates (PROBE=300) for every G-set, appended to gs/gGROUP/est.tsv
#   solve  GROUP BUDGET     exact orbdfs runs in increasing estimate order; sharded SHARD=i/m when est > TARGET;
#                           every run appended to runs.tsv (file, group, m, shard, status, nodes, sols, secs, est, desc)
#   status                  per-group summary
import sys, os, re, subprocess, time, math, glob
ROOT = '/home/user/degree-diameter/research/squads/deep-37'
C5 = os.path.join(ROOT, 'squad/r1/c5')
RUNS = os.path.join(C5, 'runs.tsv')
TARGET = 2e6          # nodes per shard (~20 s at 1e5 nodes/s)
MAXM = 256
SHARD_TMO = 90        # seconds per shard run before TIMEOUT

def gdir(g): return os.path.join(C5, 'gs', 'g' + g)

def load_sets(g):
    txt = open(os.path.join(gdir(g), 'gsets.list')).read().replace('\\\n', '')
    out = []
    for line in txt.split('\n'):
        m = re.match(r'(squad/r1/c5/gs/\S+\.txt)\s+(.*)$', line)
        if m: out.append((m.group(1), m.group(2).strip()))
    return out

def load_est(g):
    p = os.path.join(gdir(g), 'est.tsv')
    res = {}
    if os.path.exists(p):
        for line in open(p):
            parts = line.rstrip('\n').split('\t', 2)
            if len(parts) == 3:
                res[parts[0]] = (parts[1], parts[2])
    return res

def cmd_gen(g):
    o, i = g.split('_')
    D = 'squad/r1/c5/gs/g' + g
    os.makedirs(os.path.join(ROOT, D), exist_ok=True)
    p = os.path.join(ROOT, D, 'gsets.list')
    if os.path.exists(p) and 'GENDONE' in open(p).read():
        print('gen: already complete', g); return
    # resumable: existing files are kept (the last one written may be partial, so it is removed first)
    fs = sorted(glob.glob(os.path.join(ROOT, D, 'g_k*.txt')), key=lambda x: int(re.findall(r'_(\d+)\.txt', x)[0]))
    if fs and 'GENDONE' not in open(p).read(): os.remove(fs[-1])
    gap = ('Read("squad/r1/c5/gsets_resume.g");; G:=SmallGroup(%s,%s);; Print("# ", StructureDescription(G), "\\n");;'
           ' dosets(G, 180, "%s", "g", 100000);; Print("GENDONE\\n");; QUIT;') % (o, i, D)
    with open(p, 'w') as fo:
        subprocess.run(['nice', '-n', '15', 'timeout', '104', 'gap', '-q'], input=gap, text=True,
                       stdout=fo, stderr=subprocess.STDOUT, cwd=ROOT, timeout=108)
    txt = open(p).read()
    txt2 = txt.replace('\\\n', '')
    open(p, 'w').write(txt2)
    print('gen', g, 'complete' if 'GENDONE' in txt2 else 'INCOMPLETE', 'sets=', len(load_sets(g)) if 'GENDONE' in txt2 else '?')

def orbdfs(f, env_extra, tmo):
    env = dict(os.environ); env.update(env_extra)
    try:
        r = subprocess.run(['nice', '-n', '15', os.path.join(ROOT, 'bin/orbdfs'), f, '7'], env=env,
                           capture_output=True, text=True, cwd=ROOT, timeout=tmo)
        return r.stdout, False
    except subprocess.TimeoutExpired:
        return '', True

def cmd_probe(g, budget):
    sets = load_sets(g)
    ep = os.path.join(gdir(g), 'est.tsv')
    seen = load_est(g)
    t0 = time.time(); n = 0
    with open(ep, 'a') as fo:
        for f, d in sets:
            if f in seen: continue
            if time.time() - t0 > budget: break
            out, to = orbdfs(f, {'PROBE': '300'}, 20)
            m = re.search(r'nodes_est=(\S+)', out)
            est = m.group(1) if m else ('EXCL' if 'EXCLUDED' in out else 'NA')
            fo.write('%s\t%s\t%s\n' % (f, est, d)); fo.flush(); n += 1
    rest = len(sets) - len(load_est(g))
    print('probe', g, 'new=%d' % n, 'total=%d' % len(sets), 'unprobed=%d' % rest)

def load_runs():
    rows = []
    if os.path.exists(RUNS):
        for line in open(RUNS):
            p = line.rstrip('\n').split('\t')
            if len(p) >= 9 and p[0] != 'file': rows.append(p)
    return rows

def level_state(mine, ev):
    """(m, done shard set, status of last row). Level m doubles by 8 after a full-length TIMEOUT."""
    if not mine:
        return max(1, min(MAXM, int(math.ceil(ev / TARGET)))), set(), None
    last = mine[-1]; m = int(last[2])
    if last[4] == 'TIMEOUT':
        m = min(MAXM, m * 8)
    done = {int(r[3].split('/')[0]) for r in mine if r[4] == 'DONE' and int(r[2]) == m}
    return m, done, last[4]

def cmd_solve(g, budget):
    ests = []
    for f, (e, d) in load_est(g).items():
        if e in ('NA', 'EXCL'): continue
        ests.append((float(e), f, d))
    ests.sort()
    rows = load_runs()
    t0 = time.time(); ran = 0; settled_now = 0
    for ev, f, d in ests:
        while True:
            mine = [r for r in rows if r[0] == f]
            if mine and mine[-1][4] == 'HOPELESS': break
            if mine and mine[-1][4] == 'TIMEOUT' and int(mine[-1][2]) >= MAXM:
                row = [f, g, mine[-1][2], '-', 'HOPELESS', '0', '0', '0', '%.3e' % ev, d]
                with open(RUNS, 'a') as fo: fo.write('\t'.join(row) + '\n')
                rows.append(row); break
            m, done_i, last = level_state(mine, ev)
            if len(done_i) == m:
                settled_now += 1; print('SETTLED', f, 'm=%d' % m, d[:60], flush=True); break
            i = min(set(range(m)) - done_i)
            rem = budget - (time.time() - t0)
            if rem < 15: print('solve', g, 'shard runs=%d' % ran, 'settled=%d' % settled_now, 'budget used'); return
            tmo = min(rem, SHARD_TMO)
            base = os.path.basename(f)[:-4]
            env = {'MAXSOL': '50', 'SOLPREFIX': os.path.join(C5, 'sols', 'g%s_%s_m%d_s%d' % (g, base, m, i)),
                   'SHARDDEPTH': '8'}
            if m > 1: env['SHARD'] = '%d/%d' % (i, m)
            t1 = time.time()
            out, to = orbdfs(f, env, tmo)
            secs = time.time() - t1
            mm = re.search(r'DONE nodes=(\d+) sols=(\d+)', out)
            if to and tmo < SHARD_TMO:
                print('solve', g, 'budget cut a shard run; not logged', flush=True); return
            if to or not mm:
                status, nodes, sols = ('TIMEOUT' if to else 'ERROR'), 0, 0
            else:
                status, nodes, sols = 'DONE', int(mm.group(1)), int(mm.group(2))
            row = [f, g, str(m), '%d/%d' % (i, m), status, str(nodes), str(sols), '%.1f' % secs, '%.3e' % ev, d]
            with open(RUNS, 'a') as fo: fo.write('\t'.join(row) + '\n')
            rows.append(row); ran += 1
            if status == 'DONE' and sols > 0: print('SOLUTIONS', sols, f, 'shard', i, m, flush=True)
            if status == 'ERROR': print('ERROR', f, out[-200:], flush=True); break
    print('solve', g, 'shard runs=%d' % ran, 'sets settled this call=%d' % settled_now, 'elapsed=%.0fs' % (time.time() - t0))

def cmd_status():
    rows = load_runs()
    for gd in sorted(glob.glob(os.path.join(C5, 'gs', 'g*'))):
        g = os.path.basename(gd)[1:]
        sets = load_sets(g) if os.path.exists(os.path.join(gd, 'gsets.list')) else []
        ests = load_est(g)
        byf = {}
        for r in rows:
            if r[1] == g: byf.setdefault(r[0], []).append(r)
        settled = 0; hopeless = 0; sols = 0; excl = sum(1 for e, _ in ests.values() if e == 'EXCL')
        for f, rs in byf.items():
            m, done, last = level_state(rs, 0)
            if last == 'HOPELESS': hopeless += 1
            elif len(done) == m: settled += 1
            sols += sum(int(r[6]) for r in rs if r[4] == 'DONE')
        print('g%s sets=%d probed=%d excluded_nonfaithful=%d settled=%d hopeless=%d sols=%d' % (
            g, len(sets), len(ests), excl, settled, hopeless, sols))

if __name__ == '__main__':
    c = sys.argv[1]
    if c == 'gen': cmd_gen(sys.argv[2])
    elif c == 'probe': cmd_probe(sys.argv[2], float(sys.argv[3]))
    elif c == 'solve': cmd_solve(sys.argv[2], float(sys.argv[3]))
    elif c == 'status': cmd_status()
