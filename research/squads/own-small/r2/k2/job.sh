#!/bin/bash
# Card k2 (r2, own-small): joint base+voltage annealing, p=5 (n=10N), D=10, group orders N=82..86.
# Phase 1: screen every group (non-abelian first) with salift_s2, 20 CPU s, seed 1, N ascending;
#          a cost-0 state is converted (best2edges.py) and checked (score48), then the next N is screened.
# Phase 2: until the time box, restart the best (lowest cost) states of the lowest unsolved order with START and new seeds.
cd /home/user/degree-diameter/research/squads/own-small/r2/k2 || exit 1
python3 -I - <<'PYEOF'
import subprocess, os, time
T = '/home/user/degree-diameter/research/squads/own-small/tools'
GT = '/home/user/degree-diameter/research/squads/own-small/runs/gtxt'
W = '/home/user/degree-diameter/research/squads/own-small/r2/k2'
os.chdir(W)
for d in ('screen', 'push', 'valid'):
    os.makedirs(d, exist_ok=True)
ENV = dict(os.environ, D='10')
P = 5
T0 = time.time(); DEAD = T0 + 820
LOG = open(W + '/job.log', 'a')
def log(*a):
    LOG.write(time.strftime('%H:%M:%S ') + ' '.join(map(str, a)) + '\n'); LOG.flush()

groups = []
for line in open(W + '/groups.lst'):
    N, g, name, ab = line.split()
    groups.append((int(N), int(g), name, int(ab)))
groups.sort(key=lambda x: (x[0], x[3], x[1]))   # N ascending, non-abelian (ab=0) first

def state_cost(path):
    try:
        return int(open(path).readline().split()[3])
    except Exception:
        return None

def run(N, gid, secs, seed, out, start=None):
    e = dict(ENV)
    if start:
        e['START'] = start
    cmd = [T + '/bin/salift_s2', str(P), f'{GT}/g{N}.txt', str(gid), str(seed), str(secs), '10', '0.3', out]
    with open(out + '.log', 'w') as lf:
        try:
            subprocess.run(cmd, env=e, stdout=lf, stderr=subprocess.STDOUT, timeout=secs + 40)
        except subprocess.TimeoutExpired:
            log('  timeout', out)

def verify(N, gid, stfile):
    edges = f'{W}/valid/n{10 * N}_g{gid}.edges'
    subprocess.run(['python3', '-I', T + '/best2edges.py', f'{GT}/g{N}.txt', stfile, edges],
                   stdout=subprocess.DEVNULL, stderr=subprocess.STDOUT, check=True)
    r = subprocess.run([T + '/bin/score48', edges, '3', '10'], capture_output=True, text=True).stdout.strip().splitlines()
    r = r[-1] if r else 'NO OUTPUT'
    log('VERIFY N=%d gid=%d state=%s : %s' % (N, gid, stfile, r))
    return 'RESULT VALID' in r, r

valid_orders = {}      # N -> (gid, check line)
latest = {}            # (N, gid) -> (cost, path of latest best state)
fails = 0
# Phase 1: screen
for N, gid, name, ab in groups:
    if N in valid_orders:
        continue
    if time.time() > DEAD - 40:
        break
    out = f'{W}/screen/s{N}_{gid}.sol'
    log('SCREEN N=%d gid=%d %s ab=%d' % (N, gid, name, ab))
    run(N, gid, 20, 1, out)
    if os.path.exists(out):
        ok, r = verify(N, gid, out)
        if ok:
            valid_orders[N] = (gid, r)
            log('VALID order', N, 'n =', 10 * N, 'group', gid, name)
        else:
            log('cost-0 file did not verify', out)
            if os.path.exists(out + '.best'):
                latest[(N, gid)] = (0, out + '.best')
    elif os.path.exists(out + '.best'):
        latest[(N, gid)] = (state_cost(out + '.best'), out + '.best')
        log('  cost', latest[(N, gid)][0])
    else:
        log('  no state written')

# Phase 2: restarts on the best states of the lowest unsolved order
rnd = 0
while time.time() < DEAD - 40:
    pool = [(c, N, gid) for (N, gid), (c, p) in latest.items()
            if N not in valid_orders and c is not None and c > 0]
    if not pool:
        log('no open track left')
        break
    Nt = min(N for c, N, gid in pool)
    top = sorted(p for p in pool if p[1] == Nt)[:2]
    for c, N, gid in top:
        secs = min(120, int(DEAD - time.time()) - 10)
        if secs < 15:
            break
        rnd += 1
        _, path = latest[(N, gid)]
        out = f'{W}/push/r{rnd}_N{N}_g{gid}.sol'
        log('PUSH round %d N=%d gid=%d start cost %s secs %d' % (rnd, N, gid, c, secs))
        run(N, gid, secs, 100 + rnd, out, start=path)
        if os.path.exists(out):
            ok, r = verify(N, gid, out)
            if ok:
                valid_orders[N] = (gid, r)
                log('VALID order', N, 'n =', 10 * N, 'group', gid)
                break
            latest[(N, gid)] = (0, out + '.best')
        elif os.path.exists(out + '.best'):
            nc = state_cost(out + '.best')
            latest[(N, gid)] = (nc, out + '.best')
            log('  new cost', nc)
        else:
            fails += 1
            log('  no improvement / no state')
            if fails >= 4:
                break
    if fails >= 4:
        break

# Summary
best_N = max(valid_orders) if valid_orders else None
if best_N is not None:
    gid, r = valid_orders[best_N]
    log('LARGEST VALID n =', 10 * best_N, 'group', gid, r)
else:
    log('NO VALID ORDER FOUND in 82..86')
open(W + '/summary.txt', 'w').write('largest_valid_n %s\n' % (10 * best_N if best_N else 'none') +
    ''.join('valid N=%d n=%d gid=%d %s\n' % (N, 10 * N, g, r) for N, (g, r) in sorted(valid_orders.items())) +
    ''.join('track N=%d gid=%d cost=%s state=%s\n' % (N, g, c, p) for (N, g), (c, p) in sorted(latest.items())))
log('done after %.0f s' % (time.time() - T0))
PYEOF
