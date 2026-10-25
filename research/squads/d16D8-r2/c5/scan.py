# c5 driver: for each level skeleton (L, t1, t2) scan k (gcd(L,k)=1) upward; generate, anneal with FIXMOD=L, full check.
# Usage: python3 scan.py q SECS_K1 SECS_K LOGFILE "L,t1,t2;L,t1,t2;..." [kmax_m]
import sys, os, subprocess, json, math
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import skel
B = '/home/user/degree-diameter/research/d16D8/baselift'

def run(args, env_extra, timeout=900):
    env = dict(os.environ, THREADS='1'); env.update(env_extra)
    return subprocess.run(args, env=env, capture_output=True, text=True, timeout=timeout)

def check(base):
    r = run([B, 'eval', base, '6'], {})
    line = r.stdout.strip()
    u = int(line.split('uncovered=')[1].split()[0])
    return u, ('VALID(all sources)' in line), line

def scan_one(q, L, t1, t2, secs1, secs, mmax, log, seed=1):
    dd = os.path.join(HERE, 'designs'); os.makedirs(dd, exist_ok=True)
    best = None
    for k in range(1, 100):
        if math.gcd(L, k) != 1: continue
        if L * k > mmax: break
        tag = 'q%d_L%d_%d_%d_k%d' % (q, L, t1, t2, k)
        base = os.path.join(dd, tag + '.base'); out = os.path.join(dd, tag + '_out.base')
        skel.make_design(q, L, t1, t2, k, seed * 1000 + k, base)
        if k == 1:
            # pure level: only matching swaps can change anything
            env = {'MOVES': 'M', 'FIXMOD': str(L)}; T = secs1
        else:
            env = {'MOVES': 'vvvM', 'FIXMOD': str(L)}; T = secs
        r = run([B, 'anneal', base, '6', str(T), str(seed + k), out], env)
        u0, _, _ = check(base)
        ok_out = os.path.exists(out)
        u, valid, line = check(out) if ok_out else (-1, False, 'no out')
        rec = dict(q=q, L=L, t1=t1, t2=t2, k=k, m=L * k, start=u0, uncovered=u, valid=valid, secs=T,
                   anneal=r.stdout.strip()[-120:])
        print(json.dumps(rec), flush=True)
        with open(log, 'a') as f: f.write(json.dumps(rec) + '\n')
        if valid:
            best = (k, L * k, out)
            continue
        break
    return best

if __name__ == '__main__':
    q = int(sys.argv[1]); s1 = float(sys.argv[2]); s = float(sys.argv[3]); log = sys.argv[4]
    cfgs = [tuple(map(int, c.split(','))) for c in sys.argv[5].split(';')]
    mmax = int(sys.argv[6]) if len(sys.argv) > 6 else 1000
    summary = []
    for (L, t1, t2) in cfgs:
        b = scan_one(q, L, t1, t2, s1, s, mmax, log)
        summary.append(dict(skel='(%d,%d,%d)' % (L, t1, t2), best_k=(b[0] if b else 0), best_m=(b[1] if b else 0),
                            design=(b[2] if b else '')))
        print('SUMMARY', json.dumps(summary[-1]), flush=True)
    with open(log, 'a') as f: f.write(json.dumps(dict(summary=summary, q=q)) + '\n')
