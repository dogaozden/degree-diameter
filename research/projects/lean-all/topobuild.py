#!/usr/bin/env python3
"""Build every module of a generated cell directory in import order with direct lean runs, J at a time (no lake
start-up per module). Run from lean/. usage: topobuild.py DIR [J]

Environment: SKIP_BUILT=1 skips modules whose .olean is newer than their source (resume after a restart);
ONLY=REGEX builds only the modules matching it (e.g. ONLY='P_' for the light data modules at a higher J, then the
rest with SKIP_BUILT=1 at J=1); LEAN_PATH (default: `lake env printenv LEAN_PATH`); LEAN (default: lean);
TB_OUT (default /tmp): the output of each lean run goes to TB_OUT/tb_<module>.out.
Each finished module prints `<module> rc=<code> <seconds>s`; rc=-9 is the OOM killer (run heavy modules with J=1)."""
import os, re, subprocess, sys, time
D = sys.argv[1].rstrip('/'); J = int(sys.argv[2]) if len(sys.argv) > 2 else 4
M = D.replace('/', '.')
B = f'.lake/build/lib/lean/{D}'; os.makedirs(B, exist_ok=True)
env = dict(os.environ)
if not env.get('LEAN_PATH'):
    env['LEAN_PATH'] = subprocess.run(['lake', 'env', 'printenv', 'LEAN_PATH'], capture_output=True, text=True,
                                      check=True).stdout.strip()
L = os.environ.get('LEAN', 'lean')
OUT = os.environ.get('TB_OUT', '/tmp')
mods = sorted(f[:-5] for f in os.listdir(D) if f.endswith('.lean'))
ONLY = os.environ.get('ONLY')
if ONLY:
    mods = [m for m in mods if re.match(ONLY, m)]
deps = {m: [i[len(M) + 1:] for i in re.findall(r'^import (\S+)', open(f'{D}/{m}.lean').read(), re.M)
            if i.startswith(M + '.') and i[len(M) + 1:] in mods] for m in mods}
done, running, failed = set(), {}, []
if os.environ.get('SKIP_BUILT'):
    for m in mods:
        o = f'{B}/{m}.olean'
        if os.path.exists(o) and os.path.getmtime(o) > os.path.getmtime(f'{D}/{m}.lean'):
            done.add(m)
    print(f'skipping {len(done)} built modules', flush=True)
while len(done) < len(mods) and not failed:
    for p, (m, t0) in list(running.items()):
        if p.poll() is not None:
            del running[p]
            print(f'{m} rc={p.returncode} {time.time() - t0:.1f}s', flush=True)
            (done.add(m) if p.returncode == 0 else failed.append(m))
    for m in mods:
        if len(running) >= J or failed:
            break
        if m in done or m in [v[0] for v in running.values()] or not all(d in done for d in deps[m]):
            continue
        out = open(f'{OUT}/tb_{m}.out', 'w')
        p = subprocess.Popen([L, f'{D}/{m}.lean', '-o', f'{B}/{m}.olean', '-i', f'{B}/{m}.ilean'], env=env,
                             stdout=out, stderr=subprocess.STDOUT)
        running[p] = (m, time.time())
    time.sleep(0.2)
for p in running:
    p.wait()
if failed:
    print('FAILED', failed, open(f'{OUT}/tb_{failed[0]}.out').read()[-2000:])
    sys.exit(1)
print('all built')
