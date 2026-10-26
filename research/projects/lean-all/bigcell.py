#!/usr/bin/env python3
"""Build one large Haar cell through a running poolq queue without keeping all its generated sources on disk
(run from lean/).

usage: bigcell.py CELL QUEUE LOG [--chunk K] [--keep J] [--need GB] [--est GB] [--clean]

CELL is a name from cells.txt. Steps: write Defs, Cover and Record (gen_haarsl.py --no-bats, which also runs
haarcert; the pool budget is lowered by --need GB meanwhile), then write the Bat modules K at a time
(--bat-modules), append them to QUEUE as direct-lean jobs, and delete the sources of built modules so that at most
J chunks of source exist at once. The sha256 of every generated file goes to manifests/CELL.sha256 before it is
deleted. When the Record is built, `#print axioms` of the theorem is appended to axioms_big.txt. With --clean the
certificate files and the Bat oleans are deleted at the end (the result then stays only as the axioms line and the
manifest)."""
import argparse, hashlib, os, re, shlex, subprocess, sys, time

HERE = os.path.dirname(os.path.abspath(__file__))
ENV = dict(os.environ)
ENV['PATH'] = os.path.expanduser('~/.elan/bin') + ':' + ENV['PATH']


def queue_append(qpath, lines):
    q = [l for l in open(qpath).read().split('\n') if l.strip()]
    assert q and q[-1] == 'END'
    q = q[:-1] + lines + ['END']
    tmp = qpath + '.tmp'
    open(tmp, 'w').write('\n'.join(q) + '\n')
    os.replace(tmp, qpath)


def log_status(log, start=0):
    """Modules logged ok / failed after the first `start` lines of the log."""
    ok, fail = set(), set()
    if os.path.exists(log):
        for i, l in enumerate(open(log)):
            if i < start:
                continue
            m = re.match(r'\d\d:\d\d:\d\d (\S+) (ok|FAIL)', l)
            if m:
                (ok if m.group(2) == 'ok' else fail).add(m.group(1).lstrip('!'))
    return ok, fail


def mem_avail_gb():
    for l in open('/proc/meminfo'):
        if l.startswith('MemAvailable:'):
            return int(l.split()[1]) / 1024 / 1024
    return 0.0


def sha(path):
    return hashlib.sha256(open(path, 'rb').read()).hexdigest()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('cell')
    ap.add_argument('queue')
    ap.add_argument('log')
    ap.add_argument('--chunk', type=int, default=150)
    ap.add_argument('--keep', type=int, default=2)
    ap.add_argument('--need', type=float, default=0.0)
    ap.add_argument('--clean', action='store_true')
    ap.add_argument('--truncate', action='store_true',
                    help='D even only: write the chunks from the last one down and cut the certificate file '
                         'below each chunk once its sources are written (disk); chunks whose oleans all exist '
                         'are skipped, so a stopped run can be restarted')
    ap.add_argument('--est', type=float, default=3.2, help='memory estimate (GB) of one Bat module')
    args = ap.parse_args()
    line = next(l for l in open(os.path.join(HERE, 'cells.txt')) if l.split() and l.split()[0] == args.cell)
    cmd = shlex.split(line.split(None, 1)[1].replace('[committed]', ''))
    outdir, module, theorem = cmd[3], cmd[4], cmd[5]
    P = module + '.'
    man = os.path.join(HERE, 'manifests', args.cell + '.sha256')
    os.makedirs(os.path.dirname(man), exist_ok=True)
    say = lambda s: print(f'{time.strftime("%H:%M:%S")} {args.cell}: {s}', flush=True)
    start = sum(1 for _ in open(args.log)) if os.path.exists(args.log) else 0   # earlier runs do not count

    # 1. Defs, Cover, Record (and the certificates); stale Bat sources from an earlier run are removed
    if os.path.isdir(outdir):
        for f in os.listdir(outdir):
            if f.startswith('Bat') and f.endswith('.lean'):
                os.remove(os.path.join(outdir, f))
    bfile = args.queue + '.budget'
    old_budget = open(bfile).read().strip() if os.path.exists(bfile) else None
    if args.need > 0:
        base = float(old_budget) if old_budget else 13.5
        open(bfile, 'w').write(f'{base - args.need}\n')
        while mem_avail_gb() < args.need + 1.0:
            time.sleep(10)
    say('writing Defs, Cover, Record')
    r = subprocess.run(cmd + ['--no-bats'], capture_output=True, text=True)
    if old_budget is not None:
        open(bfile, 'w').write(old_budget + '\n')
    elif args.need > 0:
        os.remove(bfile)
    if r.returncode != 0:
        sys.exit(r.stderr)
    m = re.search(r'in (\d+) modules', r.stderr)
    nmods = int(m.group(1))
    covers = sorted(f[:-5] for f in os.listdir(outdir) if f.startswith('Cover') and f.endswith('.lean'))
    # a restarted --truncate run keeps the lines of the Bat files written before
    keep = [l for l in open(man) if '/Bat' in l] if args.truncate and os.path.exists(man) else []
    with open(man, 'w') as mf:
        for f in ['Defs.lean'] + [c + '.lean' for c in covers] + ['Record.lean']:
            mf.write(f'{sha(os.path.join(outdir, f))}  {outdir}/{f}\n')
        mf.writelines(keep)
    queue_append(args.queue, [f'!{P}Defs:2.5', '--'])
    say(f'{nmods} Bat modules')

    # 2. Bat modules in chunks
    pending = []   # (module name, path) generated, not yet deleted
    starts = list(range(0, nmods, args.chunk))
    lib = os.path.join('.lake/build/lib/lean', *module.split('.'))
    certf = None
    if args.truncate:
        starts.reverse()
        base = os.path.basename(cmd[2]).replace('.txt', '')
        certf = f'/tmp/claude-0/work/certs/{base}_even.bin'
        assert os.path.exists(certf), certf
    k = 0
    while k < len(starts) or pending:
        ok, fail = log_status(args.log, start)
        bad = [mn for mn, _ in pending if mn in fail]
        if bad:
            sys.exit(f'failed: {bad[:5]}')
        for mn, path in list(pending):
            if mn in ok:
                os.remove(path)
                pending.remove((mn, path))
        if k < len(starts) and len(pending) < args.keep * args.chunk:
            s = starts[k]
            e = min(nmods, s + args.chunk)
            k += 1
            if args.truncate and all(os.path.exists(os.path.join(lib, f'BatE{mi:03d}.olean')) for mi in range(s, e)):
                say(f'Bat modules {s}:{e} already built')
                continue
            r = subprocess.run(cmd + ['--bat-modules', f'{s}:{e}'], capture_output=True, text=True)
            if r.returncode != 0:
                sys.exit(r.stderr)
            if args.truncate:
                cut = int(re.search(r'certificate bytes from (\d+)', r.stderr).group(1))
                os.truncate(certf, cut)
            known = {p for _, p in pending}
            new = sorted(f for f in os.listdir(outdir) if f.startswith('Bat') and f.endswith('.lean')
                         and os.path.join(outdir, f) not in known)
            with open(man, 'a') as mf:
                for f in new:
                    mf.write(f'{sha(os.path.join(outdir, f))}  {outdir}/{f}\n')
            queue_append(args.queue, [f'!{P}{f[:-5]}:{args.est}' for f in new])
            pending += [(P + f[:-5], os.path.join(outdir, f)) for f in new]
            say(f'queued Bat modules {s}:{e} ({len(new)} files)')
        else:
            time.sleep(20)

    # 3. covers and record
    queue_append(args.queue, ['--'] + [f'!{P}{c}:3.5' for c in covers] + ['--', f'!{P}Record:3', '--'])
    while True:
        ok, fail = log_status(args.log, start)
        if P + 'Record' in ok:
            break
        if any(P + c in fail for c in covers) or P + 'Record' in fail:
            sys.exit('cover or record failed')
        time.sleep(20)
    say('record built')
    tf = f'/tmp/claude-0/work/ax/{args.cell}.lean'
    os.makedirs(os.path.dirname(tf), exist_ok=True)
    open(tf, 'w').write(f'import {P}Record\n#print axioms {theorem}\n#check @{theorem}\n')
    r = subprocess.run(['lake', 'env', 'lean', tf], capture_output=True, text=True, env=ENV)
    out = ' | '.join(l.strip() for l in (r.stdout + r.stderr).strip().split('\n'))
    say(out)
    with open(os.path.join(HERE, 'axioms_big.txt'), 'a') as f:
        f.write(f'{args.cell} ({time.strftime("%Y-%m-%d %H:%M")}): {out}\n')
    if args.clean:
        for f in os.listdir(lib):
            if f.startswith('Bat'):
                os.remove(os.path.join(lib, f))
        base = os.path.basename(cmd[2]).replace('.txt', '')
        for kd in ('left', 'right', 'even'):
            p = f'/tmp/claude-0/work/certs/{base}_{kd}.bin'
            if os.path.exists(p):
                os.remove(p)
        say('cleaned')


if __name__ == '__main__':
    main()
