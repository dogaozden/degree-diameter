#!/usr/bin/env python3
"""Build Lean modules one at a time (lake build MOD), logging wall time and peak memory of each.

usage: seqbuild.py LOG MOD [MOD ...] [--keep-going]   (run from lean/)"""
import resource, subprocess, sys, time, os


def main():
    args = sys.argv[1:]
    keep = '--keep-going' in args
    args = [a for a in args if a != '--keep-going']
    log, mods = args[0], args[1:]
    env = dict(os.environ)
    env['PATH'] = os.path.expanduser('~/.elan/bin') + ':' + env['PATH']
    ok = True
    for m in mods:
        t0 = time.time()
        p = subprocess.Popen(['lake', 'build', m], stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, env=env)
        peak = 0
        out = []
        import threading
        def reader():
            for line in p.stdout:
                out.append(line)
        th = threading.Thread(target=reader)
        th.start()
        while p.poll() is None:
            # sum RSS of all lean processes (the module being built)
            tot = 0
            for pid in os.listdir('/proc'):
                if not pid.isdigit():
                    continue
                try:
                    with open(f'/proc/{pid}/comm') as f:
                        if f.read().strip() != 'lean':
                            continue
                    with open(f'/proc/{pid}/status') as f:
                        for line in f:
                            if line.startswith('VmRSS:'):
                                tot += int(line.split()[1])
                except OSError:
                    pass
            peak = max(peak, tot)
            time.sleep(1)
        th.join()
        dt = time.time() - t0
        status = 'ok' if p.returncode == 0 else f'FAIL({p.returncode})'
        with open(log, 'a') as f:
            f.write(f'{time.strftime("%H:%M:%S")} {m} {status} {dt:.0f}s peak={peak//1024}MB\n')
            if p.returncode != 0:
                f.write(''.join(out)[-4000:] + '\n')
        if p.returncode != 0:
            ok = False
            if not keep:
                break
    sys.exit(0 if ok else 1)


if __name__ == '__main__':
    main()
