"""c6: identity-first pass for the lift search of allgroups.py.

allgroups.py plans the first free voltage over Aut(G)-orbit representatives and drops the identity
(export(): `if s1 <> One(GRP)`). This script runs lx on the same groups with the first free voltage fixed to the
identity, so that together with allgroups.py every voltage assignment up to Aut(G) is covered.

Usage (cwd = research/theorems/smallfam, env SCRATCH and OUTDIR set, THREADS=1):
  python3 /home/user/degree-diameter/research/squads/r2-smallfam/c6/identity_pass.py BASE D NMIN NMAX CYCLES OUTTSV
"""
import os
import subprocess
import sys

SM = '/home/user/degree-diameter/research/theorems/smallfam'
sys.path.insert(0, SM)
import allgroups as ag  # noqa: E402


def main():
    base, D = sys.argv[1], int(sys.argv[2])
    nmin, nmax, cycles = int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5])
    outp = sys.argv[6]
    solsdir = outp.replace('.tsv', '_sols')
    os.makedirs(solsdir, exist_ok=True)
    log = open(outp, 'a')
    for n in range(nmin, nmax + 1):
        for (i, dsize, inv) in ag.list_groups(n):
            ninv = len([x for x in inv if x > 1])
            if ninv > cycles:
                log.write(f'{n}\t{i}\t-\t{inv}\t{dsize}\trank>{cycles}\t0\t0\t-\n'); log.flush()
                continue
            ex = ag.export(n, i, True, 300, single=True)
            if ex is None:
                log.write(f'{n}\t{i}\t-\t{inv}\t{dsize}\tgap-timeout\t0\t0\t-\n'); log.flush()
                continue
            struct, tab, plan, qmap = ex
            with open(tab) as f:
                E = int(f.readline().split()[1])  # tab header: "nn E" (E = identity index)
            with open(plan, 'w') as f:
                f.write(f'{E}\n')
            env = dict(os.environ, THREADS='1', QMAP=qmap)
            r = subprocess.run([os.path.join(SM, 'lx'), 'tab', tab, base, str(D), plan, '20'],
                               capture_output=True, text=True, env=env, cwd=SM).stdout
            sols = [l for l in r.splitlines() if l.startswith('SOL')]
            dl = [l for l in r.splitlines() if l.startswith('DONE')][0].split()
            tested, nsol, best = dl[2], dl[4], dl[6]
            log.write(f'{n}\t{i}\t{struct}\t{inv}\t{dsize}\tidentity-first\t{tested}\t{nsol}\t{best}\n'); log.flush()
            if sols:
                with open(os.path.join(solsdir, f'sg_{n}_{i}.txt'), 'w') as f:
                    f.write('\n'.join(sols) + '\n')
                print('***', n, i, struct, nsol, flush=True)
            for p in (tab, plan, qmap):
                os.remove(p)
    log.close()


if __name__ == '__main__':
    main()
