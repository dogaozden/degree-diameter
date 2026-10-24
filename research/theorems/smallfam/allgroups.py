"""Exhaustive Haar-graph search over ALL groups of given orders (GAP SmallGroups), up to Aut(G).

For each order n in [NMIN, NMAX]:
  1. GAP lists every group with its abelian invariants and |G'| (gap -q).
  2. abfilt (rigorous abelianization filter) drops groups where no image S-bar in G/G' can work; groups whose
     abelianization needs more than DELTA-1 generators are dropped too (S = {e, s1, ...} must generate G).
  3. Survivors are exported by GAP (multiplication table, plan of (s1, s2) pairs: s1 over Aut(G)-orbit
     representatives, s2 over Stab(s1)-orbit representatives, and the abelianization map for hx's quotient filter).
  4. hx runs every remaining set S exhaustively.
Output: runs/allgroups_d{DELTA}D{D}.tsv, one line per group: n id structure abinv |G'| filter tested solutions best.

Usage: python3 allgroups.py DELTA D NMIN NMAX [--threads T] [--gap-timeout S] [--maxplan M]
"""
import argparse
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
SP = os.environ.get('SCRATCH', '/tmp/claude-0/-home-user-degree-diameter/2c3fb1ba-9359-5c52-a9c4-6d81a7db2df8/scratchpad')


def gap(script, timeout):
    r = subprocess.run(['gap', '-q', '-o', '6g'], input=script, capture_output=True, text=True, timeout=timeout)
    return r.stdout


def list_groups(n, timeout=3600):
    out = os.path.join(SP, f'list_{n}.txt')
    if not os.path.exists(out):
        gap(f'''f := OutputTextFile("{out}.tmp", false);; SetPrintFormattingStatus(f, false);;
for i in [1..NrSmallGroups({n})] do G := SmallGroup({n}, i);;
  AppendTo(f, i, " ", Size(DerivedSubgroup(G)), " ", JoinStringsWithSeparator(List(AbelianInvariants(G), String), ","), "\\n");; od;
CloseStream(f);; QUIT;\n''', timeout)
        os.rename(out + '.tmp', out)
    rows = []
    for line in open(out):
        f = line.split()
        i, dsize = f[0], f[1]
        ab = f[2] if len(f) > 2 else ''
        rows.append((int(i), int(dsize), [int(x) for x in ab.split(',')] if ab != '' else []))
    return rows


def abfilt(Delta, D, K, inv):
    if not inv:
        inv = [1]
    r = subprocess.run([os.path.join(HERE, 'abfilt'), str(Delta), str(D), str(K)] + [str(x) for x in inv],
                       capture_output=True, text=True)
    return r.stdout.strip()


def export(n, i, useaut, timeout, single=False):
    tab = os.path.join(SP, f'tab_{n}_{i}.txt')
    plan = os.path.join(SP, f'plan_{n}_{i}.txt')
    qmap = os.path.join(SP, f'qmap_{n}_{i}.txt')
    script = f'''GRP := SmallGroup({n}, {i});; el := AsSSortedList(GRP);; nn := Length(el);;
Print(StructureDescription(GRP), "\\n");
f := OutputTextFile("{tab}", false);; SetPrintFormattingStatus(f, false);;
AppendTo(f, nn, " ", Position(el, One(GRP)) - 1, "\\n");;
for x in el do AppendTo(f, JoinStringsWithSeparator(List(el, y -> String(Position(el, x * y) - 1)), " "), "\\n");; od;
CloseStream(f);;
hom := NaturalHomomorphismByNormalSubgroup(GRP, DerivedSubgroup(GRP));; Q := Image(hom);; qel := AsSSortedList(Q);;
f := OutputTextFile("{qmap}", false);; SetPrintFormattingStatus(f, false);;
AppendTo(f, Length(qel), "\\n");;
for x in qel do AppendTo(f, JoinStringsWithSeparator(List(qel, y -> String(Position(qel, x * y) - 1)), " "), "\\n");; od;
AppendTo(f, JoinStringsWithSeparator(List(el, g -> String(Position(qel, Image(hom, g)) - 1)), " "), "\\n");;
CloseStream(f);;
f := OutputTextFile("{plan}", false);; SetPrintFormattingStatus(f, false);;
if {'true' if single else 'false'} then
  if {'true' if useaut else 'false'} then A := AutomorphismGroup(GRP);; reps := List(Orbits(A, el), o -> o[1]);;
  else reps := el;; fi;
  for s1 in reps do if s1 <> One(GRP) then AppendTo(f, Position(el, s1) - 1, "\\n");; fi; od;
elif {'true' if useaut else 'false'} then
  A := AutomorphismGroup(GRP);;
  for o in Orbits(A, el) do s1 := o[1];;
    if s1 <> One(GRP) then st := Stabilizer(A, s1);;
      for o2 in Orbits(st, el) do s2 := o2[1];;
        if s2 <> One(GRP) and s2 <> s1 then AppendTo(f, Position(el, s1) - 1, " ", Position(el, s2) - 1, "\\n");; fi;
      od; fi; od;
else
  for a in [2..nn] do for b in [2..nn] do if a <> b then AppendTo(f, a - 1, " ", b - 1, "\\n");; fi; od; od;
fi;
CloseStream(f);; QUIT;
'''
    try:
        out = gap(script, timeout)
    except subprocess.TimeoutExpired:
        return None
    return out.strip().splitlines()[0] if out.strip() else '?', tab, plan, qmap


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('Delta', type=int)
    ap.add_argument('D', type=int)
    ap.add_argument('nmin', type=int)
    ap.add_argument('nmax', type=int)
    ap.add_argument('--threads', type=int, default=1)
    ap.add_argument('--gap-timeout', type=int, default=300)
    ap.add_argument('--maxplan', type=float, default=5e6)
    ap.add_argument('--tag', default='')
    ap.add_argument('--maxgroups', type=int, default=20000, help='skip orders with more groups than this')
    ap.add_argument('--base', default=None, help='lift mode: base file for lx (plan = Aut-orbit reps of the first free voltage)')
    ap.add_argument('--cycles', type=int, default=3, help='lift mode: number of independent cycles of the base (rank filter)')
    ap.add_argument('--abmax', type=int, default=0, help='lift mode: generic lattice bound on |G^ab| (liftbound.py); 0 = off')
    a = ap.parse_args()
    mode = 'haar' if a.base is None else 'lift_' + os.path.splitext(os.path.basename(a.base))[0]
    outp = os.path.join(HERE, 'runs', f'allgroups_d{a.Delta}D{a.D}{a.tag}.tsv' if a.base is None else f'{mode}_D{a.D}{a.tag}.tsv')
    done = set()
    if os.path.exists(outp):
        for line in open(outp):
            f = line.split('\t')
            if len(f) > 2 and f[0].isdigit():
                done.add((int(f[0]), int(f[1])))
    log = open(outp, 'a')
    soldir = os.path.join(HERE, 'runs', f'allgroups_d{a.Delta}D{a.D}_sols' if a.base is None else f'{mode}_D{a.D}_sols')
    os.makedirs(soldir, exist_ok=True)
    for n in range(a.nmin, a.nmax + 1):
        nr = int(gap(f'Print(NrSmallGroups({n}), "\\n"); QUIT;\n', 600).split()[0])
        if nr > a.maxgroups:
            log.write(f'{n}\t*\t-\t-\t-\tskipped-order({nr} groups)\t0\t0\t-\n'); log.flush()
            continue
        rows = list_groups(n)
        for (i, dsize, inv) in rows:
            if (n, i) in done:
                continue
            ninv = len([x for x in inv if x > 1])
            if a.base is not None:
                if ninv > a.cycles:
                    log.write(f'{n}\t{i}\t-\t{inv}\t{dsize}\trank>{a.cycles}\t0\t0\t-\n'); log.flush()
                    continue
                fr = 'lift'
                from math import prod
                if a.abmax and prod(inv) > a.abmax:
                    log.write(f'{n}\t{i}\t-\t{inv}\t{dsize}\tabfail(|G^ab|>{a.abmax})\t0\t0\t-\n'); log.flush()
                    continue
            elif ninv > a.Delta - 1:
                log.write(f'{n}\t{i}\t-\t{inv}\t{dsize}\trank>{a.Delta-1}\t0\t0\t-\n'); log.flush()
                continue
            if a.base is None:
                fr = abfilt(a.Delta, a.D, dsize, inv)
            if fr.startswith('pass 0 '):
                log.write(f'{n}\t{i}\t-\t{inv}\t{dsize}\tabfail\t0\t0\t-\n'); log.flush()
                continue
            ex = export(n, i, True, a.gap_timeout, single=a.base is not None)
            if ex is None:
                ex = export(n, i, False, a.gap_timeout, single=a.base is not None)
                if ex is None:
                    log.write(f'{n}\t{i}\t-\t{inv}\t{dsize}\tgap-timeout\t0\t0\t-\n'); log.flush()
                    continue
            struct, tab, plan, qmap = ex
            nplan = sum(1 for _ in open(plan))
            from math import comb
            work = nplan * (comb(n - 3, a.Delta - 3) if a.Delta > 3 else 1) if a.base is None else nplan * n * n
            if work > a.maxplan:
                log.write(f'{n}\t{i}\t{struct}\t{inv}\t{dsize}\ttoo-big:{work:.3g}\t0\t0\t-\n'); log.flush()
                for p in (tab, plan, qmap):
                    os.remove(p)
                continue
            env = dict(os.environ, THREADS=str(a.threads), QMAP=qmap)
            if a.base is None:
                r = subprocess.run([os.path.join(HERE, 'hx'), 'tab', tab, str(a.Delta), str(a.D), plan, '20'],
                                   capture_output=True, text=True, env=env).stdout
            else:
                r = subprocess.run([os.path.join(HERE, 'lx'), 'tab', tab, a.base, str(a.D), plan, '20'],
                                   capture_output=True, text=True, env=env).stdout
            sols = [l for l in r.splitlines() if l.startswith('SOL')]
            dl = [l for l in r.splitlines() if l.startswith('DONE')][0].split()
            tested, nsol, best = dl[2], dl[4], dl[6]
            log.write(f'{n}\t{i}\t{struct}\t{inv}\t{dsize}\t{fr}\t{tested}\t{nsol}\t{best}\n'); log.flush()
            if sols:
                with open(os.path.join(soldir, f'sg_{n}_{i}.txt'), 'w') as f:
                    f.write(f'# Haar graph Delta={a.Delta} D={a.D} G=SmallGroup({n},{i}) = {struct}; elements = '
                            f'AsSSortedList(G) indices (0-based); {nsol} solutions in the Aut-reduced plan\n')
                    f.write('\n'.join(sols) + '\n')
                print(f'*** {n} {i} {struct}: {nsol} solutions', flush=True)
            for p in (tab, plan, qmap):
                os.remove(p)


if __name__ == '__main__':
    main()
