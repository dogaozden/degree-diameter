"""Exhaustive Haar search (hx, Aut-reduced plan, abelianization filter) for named groups given as GAP expressions.

Usage: python3 named.py DELTA D "GAP expression" [more expressions...] [--threads T] [--maxplan M] [--gap-timeout S]
GAP helpers available in the expressions:
  Aff(n, q, H)  : the affine group F_q^n x| H for a matrix group H <= GL(n,q) (e.g. Aff(3,2,GL(3,2)) = AGL(3,2))
  Meta(m, k, r)  : Z_m x|_r Z_k, as the group of left multiplications by (1,0) and (0,1) (isomorphic to Z_m x|_r Z_k)
Results: runs/named_d{DELTA}D{D}.tsv and runs/named_d{DELTA}D{D}_sols/.
"""
import argparse
import hashlib
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
SP = os.environ.get('SCRATCH', '/tmp/claude-0/-home-user-degree-diameter/2c3fb1ba-9359-5c52-a9c4-6d81a7db2df8/scratchpad')

PRELUDE = r'''
Meta := function(m, k, r)
  local N, px, py;
  N := m * k;;
  px := PermList(List([0..N-1], t -> ((QuoInt(t, k) + 1) mod m) * k + (t mod k) + 1));;
  py := PermList(List([0..N-1], t -> ((r * QuoInt(t, k)) mod m) * k + ((t mod k) + 1) mod k + 1));;
  return Group(px, py);
end;;
Aff := function(n, q, H)
  local gens, F, one, mats, t;
  F := GF(q);; one := One(F);;
  mats := List(GeneratorsOfGroup(H), A -> Concatenation(List([1..n], i -> Concatenation(A[i], [Zero(F)])), [Concatenation(List([1..n], i -> Zero(F)), [one])]));;
  t := IdentityMat(n + 1, F);; t[1][n + 1] := one;;
  return Group(Concatenation(mats, [t]));
end;;
'''


def export(expr, useaut, timeout):
    key = hashlib.md5((expr + str(os.getpid())).encode()).hexdigest()[:10]
    tab, plan, qmap = (os.path.join(SP, f'named_{x}_{key}.txt') for x in ('tab', 'plan', 'qmap'))
    script = PRELUDE + f'''
GRP0 := {expr};;
iso := IsomorphismPermGroup(GRP0);; GRP := Image(iso);;
el := AsSSortedList(GRP);; nn := Length(el);;
if IdGroupsAvailable(nn) then idg := IdGroup(GRP);; else idg := "?";; fi;
Print(nn, "|", idg, "|", StructureDescription(GRP), "\\n");
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
if {'true' if useaut else 'false'} then
  A := AutomorphismGroup(GRP);;
  for o in Orbits(A, el) do s1 := o[1];;
    if s1 <> One(GRP) then st := Stabilizer(A, s1);;
      for o2 in Orbits(st, el) do s2 := o2[1];;
        if s2 <> One(GRP) and s2 <> s1 then AppendTo(f, Position(el, s1) - 1, " ", Position(el, s2) - 1, "\\n");; fi;
      od; fi; od;
else
  cc := ConjugacyClasses(GRP);;
  for c in cc do s1 := Representative(c);;
    if s1 <> One(GRP) then cen := Centralizer(GRP, s1);;
      for o2 in OrbitsDomain(cen, el, OnPoints) do s2 := o2[1];;
        if s2 <> One(GRP) and s2 <> s1 then AppendTo(f, Position(el, s1) - 1, " ", Position(el, s2) - 1, "\\n");; fi;
      od; fi; od;
fi;
CloseStream(f);; QUIT;
'''
    r = subprocess.run(['gap', '-q', '-o', '8g'], input=script, capture_output=True, text=True, timeout=timeout)
    head = [l for l in r.stdout.splitlines() if '|' in l]
    if not head:
        raise RuntimeError(r.stdout[-2000:] + r.stderr[-2000:])
    return head[0], tab, plan, qmap


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('Delta', type=int)
    ap.add_argument('D', type=int)
    ap.add_argument('exprs', nargs='+')
    ap.add_argument('--threads', type=int, default=2)
    ap.add_argument('--maxplan', type=float, default=5e7)
    ap.add_argument('--gap-timeout', type=int, default=1800)
    ap.add_argument('--noaut', action='store_true', help='plan up to inner automorphisms only (conjugacy classes)')
    ap.add_argument('--outdir', default=None, help='write the tsv and solutions here instead of runs/')
    a = ap.parse_args()
    from math import comb
    base = a.outdir or os.path.join(HERE, 'runs')
    os.makedirs(base, exist_ok=True)
    outp = os.path.join(base, f'named_d{a.Delta}D{a.D}.tsv')
    soldir = os.path.join(base, f'named_d{a.Delta}D{a.D}_sols')
    os.makedirs(soldir, exist_ok=True)
    for expr in a.exprs:
        try:
            head, tab, plan, qmap = export(expr, not a.noaut, a.gap_timeout)
        except Exception as e:  # noqa: BLE001
            print(f'{expr}\tGAP failure {str(e)[:200]}', flush=True)
            continue
        n = int(head.split('|')[0])
        nplan = sum(1 for _ in open(plan))
        work = nplan * (comb(n - 3, a.Delta - 3) if a.Delta > 3 else 1)
        if work > a.maxplan:
            line = f'{expr}\t{head}\tplan={nplan}\ttoo-big:{work:.3g}'
        else:
            env = dict(os.environ, THREADS=str(a.threads), QMAP=qmap)
            r = subprocess.run([os.path.join(HERE, 'hx'), 'tab', tab, str(a.Delta), str(a.D), plan, '20'],
                               capture_output=True, text=True, env=env).stdout
            sols = [l for l in r.splitlines() if l.startswith('SOL')]
            dl = [l for l in r.splitlines() if l.startswith('DONE')][0]
            line = f'{expr}\t{head}\tplan={nplan}\t{dl}'
            if sols:
                name = hashlib.md5(expr.encode()).hexdigest()[:10]
                with open(os.path.join(soldir, f'named_{name}.txt'), 'w') as f:
                    f.write(f'# Haar graph Delta={a.Delta} D={a.D} G = {expr} (GAP; IsomorphismPermGroup image, elements = '
                            f'AsSSortedList indices, 0-based) = {head}; solutions in the Aut-reduced plan\n')
                    f.write('\n'.join(sols) + '\n')
                print(f'*** {expr}: {len(sols)}+ solutions', flush=True)
        print(line, flush=True)
        with open(outp, 'a') as f:
            f.write(line + '\n')
        for p_ in (tab, plan, qmap):
            if os.path.exists(p_):
                os.remove(p_)


if __name__ == '__main__':
    main()
