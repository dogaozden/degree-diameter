#!/usr/bin/env python3
"""Score a uniform family of Haar graphs: S given by a formula in q (and m).

The family is any command that, given q and m, prints the generators of S as lines "a b c d z" (matrix entries mod q,
z mod m; for sl/psl the determinant must be 1 mod q).  For each prime q in the list we run haar_ecc (two-source BFS,
Cor. 2.3 of HAAR_D8_10.md) and record the diameter of the component of (e,A).

Scores (lower excess is better):
  excess(q) = diam(q) - log_{Delta-1}(|G|)   with |G| = |Q| * m  (one side of the graph)
  mean_excess over the q list; best order per diameter D compared with the 2013 table and the lab's records.

Usage: family_score.py --gen "python3 mygen.py {q} {m}" --group psl --qs 29,31,37 [--m 1] [--json]
       family_score.py --gen ... --group psl --qrange 23 113 [--qmod 1,4]  (primes in range, optionally q = a mod b)
"""
import argparse, subprocess, math, json, os, re, sys
HERE = os.path.dirname(os.path.abspath(__file__))
TABLE = {(3,8):256,(4,8):2184,(5,8):9234,(6,8):29790,(7,8):80940,(8,8):201480,(9,8):449480,(10,8):1176480,(11,8):2246940,
 (12,8):4650100,(13,8):5314680,(14,8):14172480,(15,8):14172480,(16,8):36201060,
 (3,9):506,(4,9):4970,(5,9):27936,(6,9):117360,(7,9):400160,(8,9):1091232,(9,9):2961536,(10,9):7057400,(11,9):15200448,
 (12,9):30001152,(13,9):50990610,(14,9):95087738,(15,9):168016334,(16,9):288939118,
 (3,10):800,(4,10):11748,(5,10):90068,(6,10):452032,(7,10):1987380,(8,10):6927210,(9,10):20017260,(10,10):50331156,
 (11,10):130592354,(12,10):300383050,(13,10):617330936,(14,10):1213477190,(15,10):2300326510,(16,10):4119507330,
 (3,7):126,(4,7):840,(5,7):3110,(6,7):8310,(7,7):23436,(8,7):40586,(9,7):117648,(10,7):224694,(11,7):398580,(12,7):664300,
 (13,7):1062936,(14,7):1771560,(15,7):2480184,(16,7):4022340}
OURS = {(5,8):9760,(6,8):31680,(7,8):95760,(8,8):239904,(9,8):540360,(11,8):2258520,(13,8):6999552,(15,8):18128880,
 (5,9):29540,(6,9):127296,(7,9):462840,(8,9):1341600,(9,9):3499776,(10,9):8003856,(11,9):16792080,(12,9):34026720,
 (13,9):67742688,(14,9):116068656,(15,9):208029120,(16,9):337394400,(3,10):810,(4,10):12416,(5,10):95472,(6,10):524160,
 (7,10):2237760,(8,10):7818096,(9,10):23975280,(10,10):60141120,(11,10):148729680,(12,10):325832976,(13,10):677714400,
 (14,10):1326627120,(15,10):2467618800,(16,10):4220872800,(4,7):864,(5,7):3120,(6,7):8880,(7,7):23598,(8,7):43344,
 (9,7):118238,(10,7):225152,(11,7):413180,(12,7):693500,(13,7):1064472,(14,7):1789588,(15,7):2501491,(16,7):4052108}
def isprime(n): return n > 1 and all(n % d for d in range(2, int(n**.5) + 1))
def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--gen', required=True); ap.add_argument('--group', required=True, choices=['sl','psl','pgl'])
    ap.add_argument('--qs'); ap.add_argument('--qrange', nargs=2, type=int); ap.add_argument('--qmod')
    ap.add_argument('--m', type=int, default=1); ap.add_argument('--json', action='store_true')
    ap.add_argument('--timeout', type=int, default=600)
    a = ap.parse_args()
    if a.qs: qs = [int(x) for x in a.qs.split(',')]
    else:
        qs = [q for q in range(a.qrange[0], a.qrange[1] + 1) if isprime(q) and q > 2]
        if a.qmod:
            r, b = map(int, a.qmod.split(',')); qs = [q for q in qs if q % b == r]
    rows = []; best = {}
    for q in qs:
        gen = subprocess.run(a.gen.format(q=q, m=a.m), shell=True, capture_output=True, text=True, timeout=a.timeout)
        if gen.returncode != 0 or not gen.stdout.strip():
            rows.append({'q': q, 'error': 'generator failed: ' + gen.stderr[-200:]}); continue
        r = subprocess.run([os.path.join(HERE, 'haar_ecc'), a.group, str(q), str(a.m)], input=gen.stdout,
                           capture_output=True, text=True, timeout=a.timeout)
        m = re.search(r'Delta=(\d+) ecc_A=(\d+) ecc_B=(\d+) compA=(\d+) compB=(\d+) order=(\d+) connected=(\w+) diam=(\d+)', r.stdout)
        if not m:
            rows.append({'q': q, 'error': (r.stdout + r.stderr)[-200:]}); continue
        d, eA, eB, cA, cB, order, conn, diam = m.groups(); d, eA, eB, cA, cB, order = map(int, (d, eA, eB, cA, cB, order))
        n = cA  # vertices of the component of (e,A); equals the order when the graph is connected
        if cA != cB:
            rows.append({'q': q, 'error': f'components differ ({cA} vs {cB})'}); continue
        G = n // 2
        diam = max(eA, eB)
        ex = diam - math.log(G) / math.log(d - 1)
        rows.append({'q': q, 'Delta': d, 'vertices': n, 'diam': diam, 'excess': round(ex, 3), 'connected': conn})
        for D in range(diam, 13):
            if n > best.get(D, (0,))[0]: best[D] = (n, q)
    ok = [r for r in rows if 'excess' in r]
    mean = sum(r['excess'] for r in ok) / len(ok) if ok else None
    d = ok[0]['Delta'] if ok else None
    summary = {'mean_excess': round(mean, 3) if mean is not None else None, 'n_q': len(ok), 'Delta': d,
               'best': {D: {'vertices': v, 'q': q, 'table': TABLE.get((d, D)), 'ours': OURS.get((d, D)),
                            'vs_table': round(v / TABLE[(d, D)], 3) if (d, D) in TABLE else None}
                        for D, (v, q) in sorted(best.items()) if 7 <= D <= 12}}
    if a.json:
        print(json.dumps({'rows': rows, 'summary': summary}))
    else:
        for r in rows: print(r)
        print('SUMMARY', json.dumps(summary))
if __name__ == '__main__':
    main()
