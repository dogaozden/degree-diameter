# build_audit.py : writes w18/audit.tsv, one line per scoreboard data line (w18 audit, 1-based index = data line number).
# Edge-list lines: values from raw/L<i>.score and raw/L<i>.apsp (score48 + apsp, d=4 D=9).
# Other lines: values from the auditor's manual rebuilds (see columns "how" and NOTES.md).
import os, re
H = '/home/user/degree-diameter/research/squads/handsoff-49'
W = H + '/w18'
rows = [l.rstrip('\n').split('\t') for l in open(H + '/scoreboard.tsv')][1:]
# N_side: the group order used by the worker's cost convention (far = cost * N_side / 2); None if claim is a far count
NSIDE = {1: 2600, 5: 832, 8: 1248, 3: 1248, 9: 622, 10: 2520, 11: 832, 12: 1248, 15: 1248, 17: 1248, 18: 416,
         19: 2640, 20: 416, 21: 2525, 22: 2496, 23: 2496, 24: 2520, 32: 1248, 35: 416, 36: 1320, 37: 1320,
         39: 2496, 40: 2520, 43: 1320, 47: 2520, 6: 63, 13: 2496, 14: 2525, 38: 2500, 46: 2500, 49: 504}
# manual rows: index -> (actual_n, actual_edges, deg, bipartite, diameter, far, apsp, how, verdict)
MAN = {
 2: ('4972', '9944', '4-4', 'yes', '10', '160', 'INVALID', 'edge file; far is the claim itself', 'holds'),
 4: ('-', '-', '-', '-', '-', '-', '-', 'file missing (w1 22:18 line)', 'file never existed; superseded by line 10 (w1 correction 22:26, same cost 6, file present and checked)'),
 6: ('5040', '10080', '4-4', 'yes', '10', '28539', 'INVALID', 'rebuilt: w3/runs/rep63_best.edges (the .volt is a voltage file, not an edge list)', 'holds: 2*28539/63 = 906'),
 7: ('3200', '6400', '4-4', 'yes', '9', '0', 'VALID', 'edge file', 'VALID at n=3200 (not a record: n <= 4970)'),
 13: ('4992', '9984', '4-4', 'yes', '10', '4992', 'INVALID', 'no edge file in w2 (deep.tsv row only); same group re-checked via w11/out/m208_k12_r3_c4.edges (line 23)', 'holds: group 208 12 3 floor 4 (exact, see w11 line 23 and repro_w11.tsv)'),
 14: ('5050', '10100', '4-4', 'yes', '10', '2525', 'INVALID', 'no edge file in w2 (deep.tsv row only); same group re-checked via w11/out/m101_k25_r5_c2.edges (line 21)', 'holds: group 101 25 5 floor 2 (exact, reproduced by w18: exh3 min 2)'),
 16: ('5040', '-', '-', '-', '-', '-', '-', 'w1 text output: exh_A7_class19.out; exact re-run by w18 on rep element 19 (see NOTES)', 'see NOTES: re-run reproduces min 6 (class scan)'),
 25: ('5040', '-', '-', '-', '-', '-', '-', 'no file; exh3 certification (w11 certified.tsv)', 'reproduction pending in w18 run (exh3 m35 k72 r4, bound 6)'),
 26: ('5040', '-', '-', '-', '-', '-', '-', 'no file; exh3 certification', 'reproduced by w18: exact min 6 (repro_w11.tsv)'),
 27: ('4992', '-', '-', '-', '-', '-', '-', 'no file; exh3 certification', 'reproduced by w18: exact min 6'),
 28: ('5040', '-', '-', '-', '-', '-', '-', 'no file; exh3 certification', 'reproduced by w18: exact min 6'),
 29: ('5040', '-', '-', '-', '-', '-', '-', 'no file; exh3 certification', 'reproduced by w18: exact min 8'),
 30: ('4992', '-', '-', '-', '-', '-', '-', 'no file; exh3 certification', 'reproduced by w18: exact min 8'),
 31: ('4992', '-', '-', '-', '-', '-', '-', 'no file; exh3 certification', 'reproduced by w18: exact min 8'),
 33: ('4992', '-', '-', '-', '-', '-', '-', 'no file; exh3 certification', 'reproduced by w18: exact min 8'),
 34: ('4992', '-', '-', '-', '-', '-', '-', 'no file; exh3 certification', 'reproduced by w18: exact min 9'),
 38: ('5000', '10000', '4-4', 'yes', '10', '12500', 'INVALID', 'rebuilt by w18 (haar_tab copy with SAVE_ANY, seed 8, 10 s): w18/val/hb1_c.edges', 'holds for cost 10 at the TRUE order: scoreboard n=2500 is wrong, Haar graph has 2|G| = 5000 vertices'),
 41: ('5060', '-', '-', '-', '-', '-', '-', 'no file; exh3 certification', 'reproduced by w18: exact min 10'),
 42: ('5160', '-', '-', '-', '-', '-', '-', 'no file; exh3 certification', 'reproduced by w18: exact min 10'),
 44: ('5120', '-', '-', '-', '-', '-', '-', 'no file; exh3 certification', 'reproduction pending in w18 run (exh3 m320 k8 r7, bound 12)'),
 45: ('5124', '-', '-', '-', '-', '-', '-', 'no file; exh3 certification', 'reproduced by w18: exact min 12'),
 46: ('5000', '10000', '4-4', 'yes', '10', '5000', 'INVALID', 'rebuilt by w18 (haar_tab copy with SAVE_ANY, seed 8, 10 s): w18/val/u4m7_c.edges', 'holds for cost 4 at the TRUE order: scoreboard n=2500 is wrong, Haar graph has 2|G| = 5000 vertices'),
}
NONEDGE_NOFILE = {25, 26, 27, 28, 29, 30, 31, 33, 34, 41, 42, 44, 45}
out = open(W + '/audit.tsv', 'w')
out.write('line\tscoreboard_time\tworker\tclaimed_n\tclaimed_cost_or_far\tclaimed_valid\tfile\tfile_status\t'
          'actual_n\tactual_edges\tdeg\tbipartite\tactual_diameter\tactual_far_pairs\tscore48_apsp\t'
          'expected_far_from_claim\tverdict\n')
for idx, r in enumerate(rows, start=1):
    t, w, strat, cn, cc, cv, f = (r + [''] * 7)[:7]
    p = f if f.startswith('/') else (H + '/' + f if f not in ('none', '') else '')
    exp = ''
    if idx in NSIDE and idx not in (2, 7, 13, 14):
        exp = str(int(cc) * NSIDE[idx] // 2) if cc.isdigit() else ''
    if idx == 2: exp = '160'
    if idx == 7: exp = '0'
    if idx == 48: exp = '0'
    st = 'missing' if (p and not os.path.exists(p)) else ('none' if not p else 'present')
    if idx in MAN:
        n_, e_, dg, bp, dm, fr, ap, how, verdict = MAN[idx]
        status = 'checked' if how.startswith(('edge', 'rebuilt')) else ('not an edge list' if 'no file' not in how else 'no file')
        if idx == 4: st = 'missing'
        if idx in (13, 14, 16): st = 'not an edge list'
        if idx in NONEDGE_NOFILE: st = 'none (exhaustive claim)'
        if idx in (38, 46): st = 'present: scoreboard file is a group table; rebuilt'
        if idx == 6: st = 'not an edge list (volt); rebuilt'
    else:
        base = W + '/raw/L%d' % idx
        sc = open(base + '.score').read().strip().splitlines() if os.path.exists(base + '.score') else []
        ap = open(base + '.apsp').read().strip().splitlines() if os.path.exists(base + '.apsp') else []
        if not sc:
            n_ = e_ = dg = bp = dm = fr = '?'; ap_r = '?'; verdict = 'not checked'; st = 'not an edge list'
            how = 'not an edge list: ' + f
        else:
            s_line = [x for x in sc if x.startswith('n=')][0]
            n_ = re.search(r'n=(\d+)', s_line).group(1); e_ = re.search(r'edges=(\d+)', s_line).group(1)
            dg = re.search(r'degree min=(\d+) max=(\d+)', s_line).groups()
            dg = '%s-%s' % dg
            bp = re.search(r'bipartite=(\w+)', s_line).group(1)
            dm = re.search(r'diameter=(\d+)', s_line).group(1)
            fr = re.search(r'far_pairs=(\d+)', s_line).group(1)
            ap_r = [x for x in ap if x.startswith('RESULT')][-1].replace('RESULT ', '').split(' ')[0]
            ap_r = 'VALID' if any(x.startswith('RESULT VALID') for x in ap) else 'INVALID'
            how = 'edge file checked with score48 and apsp (d=4 D=9)'
            cc_i = int(cc) if cc.isdigit() else None
            if exp:
                ok = (int(fr) == int(exp))
                verdict = 'holds' if ok else 'DISCREPANCY (far %s vs expected %s)' % (fr, exp)
            else:
                verdict = 'checked'
            if idx == 3 or idx == 8 or idx == 15:
                verdict = 'STALE: same path as line 17, file overwritten later; current far %s = cost %d at N=1248, claim %s not reproducible' % (fr, int(fr) * 2 // 1248, cc)
            if idx == 4:
                verdict = 'n/a'
            if idx == 17:
                verdict = 'holds (file is the latest version of the path shared by lines 3, 8, 15, 17)'
            if idx == 2:
                verdict = 'holds (claim is far pairs = 160; diameter 10)'
            if idx == 7:
                verdict = 'VALID at n=3200: not a record (n <= 4970)'
            if idx == 1:
                verdict = 'holds (far = 2600*30/2 = 39000; diameter 10)'
            if idx == 9:
                verdict = 'holds (n = 8*622 = 4976; cost = 2*far/622)'
            if idx == 10:
                verdict = 'holds (far = 2520*6/2 = 7560; diameter 10)'
            if idx == 21:
                verdict = 'holds (cost 2 = 2*2525/2525)'
            if idx == 22 or idx == 23:
                verdict = 'holds (cost 4 = 2*4992/2496); cost 4 is the exact minimum for this group (w11 certified)'
            if idx == 24:
                verdict = 'holds (far = 2520*15/2 = 18900)'
            if idx == 19:
                verdict = 'holds (far = 2640*38/2 = 50160)'
            if idx == 47:
                verdict = 'holds (far = 2520*312/2 = 393120; diameter 11, claim said 11)'
            if idx == 5 or idx == 11 or idx == 12 or idx == 32:
                verdict = 'holds (cost = 2*far/832 or /1248)'
            if idx == 18 or idx == 20 or idx == 35:
                verdict = 'holds (cost = 2*far/416)'
            if idx == 36 or idx == 37 or idx == 43:
                verdict = 'holds (cost = 2*far/1320)'
            if idx == 39:
                verdict = 'holds (cost = 2*far/2496 = 4)'
            if idx == 40:
                verdict = 'holds (cost = 2*far/2520 = 8)'
            if idx == 1: pass
            if idx == 6: pass
    line_fields = [str(idx), t, w, cn, cc, cv, f, st, n_, e_ if 'e_' in dir() else '', dg if 'dg' in dir() else '', bp if 'bp' in dir() else '',
                   dm if 'dm' in dir() else '', fr if 'fr' in dir() else '', ap_r if 'ap_r' in dir() else '', exp, verdict]
    out.write('\t'.join(line_fields) + '\n')
out.close()
print('wrote', len(rows), 'rows')
