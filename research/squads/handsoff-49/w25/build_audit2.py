# build_audit2.py [FROM_LINE] : w25 audit of scoreboard data lines (1-based data index, as w18 numbers them).
# For each line with index >= FROM_LINE (default 52 = lines added after w18's 01:57 audit):
#   - resolve the file; if it is an edge list (first token n, then pairs), run tools/score48 and tools/apsp (d=4 D=9)
#     and the independent bitset checker w25/indep_bits.py (no tools code); compare n, degree, bipartite, far pairs, diameter.
#   - otherwise mark 'not an edge list' or 'missing' or 'no file'.
# Writes w25/audit2.tsv (new lines only) and w25/indep_all.tsv when FROM_LINE = 1 (re-check of every line).
import os, re, subprocess, sys
H = '/home/user/degree-diameter/research/squads/handsoff-49'
W = H + '/w25'
FROM = int(sys.argv[1]) if len(sys.argv) > 1 else 52
OUT = W + ('/indep_all.tsv' if FROM == 1 else '/audit2.tsv')
rows = [l.rstrip('\n').split('\t') for l in open(H + '/scoreboard.tsv')][1:]

def run(cmd):
    return subprocess.run(cmd, capture_output=True, text=True, timeout=500).stdout

def is_edge_list(p):
    try:
        with open(p) as f:
            head = f.readline().split()
            if len(head) != 1 or not head[0].isdigit(): return False
            rest = f.read().split()
        return len(rest) % 2 == 0 and all(t.isdigit() for t in rest[:50])
    except Exception:
        return False

out = open(OUT, 'w')
out.write('line\ttime\tworker\tclaimed_n\tclaimed_cost_or_far\tclaimed_valid\tfile\tstatus\tn\tedges\tdeg\tbipartite\t'
          'diameter_score48\tfar_pairs_score48\tscore48_result\tapsp_result\tindep_diameter\tindep_far_unordered\tverdict\n')
for idx, r in enumerate(rows, start=1):
    if idx < FROM: continue
    t, w, strat, cn, cc, cv, f = (r + [''] * 7)[:7]
    p = f if f.startswith('/') else (H + '/' + f if f not in ('none', '') else '')
    base = [str(idx), t, w, cn, cc, cv, p or '-']
    if not p:
        out.write('\t'.join(base + ['no file'] + ['-'] * 10 + ['no file to check']) + '\n'); continue
    if not os.path.exists(p):
        out.write('\t'.join(base + ['missing'] + ['-'] * 10 + ['file not found']) + '\n'); continue
    if not is_edge_list(p):
        out.write('\t'.join(base + ['not an edge list'] + ['-'] * 10 + ['needs its own rebuild; not checked here']) + '\n'); continue
    s48 = run(['nice', '-n', '10', H + '/tools/score48', p, '4', '9'])
    ap = run(['nice', '-n', '10', H + '/tools/apsp', p, '4', '9'])
    ind = run(['nice', '-n', '10', 'python3', '-I', W + '/indep_bits.py', p, '9'])
    n = re.search(r'n=(\d+)', s48); edges = re.search(r'edges=(\d+)', s48)
    deg = re.search(r'degree min=(\d+) max=(\d+)', s48); bip = re.search(r'bipartite=(\w+)', s48)
    diam = re.search(r'diameter=(\d+)', s48); far = re.search(r'far_pairs=(\d+)', s48)
    s48r = re.search(r'RESULT (\w+)', s48)
    apr = re.search(r'RESULT (\w+)', ap)
    idiam = re.search(r'diameter=(\w+)', ind); ifar = re.search(r'far_D_unordered=(\d+)', ind)
    g = lambda m, i=1: m.group(i) if m else '-'
    degs = ('%s-%s' % (g(deg, 1), g(deg, 2))) if deg else '-'
    res = [g(n), g(edges), degs, g(bip), g(diam), g(far), (s48r.group(1) if s48r else '-'),
           (apr.group(1) if apr else '-'), g(idiam), g(ifar)]
    valid_real = bool(s48r and s48r.group(1) == 'VALID' and apr and apr.group(1) == 'VALID')
    claim_valid = cv.strip().upper() == 'VALID'
    n_ok = (res[0] == cn)
    ind_ok = bool(idiam and ifar and far and idiam.group(1) == g(diam) and ifar.group(1) == far.group(1))
    verdict = ('n %s claim' % ('matches' if n_ok else 'DIFFERS from')) + '; ' + \
              ('indep check agrees with score48' if ind_ok else 'indep check DIFFERS or missing') + '; ' + \
              ('VALID at d=4 D=9' if valid_real else 'not valid at d=4 D=9') + \
              ('; claim VALID but not valid' if (claim_valid and not valid_real) else '') + \
              ('; RECORD CANDIDATE (n > 4970)' if (valid_real and int(res[0]) > 4970) else '')
    out.write('\t'.join(base + ['checked'] + res + [verdict]) + '\n')
    open(W + '/raw/L%d.s48' % idx, 'w').write(s48)
    open(W + '/raw/L%d.apsp' % idx, 'w').write(ap)
    open(W + '/raw/L%d.indep' % idx, 'w').write(ind)
out.close()
print('wrote', OUT)
