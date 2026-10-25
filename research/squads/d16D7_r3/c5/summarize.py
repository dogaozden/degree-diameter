import sys, os, re, subprocess
R2 = '/home/user/degree-diameter/research/squads/d16D7_r2/'
def score(graph, sol):
    if not os.path.exists(sol):
        return None, 'missing'
    out = subprocess.run(['python3', R2 + 'ogscore.py', R2 + graph, sol], capture_output=True, text=True).stdout.strip()
    m = re.match(r'VALID orbits=(\d+)', out)
    return (int(m.group(1)) if m else None), out
for tag in sys.argv[1:]:
    side = tag.split('_')[1]
    graph = 'og_%s.txt' % side
    qlog = 'log_q_%s.txt' % tag
    qbest = None
    if os.path.exists(qlog):
        for l in open(qlog):
            m = re.search(r'END .*best_total=(\d+)', l)
            if m: qbest = int(m.group(1))
    exp_k, exp_msg = score(graph, 'exp_%s.txt' % tag)
    pol_k, pol_msg = score(graph, 'pol_%s.txt' % tag)
    print('%s quotient_best_total=%s expansion=%s polish=%s' % (tag, qbest, exp_k, pol_k if pol_k is not None else 'none'))
    print('   expansion:', exp_msg, '| polish:', pol_msg)
