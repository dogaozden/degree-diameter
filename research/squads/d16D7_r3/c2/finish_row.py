#!/usr/bin/env python3
"""finish_row.py [--dry]: builds the ONE scoreboard JSON line for card c2 from ogscore.py on best_pts.txt / best_lines.txt
(orbit-graph indices). --dry prints the line only."""
import json, re, subprocess, sys
D = '/home/user/degree-diameter/research/squads/d16D7_r3/c2'
R2 = '/home/user/degree-diameter/research/squads/d16D7_r2'

def score(g):
    out = subprocess.run(['python3', R2 + '/ogscore.py', R2 + '/og_%s.txt' % g, '%s/best_%s.txt' % (D, g)],
                         capture_output=True, text=True).stdout.strip()
    m = re.match(r'VALID orbits=(\d+)', out)
    return (int(m.group(1)) if m else 0), bool(m), out

kp, vp, op = score('pts')
kl, vl, ol = score('lines')
row = {
    "card": "c2",
    "idea": "k-fixed tabu (ktq.c) on the weight-9 vertices of the order-9 quotients, unweighted, each conflict-free set filled exactly with weight-3/1 vertices, full restarts; quotient weights pts 240 / lines 243; expansion then 420 s ktabu polish on the orbit graph",
    "code": "research/squads/d16D7_r3/c2/ktq.c",
    "command": "./ktq quot/q9_pts.txt - q9q_pts.sol 120 1 3000000 1000000 and the same for q9_lines (via run_slot.sh); ogquot_expand.py quot/q9_X.map q9q_X.sol.exact exp_X.txt; ./ktabu og_X.txt exp_X.txt polish_X.sol 420 1 (via run_slot.sh); assemble.sh",
    "score": min(kp, kl),
    "pts": kp,
    "lines": kl,
    "valid": bool(vp and vl),
    "next": "pts quotient never reached 26 heavy vertices (lines did): longer or more ktq restarts on q9_pts; polish from c8's 240 expansion as a second start",
}
line = json.dumps(row)
print(line)
print('pts:', op, '| lines:', ol)
if '--dry' not in sys.argv:
    with open('/home/user/degree-diameter/research/squads/d16D7_r3/scoreboard.jsonl', 'a') as f:
        f.write(line + '\n')
    print('appended to scoreboard.jsonl')
