"""Re-derive the properties of the (16,5) chart chart_u8 (33,792 graph) from the walk rules."""
from chartlib import read_chart_txt
ch = read_chart_txt('../squad165/charts/chart_u8.txt', 4)
s = ch.summary()
print('k=%d q=%d singular NB patterns: %d' % (s['k'], s['q'], s['singular']))
for side, pat, r in s['singular_list']: print('  ', side, pat, 'rank', r)
print('pencil failures (side, i, j, covered):', s['pencil_fail'])
print('diagonal by closed backtracking walks: A covers %d/%d, B covers %d/%d' % (s['diagA'][0], ch.full, s['diagB'][0], ch.full))
cyc = ch.cycle_patterns()
print('4-cycle patterns: %d, singular on A: %d, on B: %d' % (len(cyc), sum(r < 4 for p, r, _ in cyc), sum(r < 4 for p, _, r in cyc)))
