"""Coverage summary of the exhaustive all-groups runs (allgroups.py, Haar and lift modes) and the annealing screens.
For each run file: orders covered, groups per status (rigorous filters / searched / skipped), solutions, and the best
costs among the searched groups.  Usage: python3 summarize.py > runs/coverage_summary.md"""
import glob
import os
import re
from collections import Counter

HERE = os.path.dirname(os.path.abspath(__file__))


def status(field):
    if field.startswith('pass') or field == 'lift':
        return 'searched'
    if field.startswith('abfail'):
        return 'abelianization bound'
    if field.startswith('rank'):
        return 'rank test'
    if field.startswith('skipped-order'):
        return 'order skipped'
    if field.startswith('|G/G'):
        return 'heuristic skip'
    if 'timeout' in field or 'too-big' in field:
        return 'NOT searched (timeout/too big)'
    return field


def orders_str(orders):
    orders = sorted(orders)
    if not orders:
        return '-'
    runs, start, prev = [], orders[0], orders[0]
    for o in orders[1:]:
        if o == prev + 1:
            prev = o
            continue
        runs.append((start, prev))
        start = prev = o
    runs.append((start, prev))
    return ', '.join(f'{a}' if a == b else f'{a}–{b}' for a, b in runs)


def main():
    print('| run | orders | groups | rigorous filters | searched | not searched | solutions (order, id) | best costs (no solution) |')
    print('|---|---|---|---|---|---|---|---|')
    files = sorted(glob.glob(os.path.join(HERE, 'runs', 'allgroups_d*.tsv')) + glob.glob(os.path.join(HERE, 'runs', 'lift_b*_D*.tsv')))
    for f in files:
        rows = [l.rstrip('\n').split('\t') for l in open(f) if l.strip()]
        rows = [r for r in rows if len(r) >= 9]
        orders = {int(r[0]) for r in rows if r[0].isdigit()}
        st = Counter(status(r[5]) for r in rows if r[1] != '*')
        skipped_orders = [r[0] + ' (' + r[5] + ')' for r in rows if r[1] == '*']
        sols = [(int(r[0]), int(r[1])) for r in rows if r[1] != '*' and r[7].isdigit() and int(r[7]) > 0]
        best = sorted((int(r[8]), int(r[0]), int(r[1])) for r in rows if r[1] != '*' and r[8].isdigit() and r[7] == '0')
        nf = st['abelianization bound'] + st['rank test']
        ns = st['NOT searched (timeout/too big)'] + st['heuristic skip']
        print(f"| {os.path.basename(f)} | {orders_str(orders)}{' (skipped: ' + '; '.join(skipped_orders) + ')' if skipped_orders else ''} | "
              f"{sum(st.values())} | {nf} | {st['searched']} | {ns} | {sols if sols else 'none'} | "
              f"{', '.join(f'{c} ({o},{i})' for c, o, i in best[:3])} |")


if __name__ == '__main__':
    main()
