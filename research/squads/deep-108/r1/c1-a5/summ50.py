# usage: summ50.py FILE... -- connected-member stats (uBA+uAA <= 300) and proxy median over all members
import sys, statistics
for fn in sys.argv[1:]:
    rows = [l.split() for l in open(fn) if l.startswith("M ")]
    conn = sorted(int(r[3]) + int(r[4]) + int(r[5]) for r in rows if int(r[3]) + int(r[4]) <= 300)
    prox = sorted(int(r[3]) + int(r[4]) + (int(r[5]) if int(r[5]) >= 0 else 0) for r in rows)
    print(f"{fn}: n={len(rows)} connected={len(conn)} ({100*len(conn)/len(rows):.1f}%) "
          f"minC={conn[0] if conn else None} connected p10={conn[len(conn)//10] if conn else None} "
          f"connected median={statistics.median(conn) if conn else None} proxy median={statistics.median(prox)} "
          f"best3={conn[:3]}")
