"""Pick the top-K screened jobs from make_jobs3.py --show output (stdin) and print them sorted by group order.
  python3 wave3/make_jobs3.py ... --screen M --show | python3 wave3/pick_top.py K"""
import sys
K = int(sys.argv[1])
rows = []
for ln in sys.stdin:
    if "|" not in ln:
        continue
    head, job = ln.split("|", 1)
    N, sc = head.split()
    if sc == "-":
        continue
    rows.append((float(sc), int(N), job.strip()))
rows.sort()
for sc, N, job in sorted(rows[:K], key=lambda r: r[1]):
    print(job)
