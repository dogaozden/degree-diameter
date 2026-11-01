# girth of the H(3) incidence graph and closed non-backtracking walk counts at a root (fiber argument)
exec(open('walkcount.py').read().split('# walks of length')[0])
print("girth check: shortest cycle through root 0 is >=", min([L for L in range(1,10) if cnt[L][0] > 0] or [99]))
print("closed NB walks at root by length:", {L: cnt[L][0] for L in range(0, 10) if cnt[L][0]})
