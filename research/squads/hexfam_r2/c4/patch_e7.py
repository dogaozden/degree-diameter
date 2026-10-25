src = open('/home/user/degree-diameter/research/squads/hexfam_r2/c4/e7roots.py').read()
old = """    def dfs(chosen):
        k = len(chosen)
        if k == n: return list(chosen)"""
new = """    budget = [4000]
    def dfs(chosen):
        k = len(chosen)
        if budget[0] <= 0: return None
        budget[0] -= 1
        if k == n: return list(chosen)"""
assert old in src
src = src.replace(old, new)
old2 = """    for t in range(tries):
        c0 = rng.randrange(len(R))
        res = dfs([c0])"""
assert old2 in src
src = src.replace(old2, """    for t in range(tries):
        c0 = rng.randrange(len(R))
        budget[0] = 4000
        res = dfs([c0])""")
open('/home/user/degree-diameter/research/squads/hexfam_r2/c4/e7roots.py', 'w').write(src)
print('patched')
