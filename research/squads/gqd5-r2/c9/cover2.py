import json
N = {2:7, 3:13, 4:21, 5:31}
CAPM = {5:7, 4:9, 3:6, 2:11}   # verified max cores containing that order (search), total cores also <= 11
def feasible(cnt):
    tot = sum(cnt.values())
    if tot == 1: return True
    if tot > 11: return False
    return all(cnt[s] == 0 or tot <= CAPM[s] for s in cnt)
res = {}
def gen(idx, cnt, tot):
    if idx == 0:
        pass
    for s in [5,4,3,2]:
        pass
import itertools
best = {}
for c5 in range(0,8):
  for c4 in range(0,10):
    for c3 in range(0,7):
      for c2 in range(0,12):
        cnt = {5:c5,4:c4,3:c3,2:c2}
        tot = c5+c4+c3+c2
        if tot == 0: continue
        if not feasible({s:v for s,v in cnt.items() if v>0}): continue
        K = c5*31 + c4*21 + c3*13 + c2*7
        if K not in best or tot < sum(best[K].values()):
            best[K] = {s:v for s,v in cnt.items() if v>0}
M = 100
while (M+1) in best: M += 1
print("contiguous from 7 up to", M, "(windows cover 7..100, cliques above)")
print("first gap above 100:", M+1)
json.dump({str(k): v for k, v in sorted(best.items()) if 94 <= k <= M}, open('plan_d8.json','w'), indent=0)
print(sorted(best.items())[:0], [ (k,best[k]) for k in range(101, 121) if k in best])
