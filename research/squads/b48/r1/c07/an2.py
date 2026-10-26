exec(open('/home/user/degree-diameter/research/squads/b48/r1/c07/analyze.py').read().split("def stats")[0])
import collections
print("good (best<=20):")
for d in sorted(data, key=lambda d: d['best']):
    if d['best'] <= 20:
        print(d['N'], 'm',d['m'],'k',d['k'],'r',d['r'],'ord',d['o'],'g',d['g'],'cent',d['cent'],'fac m',factor(d['m']),'fac k',factor(d['k']),'best',d['best'])
# (ord,k) table of mean best
tab = collections.defaultdict(list)
for d in data: tab[(d['o'], d['k'])].append(d['best'])
print("\n(ord,k): count mean min")
for key, v in sorted(tab.items(), key=lambda t: sum(t[1])/len(t[1]))[:30]:
    print(key, len(v), round(sum(v)/len(v)), min(v))
