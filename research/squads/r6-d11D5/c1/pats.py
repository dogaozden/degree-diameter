"""List the 3 new points x 3 new lines incidence patterns with no isolated new vertex, up to side-preserving
row and column permutations. Output: index, edge count, PAT string for kkk.py, and the dual (transpose) class."""
import itertools
def canon(M):
    return min(tuple(M[p[i]][q[j]] for i in range(3) for j in range(3))
               for p in itertools.permutations(range(3)) for q in itertools.permutations(range(3)))
def transpose(key):
    return tuple(key[3 * j + i] for i in range(3) for j in range(3))
classes = set()
for bits in range(512):
    M = [[(bits >> (3 * i + j)) & 1 for j in range(3)] for i in range(3)]
    if any(sum(r) == 0 for r in M) or any(sum(M[i][j] for i in range(3)) == 0 for j in range(3)):
        continue
    classes.add(canon([list(M[i]) for i in range(3)]))
def pat(key):
    return ",".join(f"{i}-{j}" for i in range(3) for j in range(3) if key[3 * i + j])
order = sorted(classes, key=lambda k: (sum(k), k))
print(len(order), "classes")
for idx, key in enumerate(order, 1):
    t = canon([[transpose(key)[3 * i + j] for j in range(3)] for i in range(3)])
    dual = "self-dual" if t == key else "dual=" + pat(t)
    print(f"{idx:2d} E={sum(key)} PAT={pat(key)} | {dual}")
