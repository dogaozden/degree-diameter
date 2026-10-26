import itertools
# connected 3x3 nonnegative integer matrices with row and column sums 3, up to row/column permutations
rows = [r for r in itertools.product(range(4), repeat=3) if sum(r) == 3]
classes = set()
for a in rows:
    for b in rows:
        for c in rows:
            if all(a[j] + b[j] + c[j] == 3 for j in range(3)):
                M = (a, b, c)
                best = min(tuple(tuple(M[p[i]][q[j]] for j in range(3)) for i in range(3))
                           for p in itertools.permutations(range(3)) for q in itertools.permutations(range(3)))
                # connectivity
                seen = {0}; st = [0]
                while st:
                    v = st.pop()
                    nb = [3 + j for j in range(3) if M[v][j] > 0] if v < 3 else [i for i in range(3) if M[i][v - 3] > 0]
                    for w in nb:
                        if w not in seen: seen.add(w); st.append(w)
                if len(seen) == 6: classes.add(best)
for c in sorted(classes): print(c)
print(len(classes), "connected classes")
