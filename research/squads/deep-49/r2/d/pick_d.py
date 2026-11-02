import random, re, json
# unambiguous descriptions only: dihedral D_N (m = N/2, k = 2, r = -1) and C_p : C_k with forced action
rows = [(2486,3,'D2486'),(2494,3,'D2494'),(2498,1,'D2498'),(2506,3,'D2506'),(2510,5,'D2510'),(2514,3,'D2514'),
        (2518,1,'D2518'),(2522,3,'D2522'),(2524,3,'D2524'),(2526,5,'D2526'),(2487,1,'C829 : C3'),(2493,1,'C277 : C9')]
pick = random.Random(49).sample(rows, 3)
out = []
for N, i, desc in pick:
    if desc.startswith('D'):
        m, k = N // 2, 2; r = m - 1
    elif '829' in desc:
        m, k = 829, 3
        r = next(pow(x, 276 // 3, 829) for x in range(2, 829) if pow(x, 276 // 3, 829) != 1)
    else:
        m, k = 277, 9
        r = next(pow(x, 276 // 3, 277) for x in range(2, 277) if pow(x, 276 // 3, 277) != 1)
    assert m * k == N and pow(r, k, m) == 1 % m, (N, desc)
    out.append((N, i, desc, m, k, r))
    print(f"g{N}_{i}\t{desc}\tm={m} k={k} r={r}")
