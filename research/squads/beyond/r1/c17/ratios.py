# Bipartite Moore bound for each candidate cell, header record, and fraction of the bound.
def Mb(D, d):
    return 2 * sum((d - 1) ** i for i in range(D))
def Mb_adj(D, d):
    return Mb(D, d) - 6 if D not in (3, 4, 6) else Mb(D, d)
cells = {(17, 5): 33792, (18, 5): 42840, (17, 7): 5631276, (18, 7): 7240212}
for (d, D), rec in cells.items():
    m = Mb_adj(D, d)
    print(f"cell (Delta={d}, D={D}): Moore-type bound {m}, header record {rec}, ratio {rec/m:.4f}")
# Count of vertices of H(q) (incidence graph of generalized hexagon): 2*(q^6-1)/(q-1)
def H(q):
    return 2 * (q**6 - 1) // (q - 1)
print("H(13) =", H(13), " 9*H(13) =", 9 * H(13))
print("H(16) =", H(16), " 3*H(16) =", 3 * H(16), " 2*H(16) (H x K2, diam 7, deg 18) =", 2 * H(16))
print("H(11) =", H(11), " 13*H(11) =", 13 * H(11))
