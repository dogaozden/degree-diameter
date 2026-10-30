# meta_group.g: G = C_p : C_k with y x y^-1 = x^r, r of multiplicative order d mod p (d | k, d | p-1), as a permutation
# group on p + k points: x = (t -> t+1) on Z_p, y = (t -> r t) on Z_p times a k-cycle.  Read before export_sd.g with
# P0, K0, D0 bound (P0 prime).  Sets G and prints nothing.
r0 := First([2..P0-1], a -> OrderMod(a, P0) = P0 - 1)^((P0 - 1) / D0) mod P0;;
xp := PermList(Concatenation(List([0..P0-1], t -> (t + 1) mod P0 + 1), [P0+1..P0+K0]));;
yp := PermList(Concatenation(List([0..P0-1], t -> (r0 * t) mod P0 + 1), List([0..K0-1], j -> P0 + (j + 1) mod K0 + 1)));;
G := Group(xp, yp);;
if Size(G) <> P0 * K0 then Error("meta_group: wrong order"); fi;
