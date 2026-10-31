# meta_group2.g: G = C_M0 : C_K0 with y x y^-1 = x^R0 (R0^K0 = 1 mod M0), as a permutation group on M0 + K0 points:
# x = (t -> t+1) on Z_M0, y = (t -> R0 t) on Z_M0 times a K0-cycle.  Read before export_sd.g.
xp := PermList(Concatenation(List([0..M0-1], t -> (t + 1) mod M0 + 1), [M0+1..M0+K0]));;
yp := PermList(Concatenation(List([0..M0-1], t -> (R0 * t) mod M0 + 1), List([0..K0-1], j -> M0 + (j + 1) mod K0 + 1)));;
G := Group(xp, yp);;
if Size(G) <> M0 * K0 then Error("meta_group2: wrong order"); fi;
