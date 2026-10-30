# meta_coords2.g: for G = C_P0 : C_K0 built by meta_group.g (x = xp, y = yp), print r with y x y^-1 = x^r and every
# set in SOLS (export_sd.g element numbers) as pairs (i, j) = x^i y^j.  Read after meta_group.g.
n := Size(G);; els := ShallowCopy(AsSSortedList(G));; ix := PositionSorted(els, One(G));;
old := List([1..n], i -> i);; old[1] := ix; old[ix] := 1;;
elt_ := k -> els[old[k+1]];;
x := xp;; y := yp;;
r := First([0..P0-1], t -> y * x * y^-1 = x^t);;
Print("m ", P0, " k ", K0, " r ", r, "\n");
coord := function(g) local i, j; for j in [0..K0-1] do for i in [0..P0-1] do if x^i * y^j = g then return [i, j]; fi; od; od; return fail; end;;
for line in SOLS do Print("S ", JoinStringsWithSeparator(List(line, k -> JoinStringsWithSeparator(List(coord(elt_(k)), String), ",")), " "), "\n"); od;
QUIT;
