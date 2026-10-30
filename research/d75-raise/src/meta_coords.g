# meta_coords.g: for a metacyclic SmallGroup(NN,II) = C_m : C_k, find x (order m, normal) and y (order k) with
# y x y^-1 = x^r, and print every listed connection set S (export.g element numbers) as pairs (i, j) = x^i y^j.
G := SmallGroup(NN, II);; n := Size(G);;
els := ShallowCopy(AsSSortedList(G));; ix := PositionSorted(els, One(G));;
old := List([1..n], i -> i);; old[1] := ix; old[ix] := 1;;
elt_ := k -> els[old[k+1]];;
C := First(NormalSubgroups(G), N -> IsCyclic(N) and Size(N) = MM);;
x := MinimalGeneratingSet(C)[1];;
y := First(els, g -> Order(g) = KK and Size(Intersection(Group(g), C)) = 1);;
r := First([0..MM-1], t -> y * x * y^-1 = x^t);;
Print("structure ", StructureDescription(G), " m ", MM, " k ", KK, " r ", r, "\n");
coord := function(g) local i, j; for j in [0..KK-1] do for i in [0..MM-1] do if x^i * y^j = g then return [i, j]; fi; od; od; return fail; end;;
for line in SOLS do Print("S ", List(line, k -> coord(elt_(k))), "\n"); od;
QUIT;
