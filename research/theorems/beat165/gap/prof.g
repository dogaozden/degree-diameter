Read("cosetsearch2.g");
t := TableOfMarks("U3(5)"); G := UnderlyingGroup(t); o := OrdersTom(t);
idx := List(o, x -> Size(G)/x);
cls := Filtered([1..Length(o)], i -> idx[i] >= 300 and idx[i] <= 54241);
t0 := Runtime(); reps := List(cls, i -> RepresentativeTom(t, i)); Print("reps ", Runtime()-t0, " ms\n");
t0 := Runtime(); acts := List(reps, H -> FactorCosetAction(G, H)); Print("acts ", Runtime()-t0, " ms\n");
t0 := Runtime(); n := 0;
for i in [1..10] do for j in [1..Length(cls)] do
  orbs := Orbits(Image(acts[j], reps[i]), [1..idx[cls[j]]]); n := n + Number(orbs, x -> Length(x) <= 16 and Length(x) >= 6);
od; od;
Print("orbits for 10 rows ", Runtime()-t0, " ms, small orbits ", n, "\n");
QUIT;
