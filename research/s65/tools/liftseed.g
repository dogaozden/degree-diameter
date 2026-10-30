# Write a Haar graph H(G,S) as a voltage lift of an h+h base by a subgroup Gam of index h, for liftseed.c.
# S is given by haarex2 indices (element 0 = identity, then AsSSortedList order without the identity).
# usage: gap -q -c 'K:=SmallGroup(351,5);; SIDX:=[0,1,11,84,220,254];; GAMIDX:=1;; FN:="x.txt";;' liftseed.g
elms := AsSSortedList(K); e := One(K); elms := Concatenation([e], Filtered(elms, x -> x <> e));
S := List(SIDX, i -> elms[i + 1]);
subs := List(Filtered(ConjugacyClassesSubgroups(K), c -> Index(K, Representative(c)) in [2, 3]), Representative);
Gam := subs[GAMIDX]; h := Index(K, Gam);
tr := List(LeftCosets(K, Gam), c -> Representative(c));   # left cosets t Gam
tr := Concatenation([e], Filtered(tr, t -> not t in Gam));
gl := AsSSortedList(Gam); gl := Concatenation([e], Filtered(gl, x -> x <> e)); n := Length(gl);
out := OutputTextFile(FN, false); SetPrintFormattingStatus(out, false);
AppendTo(out, n, " ", h, " ", Length(S) * h, "\n");
for a in gl do AppendTo(out, JoinStringsWithSeparator(List(gl, b -> String(Position(gl, a * b) - 1)), " "), "\n"); od;
# (t_i g, A) ~ (s t_i g, B); s t_i = t_j g' with g' in Gam  =>  base edge a_i - b_j, voltage g' (left multiplication)
for i in [1..h] do for s in S do
    x := s * tr[i];
    j := First([1..h], k -> tr[k]^-1 * x in Gam);
    AppendTo(out, i - 1, " ", j - 1, " ", Position(gl, tr[j]^-1 * x) - 1, "\n");
od; od;
CloseStream(out);
Print("WROTE ", FN, " |Gam|=", n, " h=", h, " ", StructureDescription(Gam), " (", Length(subs), " index-2/3 subgroup classes)\n");
QUIT;
