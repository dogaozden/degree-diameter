# gap_export.g: write the multiplication table and an Aut-reduced (s1, s2) plan of a group for hx.c.
# Called as:  gap -q -o 4g gap_export.g  with variables set beforehand:
#   GRP  : the group (e.g. SmallGroup(n, i))
#   TAB  : output path of the table ("N e" then N rows of N 0-based entries, row x = x*y)
#   PLAN : output path of the plan (lines "s1 s2": s1 over Aut(G)-orbit representatives of G\{e},
#          s2 over Stab_Aut(s1)-orbit representatives of G\{e,s1})
#   USEAUT : true/false (false: s1 over all of G\{e}, s2 over all of G\{e,s1})
el := AsSSortedList(GRP);;
n := Length(el);;
eidx := Position(el, One(GRP)) - 1;;
f := OutputTextFile(TAB, false);;
SetPrintFormattingStatus(f, false);;
AppendTo(f, n, " ", eidx, "\n");;
for x in el do
  row := List(el, y -> Position(el, x * y) - 1);;
  AppendTo(f, JoinStringsWithSeparator(List(row, String), " "), "\n");;
od;
CloseStream(f);;
f := OutputTextFile(PLAN, false);;
SetPrintFormattingStatus(f, false);;
if USEAUT then
  A := AutomorphismGroup(GRP);;
  orbs := Orbits(A, el);;
  for o in orbs do
    s1 := o[1];;
    if s1 <> One(GRP) then
      st := Stabilizer(A, s1);;
      for o2 in Orbits(st, el) do
        s2 := o2[1];;
        if s2 <> One(GRP) and s2 <> s1 then
          AppendTo(f, Position(el, s1) - 1, " ", Position(el, s2) - 1, "\n");;
        fi;
      od;
    fi;
  od;
else
  for s1 in el do
    if s1 <> One(GRP) then
      for s2 in el do
        if s2 <> One(GRP) and s2 <> s1 then
          AppendTo(f, Position(el, s1) - 1, " ", Position(el, s2) - 1, "\n");;
        fi;
      od;
    fi;
  od;
fi;
CloseStream(f);;
QUIT;
