G := SmallGroup(176,17);;
els := AsList(G);;
idx := function(x) return Position(els, x); end;;
m := Size(G);;
f := OutputTextFile("/home/user/degree-diameter/research/squads/s384r2/c4/sg176_17.txt", false);;
SetPrintFormattingStatus(f, false);;
AppendTo(f, m, "\n");;
for i in [1..m] do
  for j in [1..m] do
    AppendTo(f, idx(els[i]*els[j])-1, " ");
  od;
  AppendTo(f, "\n");
od;
CloseStream(f);;
QUIT;
