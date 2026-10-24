#!/bin/bash
# usage: export_order.sh n outfile
cat > /tmp/claude-0/-home-user-degree-diameter/f8a36126-b548-5f60-bd9a-01a3e8198698/scratchpad/exp_$1.g << EOG
n := $1;
out := OutputTextFile("$2", false); SetPrintFormattingStatus(out, false);
for i in [1..NrSmallGroups(n)] do
  G := SmallGroup(n, i);
  subs := Filtered(MaximalNormalSubgroups(G), N -> Index(G, N) = 2);
  if Length(subs) = 0 then continue; fi;
  el := AsSSortedList(G);
  tab := MultiplicationTable(el);
  WriteAll(out, Concatenation(String(n), " ", String(i), " ", String(Length(subs)), "\n"));
  for row in tab do WriteAll(out, Concatenation(JoinStringsWithSeparator(List(row, x -> String(x-1)), " "), "\n")); od;
  for S in subs do WriteAll(out, Concatenation(JoinStringsWithSeparator(List(el, function(x) if x in S then return "1"; else return "0"; fi; end), " "), "\n")); od;
od;
CloseStream(out);
QUIT;
EOG
gap -q -b -o 4g /tmp/claude-0/-home-user-degree-diameter/f8a36126-b548-5f60-bd9a-01a3e8198698/scratchpad/exp_$1.g < /dev/null
