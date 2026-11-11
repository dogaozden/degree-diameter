#!/bin/bash
# all groups of order n (no index-2 requirement): writes "n id 0" + table
cat > /tmp/claude-0/-home-user-degree-diameter/f8a36126-b548-5f60-bd9a-01a3e8198698/scratchpad/expall_$1.g << EOG
n := $1;
out := OutputTextFile("$2", false); SetPrintFormattingStatus(out, false);
for i in [1..NrSmallGroups(n)] do
  G := SmallGroup(n, i); el := AsSSortedList(G); tab := MultiplicationTable(el);
  WriteAll(out, Concatenation(String(n), " ", String(i), " 0\n"));
  for row in tab do WriteAll(out, Concatenation(JoinStringsWithSeparator(List(row, x -> String(x-1)), " "), "\n")); od;
od;
CloseStream(out);
QUIT;
EOG
gap -q -b -o 4g /tmp/claude-0/-home-user-degree-diameter/f8a36126-b548-5f60-bd9a-01a3e8198698/scratchpad/expall_$1.g < /dev/null
