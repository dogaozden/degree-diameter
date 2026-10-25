#!/bin/sh
# consistency check of hx's negatives with the independent annealer (hanneal) at (4,7), order 432
cd "$(dirname "$0")/.."
for g in 30 31 247 249; do
  echo 'GRP := SmallGroup(432, '$g');; el := AsSSortedList(GRP);; nn := Length(el);; f := OutputTextFile("/tmp/claude-0/-home-user-degree-diameter/2c3fb1ba-9359-5c52-a9c4-6d81a7db2df8/scratchpad/cc_tab_'$g'.txt", false);; SetPrintFormattingStatus(f, false);; AppendTo(f, nn, " ", Position(el, One(GRP)) - 1, "\n");; for x in el do AppendTo(f, JoinStringsWithSeparator(List(el, y -> String(Position(el, x * y) - 1)), " "), "\n");; od; CloseStream(f);; QUIT;' | gap -q
  for s in 1 2; do echo "432#$g seed $s: $(nice -n 5 ./hanneal /tmp/claude-0/-home-user-degree-diameter/2c3fb1ba-9359-5c52-a9c4-6d81a7db2df8/scratchpad/cc_tab_$g.txt 4 7 60 $s 8 /tmp/claude-0/-home-user-degree-diameter/2c3fb1ba-9359-5c52-a9c4-6d81a7db2df8/scratchpad/cc_sol.txt 2>/dev/null | tail -1)" >> runs/hx_vs_hanneal_d4D7.txt; done
done
