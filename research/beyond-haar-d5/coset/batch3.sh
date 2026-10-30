#!/bin/bash
./run_group2.sh s7_h28 "SymmetricGroup(7)" 28 5 60 > /dev/null
./run_group2.sh a5xa5_h20 "DirectProduct(AlternatingGroup(5), AlternatingGroup(5))" 20 5 60 > /dev/null
ids=$(echo 'Print(Filtered([1..NrSmallGroups(720)], i -> not IsSolvable(SmallGroup(720, i))), "\n"); QUIT;' | gap -q | tr -d ' \n')
echo "720 non-solvable: $ids"
./sweep.sh 720 4 5 "$ids"
echo BATCH3_DONE
