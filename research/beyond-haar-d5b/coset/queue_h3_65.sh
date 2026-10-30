#!/bin/bash
# (6,5): bi-coset graphs with |H| = 3 (|G| = 3N/2, N = 686..760), exhaustive, orders with <= 80 groups
cd "$(dirname "$0")"
for o in 1029 1032 1035 1038 1041 1044 1047 1050 1053 1059 1062 1065 1068 1071 1074 1077 1083 1086 1089 1092 1095 1098 1101 1107 1110 1113 1116 1119 1122 1125 1128 1131 1137 1140 ; do
  ./sweep_exh.sh $o 3 6 10 "[1..NrSmallGroups($o)]"; echo "$o (6,5) h3 done $(date -u +%H:%M)" >> logs/queue_h3_65.log
done
