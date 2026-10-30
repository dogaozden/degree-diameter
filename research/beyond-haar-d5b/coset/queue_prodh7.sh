#!/bin/bash
# (7,5): relatives of the 1200 record group with |H| = 3 (1280 vertices) and |H| = 4 (1320 vertices)
cd "$(dirname "$0")"
Q() { ./prodh_sweep.sh "$1" "$2" $3 7 20; echo "$1 h$3 done $(date -u +%H:%M)" >> logs/queue_prodh.log; }
Q sl25c2a_x_c8 "DirectProduct(SmallGroup(240,89), CyclicGroup(8))" 3
Q sl25c2b_x_c8 "DirectProduct(SmallGroup(240,90), CyclicGroup(8))" 3
Q sl25_x_c16 "DirectProduct(SL(2,5), CyclicGroup(16))" 3
Q s5_x_c16 "DirectProduct(SymmetricGroup(5), CyclicGroup(16))" 3
Q a5_x_c32 "DirectProduct(AlternatingGroup(5), CyclicGroup(32))" 3
Q gl25_x_c4 "DirectProduct(GL(2,5), CyclicGroup(4))" 3
Q sl25c2a_x_c11 "DirectProduct(SmallGroup(240,89), CyclicGroup(11))" 4
Q sl25c2b_x_c11 "DirectProduct(SmallGroup(240,90), CyclicGroup(11))" 4
Q s5_x_c22 "DirectProduct(SymmetricGroup(5), CyclicGroup(22))" 4
Q sl25_x_d22 "DirectProduct(SL(2,5), DihedralGroup(22))" 4
