#!/bin/bash
# runs after queue55.sh: (6,5) |H| = 2 bi-coset sweep above 684, then (7,5) |H| = 2 at 2-rich orders above 1200
while pgrep -f "[q]ueue55.sh" > /dev/null; do sleep 30; done
# (5,5) |H| = 3 (|G| = 3N/2, N = 390..440), exhaustive
for o in 585 591 597 603 609 615 621 627 633 639 645 651 657 594 606 618 630 642 654 588 612 636 660 600 624; do
  ./sweep_exh.sh $o 3 5 3 "[1..NrSmallGroups($o)]"; echo "$o (5,5) h3 done $(date -u +%H:%M)" >> logs/queue_next.log
done
for o in 686 688 690 692 694 696 698 700 702 704 706 708 710 712 714 716 718; do
  ./sweep.sh $o 2 6 3 "[1..NrSmallGroups($o)]" 1; echo "$o (6,5) done $(date -u +%H:%M)" >> logs/queue_next.log
done
for o in 1264 1288 1272 1240 1232 1312; do
  ./sweep.sh $o 2 7 5 "[1..NrSmallGroups($o)]" 1; echo "$o (7,5) done $(date -u +%H:%M)" >> logs/queue_next.log
done
