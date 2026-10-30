#!/bin/bash
# runs after queue55.sh: (5,5) |H| = 3 and |H| = 4 exhaustive sweeps above 384, then in parallel
# (7,5) |H| = 2 annealing sweep upward from 1220 and (6,5) |H| = 2 annealing sweep above 684.
cd "$(dirname "$0")"
# (started in parallel with queue55.sh at 06:42)
# (5,5) |H| = 3 (|G| = 3N/2, N = 390..440), exhaustive
for o in 585 591 597 603 609 615 621 627 633 639 645 651 657 594 606 618 630 642 654 588 612 636 660 600 624; do
  ./sweep_exh.sh $o 3 5 3 "[1..NrSmallGroups($o)]"; echo "$o (5,5) h3 done $(date -u +%H:%M)" >> logs/queue_next.log
done
# (5,5) |H| = 4 (|G| = 2N, N = 388..440), exhaustive
for o in 776 808 824 856 872 848 792 784 840 816 880; do
  ./sweep_exh.sh $o 4 5 3 "[1..NrSmallGroups($o)]"; echo "$o (5,5) h4 done $(date -u +%H:%M)" >> logs/queue_next.log
done
# (7,5) upward sweep moved to queue75b.sh (started at 06:40)
for o in 686 688 690 692 694 696 698 700 702 706 708 710 712 714 716 718; do
  ./sweep.sh $o 2 6 3 "[1..NrSmallGroups($o)]" 1; echo "$o (6,5) done $(date -u +%H:%M)" >> logs/queue_next.log
done
wait
