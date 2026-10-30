#!/bin/bash
# stop every search of this session (queues first, then the workers), and remove temporary directories
cd "$(dirname "$0")"
for pat in "[q]ueue[0-9a-z_]*\.sh" "[f]ocus[0-9]*\.sh" "[e]xh75\.sh" "[r]edo1053\.sh" "[a]fter[0-9a-z_]*\.sh" "[r]estart55\.sh" \
           "[x]args -P" "[r]un_one[a-z0-9_]*\.sh" "[s]weep[a-z_]*\.sh" "[p]rod[a-z]*_sweep\.sh" "[s]creen7\.sh"; do
  for p in $(pgrep -f "$pat"); do kill $p 2>/dev/null; done
done
sleep 2
for pat in "[.]/dcenum " "[.]/b4a2y " "[.]/b4a1x " "[.]/haar5x " "[g]ap.*sg_export" "[g]ap.*gap_tab" "[g]ap.*dc2_lib" "[.]/vl " "[b]4a2x "; do
  for p in $(pgrep -f "$pat"); do kill $p 2>/dev/null; done
done
sleep 2
rm -rf coset/tmp* exh/locks exh/grp/g*_*.txt exh/grp/g*_*.gens exh/grp/a1_* exh/grp/h_*
echo "stopped $(date -u +%H:%M)"
