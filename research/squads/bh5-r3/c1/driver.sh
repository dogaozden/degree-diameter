#!/bin/bash
# c1 driver: sweep (7,5) h=3 over orders 1731..1845 (multiples of 3, skip >300 groups), fewest groups first.
# Runs one sweep at a time; per-order cap 600 s; stops starting new orders after DEADLINE (epoch seconds).
C=/home/user/degree-diameter/research/beyond-haar-d5/coset
DEADLINE=$1
cd $C
for o in 1749 1761 1779 1797 1731 1743 1773 1785 1803 1821 1833 1839 1737 1758 1845 1767 1791 1770 1734 1788 1794 1809 1806 1812 1815 1818 1827 1830 1842 1755 1746 1740 1752 1782 1776 1764 1836; do
  now=$(date +%s)
  if [ $now -ge $DEADLINE ]; then echo "STOP before $o at $(date)"; break; fi
  echo "START $o $(date +%T)"
  timeout 600 nice -n 10 ./sweep.sh $o 3 7
  echo "END $o rc=$? $(date +%T)"
done
echo DRIVER_DONE $(date +%T)
