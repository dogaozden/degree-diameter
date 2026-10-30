#!/bin/bash
# (7,5): bi-coset graphs with |H| = 3 (|G| = 3N/2, N = 1232..1320), exhaustive (cap 2M unions, then 10 s annealing)
cd "$(dirname "$0")"
for o in 1851 1854 1857 1860 1863 1866 1869 1875 1878 1881 1884 1887 1893 1896 1899 1902 1905 1908 1911 1914 1917 1923 1926 1929 1932 1935 1938 1941 1947 1950 1953 1956 1959 1962 1965 1971 1974 1977 1848 1890 1980 1968 1836; do
  ./sweep_exh.sh $o 3 7 10 "[1..NrSmallGroups($o)]"; echo "$o (7,5) h3 done $(date -u +%H:%M)" >> logs/queue_h3_75.log
done
