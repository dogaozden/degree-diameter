# The bipartite degree–diameter table (largest known orders), Δ ≤ 16, D ≤ 10

frontier-opus, 2026-10-22.

## Where the numbers come from

- **The live CombinatoricsWiki page could not be read.** From this container its TLS certificate fails verification
  (`curl: (60) unable to get local issuer certificate`, also with the proxy CA bundle; WebFetch got HTTP 503;
  web.archive.org is blocked for the fetch tool). I did not bypass TLS.
- **Main source used:** M. Miller, J. Širáň, *Moore graphs and beyond: a survey of the degree/diameter problem*,
  Electron. J. Combin. Dynamic Survey DS14v2 (May 16, 2013), **Table 4**, p. 37: "The order of the largest known
  bipartite graphs of maximum degree Δ and diameter D, CombinatoricsWiki, accessed on 10 March 2013."
  Downloaded from https://www.combinatorics.org/ojs/index.php/eljc/article/download/DS14/pdf/ and read with pdftotext.
- **Later changes I know of (D = 3 column):** ¹ (13,3) = 274 and (15,3) = 374 are Araujo-Pardo–López (Graphs Combin.
  2022), replacing the survey's 270 and 370; the wiki's current values for (11,3) 190, (13,3) 274, (15,3) 374,
  (16,3) 394, (4,5) 160, (5,5) 336, (7,4) 346, (7,5) 1134, (11,4) 1734 were read from the wiki on 2026-10-10 by an
  earlier session (records/bipartite_dd/CANDIDATES.md) and agree with the survey except for the two AL cells.
  Our own earlier sessions also used (8,5) 1710, (9,5) 2496, (16,4) 5134, (16,3) 394 and the D = 6 column, all equal
  to the survey.
- **Not checked:** whether any D ≥ 7 cell, or D = 5 with Δ ≥ 10, changed on the wiki after March 2013. The wiki page
  was last edited in 2022 (CANDIDATES.md says its table is headed "as of January 2012"). A web search for post-2013
  bipartite records found nothing. Treat every D ≥ 7 value below as "survey value; current wiki value unverified".
- **(11,10)** is unreadable in the PDF text ("130 592 1354", one digit too many or a typo in the survey); I do not
  guess it.
- The wiki's "lowest known upper bounds" table could not be read; below I give the bipartite Moore bound
  2(1 + (Δ−1) + … + (Δ−1)^(D−1)) instead, which is weaker for some cells (e.g. defect results at D = 3, 4).

Legend: M = bipartite Moore graph exists (D = 3, 4, 6 and Δ−1 a prime power): optimal. opt = proved optimal
((3,5) = 56, Jørgensen; (7,3) = 80, Feria-Purón–Miller–Pineda-Villavicencio). → **x** = our verified graph
(records/bipartite_dd/, research-lab/records.json; 19 cells).

## Largest known orders

| Δ \ D | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 |
|---|---|---|---|---|---|---|---|---|
| 3 | 14 M | 30 M | 56 opt | 126 M | 168 | 256 | 506 | 800 |
| 4 | 26 M | 80 M | 160 → **162** | 728 M | 840 | 2,184 | 4,970 | 11,748 |
| 5 | 42 M | 170 M | 336 → **354** | 2,730 M | 3,110 | 9,234 | 27,936 | 90,068 |
| 6 | 62 M | 312 M | 684 | 7,812 M | 8,310 | 29,790 | 117,360 | 452,032 |
| 7 | 80 opt | 346 → **359** | 1,134 → **1,152** | 8,992 → **9,592** | 23,436 | 80,940 | 400,160 | 1,987,380 |
| 8 | 114 M | 800 M | 1,710 → **1,764** | 39,216 M | 40,586 | 201,480 | 1,091,232 | 6,927,210 |
| 9 | 146 M | 1,170 M | 2,496 → **2,662** | 74,898 M | 117,648 | 449,480 | 2,961,536 | 20,017,260 |
| 10 | 182 M | 1,640 M | 4,000 | 132,860 M | 224,694 | 1,176,480 | 7,057,400 | 50,331,156 |
| 11 | 190 → **192** | 1,734 → **1,782** | 5,850 | 142,464 → **148,944** | 398,580 | 2,246,940 | 15,200,448 | unreadable |
| 12 | 266 M | 2,928 M | 8,200 | 354,312 M | 664,300 | 4,650,100 | 30,001,152 | 300,383,050 |
| 13 | 274¹ → **276** | 3,064 → **3,146** | 11,480 | 374,452 → **388,972** | 1,062,936 | 5,314,680 | 50,990,610 | 617,330,936 |
| 14 | 366 M | 4,760 M | 14,760 | 804,468 M | 1,771,560 | 14,172,480 | 95,087,738 | 1,213,477,190 |
| 15 | 374¹ → **376** | 4,946 → **5,070** | 20,496 | 842,048 → **870,440** | 2,480,184 | 14,172,480 | 168,016,334 | 2,300,326,510 |
| 16 | 394 → **396** | 5,134 → **5,440** | 27,300 | 884,062 → **940,846** | 4,022,340 | 36,201,060 | 288,939,118 | 4,119,507,330 |

## Bipartite Moore bound (upper bound)

| Δ \ D | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 |
|---|---|---|---|---|---|---|---|---|
| 3 | 14 | 30 | 62 | 126 | 254 | 510 | 1,022 | 2,046 |
| 4 | 26 | 80 | 242 | 728 | 2,186 | 6,560 | 19,682 | 59,048 |
| 5 | 42 | 170 | 682 | 2,730 | 10,922 | 43,690 | 174,762 | 699,050 |
| 6 | 62 | 312 | 1,562 | 7,812 | 39,062 | 195,312 | 976,562 | 4,882,812 |
| 7 | 86 | 518 | 3,110 | 18,662 | 111,974 | 671,846 | 4,031,078 | 24,186,470 |
| 8 | 114 | 800 | 5,602 | 39,216 | 274,514 | 1,921,600 | 13,451,202 | 94,158,416 |
| 9 | 146 | 1,170 | 9,362 | 74,898 | 599,186 | 4,793,490 | 38,347,922 | 306,783,378 |
| 10 | 182 | 1,640 | 14,762 | 132,860 | 1,195,742 | 10,761,680 | 96,855,122 | 871,696,100 |
| 11 | 222 | 2,222 | 22,222 | 222,222 | 2,222,222 | 22,222,222 | 222,222,222 | 2,222,222,222 |
| 12 | 266 | 2,928 | 32,210 | 354,312 | 3,897,434 | 42,871,776 | 471,589,538 | 5,187,484,920 |
| 13 | 314 | 3,770 | 45,242 | 542,906 | 6,514,874 | 78,178,490 | 938,141,882 | 11,257,702,586 |
| 14 | 366 | 4,760 | 61,882 | 804,468 | 10,458,086 | 135,955,120 | 1,767,416,562 | 22,976,415,308 |
| 15 | 422 | 5,910 | 82,742 | 1,158,390 | 16,217,462 | 227,044,470 | 3,178,622,582 | 44,500,716,150 |
| 16 | 482 | 7,232 | 108,482 | 1,627,232 | 24,408,482 | 366,127,232 | 5,491,908,482 | 82,378,627,232 |

## Who holds what (survey §3.4.5 and wiki colour key, as far as known)

- D = 3, 4, 6 with Δ−1 a prime power: incidence graphs of projective planes, GQs, generalized hexagons (Moore).
- D = 4 and 6 otherwise: Delorme 1985 doubling (and Delorme–Farhi 1984); all now beaten by us.
- D = 5, 7, 8, 9, 10: mostly Loz, Pérez-Rosés, Pineda-Villavicencio (voltage lifts, "updated more than one third of the
  table", survey ref. [240]), plus older Bond–Delorme partial Cayley graphs and Delorme's ∗-products/compounding.
  The exact attribution per cell is on the wiki's colour key, which I could not read.
