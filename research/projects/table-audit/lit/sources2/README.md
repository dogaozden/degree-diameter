# sources2: files downloaded by the round-2 literature sub-agent (2026-10-26)

Data only. Nothing here is meant to be executed. Notes are in ../LITERATURE2.md.

| file | what | source URL |
|---|---|---|
| perez-roses_thesis_2012_excerpt.txt | H. Pérez-Rosés, PhD thesis "Large networks bounded in degree and diameter" (Univ. Newcastle, 2012; PDF metadata title "The Maximum Degree-and-Diameter-Bounded Subgraph"). pdftotext excerpts: §5.3 "Bipartite lifts", Table 5.1 "Orders of the largest known bipartite graphs", wiki remarks, refs [47]–[49], [63], [103]–[107]. Full PDF: 1,731,412 bytes, sha256 15a9a583191e7ce17aa2d4593d165f1a419704cf20ea11122a70696f791c0a09 | https://ndownloader.figshare.com/files/54389441 (record: https://openresearch.newcastle.edu.au/articles/thesis/Large_networks_bounded_in_degree_and_diameter/29002925) |
| perez-roses_table5.1_fonts.txt | Words of Table 5.1 (PDF page 84) with their font names, from pdfplumber. `B…SFBX1095` = bold. Shows which cells the thesis marks bold ("obtained with the aid of our methods") | same PDF |
| feria-puron_thesis_2015_excerpt.txt | R. Feria Purón, PhD thesis "Large interconnection networks with given degree and diameter" (Univ. Newcastle, 2015): §3.2.3 "Large Bipartite Graphs", §4.8, §4.9 "Catalogues and Upper Bounds" (Props 4.13–4.17). Full PDF: 5,811,324 bytes, sha256 e3a60f638a3d6cc76d4d1bd497a598f49d12c863f116b00b4e789ef3952cf77f | https://ndownloader.figshare.com/files/54314375 (record: https://openresearch.newcastle.edu.au/articles/thesis/Large_interconnection_networks_with_given_degree_and_diameter/28960712) |
| wiki_bipartite_oldid296_2012-01-17.wikitext | Combinatorics Wiki bipartite page, first revision (17 Jan 2012, "CW>Gpineda"), raw wikitext | http://combinatoricswiki.org/index.php?title=The_Degree_Diameter_Problem_for_Bipartite_Graphs&oldid=296&action=raw |
| wiki_bipartite_current.wikitext | same page, current revision (18 Feb 2022) | http://combinatoricswiki.org/index.php?title=The_Degree_Diameter_Problem_for_Bipartite_Graphs&action=raw |
| wiki_bipartite_history.txt | page history (4 revisions), text only | http://combinatoricswiki.org/index.php?title=The_Degree_Diameter_Problem_for_Bipartite_Graphs&action=history |
| zbmath_1017.05089_delorme-gomez-2002.txt | zbMATH entry for Delorme–Gómez, "Some new large compound graphs", EJC 23 (2002): summary (the abstract) and the 17-item reference list | https://zbmath.org/?q=an:1017.05089 |
| zbmath_0649.05043_bond-delorme-1988.txt | zbMATH review of Bond–Delorme, Ars Combin. 25C (1988): says the paper has a table for 3 ≤ Δ ≤ 16, 3 ≤ D ≤ 10 with references | https://zbmath.org/?q=an:0649.05043 |
| zbmath_0623.05048_delorme-1985-jgt.txt | zbMATH entry for Delorme, JGT 9 (1985) (abstract only) | https://zbmath.org/?q=an:0623.05048 |
| zbmath_0784.05028_bond-delorme-1993.txt | zbMATH review of Bond–Delorme, "A note on partial Cayley graphs", DM 114 (1993) | https://zbmath.org/?q=an:0784.05028 |
| dg2002_openalex.json | OpenAlex record of Delorme–Gómez 2002 (no repository copy, no abstract) | https://api.openalex.org/works/doi:10.1006/eujc.2002.0581 |
| dg2002_unpaywall.json | Unpaywall record (bronze OA at publisher only) | https://api.unpaywall.org/v2/10.1006/eujc.2002.0581?email=research@example.org |
| dg2002_elsevier_api_metadata.xml | Elsevier article API, metadata view (openArchiveArticle = true; full text needs an API key) | https://api.elsevier.com/content/article/pii/S0195669802905810 |
| comellas_desc_g9_DG-excerpt.txt | Comellas's description page, D = 9: the Delorme–Gómez general-graph entries and the earlier version "LRI Rapport 905 (05/1994)" | https://web.mat.upc.edu/francesc.comellas/delta-d/desc_g/desc_g9.html |
| cvt_census/b5.json … b10.json | MathDataHub queries on the Potočnik–Spiga–Verret census of all cubic vertex-transitive graphs on ≤ 1280 vertices: the 5 largest bipartite graphs of diameter D (D = 5..10), with girth, arc-transitivity, Cayley flag | https://data.mathhub.info/api/query/cvt?filter=(diameter%3DD)%26%26(is_bipartite%3Dtrue)&properties=order,cvt_index,diameter,girth,is_bipartite,is_cayley,is_arc_transitive&order=-order&page=1&per_page=5 (collection page https://data.mathhub.info/collection/cvt) |
| cvt_census/g_168.json, g_506.json, g_234.json, g_768.json | the same records with the graph in sparse6 (largest bipartite VT cubic graph of diameter 7, 9, 8, 10) | same API, filter (order=n)&&(diameter=D)&&(is_bipartite=true), properties including `graph` |
| cvt_census/all2.json … all9.json | the 2 largest cubic VT graphs of diameter D = 2..9, bipartite or not | same API, filter (diameter=D) |
| oeis_A241162.txt | OEIS A241162, "Largest order of a cubic vertex-transitive graph of diameter d" | https://oeis.org/search?q=id:A241162&fmt=text |
| cvt_census/check_output.txt | my check of those four graphs: own sparse6 decoder plus BFS from every vertex (degree set, bipartite, diameter, girth) | computed here |
| cvt_census/check_s6.py.txt | copy of the checker script I ran (from the scratchpad, not from this folder) | written here |

Not saved: the two full thesis PDFs (re-downloadable from the figshare URLs above, checksums given), the Pérez-Rosés 2014
EJGTA survey (https://ejgta.org/index.php/ejgta/article/download/96/28; nothing new on bipartite cells), and
arXiv:2608.27253 (general graphs only).
