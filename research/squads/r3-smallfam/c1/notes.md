# c1 notes: literature on metacyclic bounds (round r3-smallfam)

Run: 2026-10-25, about 06:15 to 06:35 UTC (20-minute box). Tools: WebSearch, WebFetch, and pdftotext on two fetched PDFs (copies in `c1/thesis_pdf/` and `c1/dougherty_pdf/`). No git, no heavy computation.

## Bottom line
- I could NOT read the metacyclic theorem of Macbeth, Šiagiová, Širáň, Discrete Math. 312 (2012) 94–99. Every route to its abstract or body was blocked (see Access log). Whether it is an upper bound, a construction, or something else is UNVERIFIED.
- Nothing I read states an upper bound on the order of Cayley graphs of metacyclic groups in terms of degree, diameter and action order o. Nothing I read states the fibre bound (§2.3) or N ≤ (2D+1)^((o+1)(Δ−1)) (§2.4). Absence from what I read is not proof of absence.
- The only upper-bound method I read in full is Dougherty–Faber's, which is for Abelian groups only.

## Access log (what was blocked; nothing was worked around)
- https://oro.open.ac.uk/30423 (the Open Research Online record, which carries the abstract): HTTP 403 Forbidden. Not retried.
- https://www.sciencedirect.com/science/article/pii/S0012365X1100149X: HTTP 403 Forbidden.
- https://doi.org/10.1016/j.disc.2011.03.038 redirects to https://linkinghub.elsevier.com/retrieve/pii/S0012365X1100149X. That page returned only the word "Redirecting", with no abstract.
- https://link.springer.com/article/10.1007/s10801-018-0822-6 and https://link.springer.com/article/10.1007/s00373-013-1361-5: each redirects to an identity-provider login (idp.springer.com/authorize). Not followed.
- https://dblp.uni-trier.de/pid/36/3705.html: "Access Denied" bot-protection page. Not worked around.
- https://www.ma.imperial.ac.uk/~hmacbeth/ (readable): lists the paper with its exact title, co-authors Jana Šiagiová and Jozef Širáň, and "Discrete Mathematics 312 (2012)". No PDF link. Read via WebFetch extraction.

## Quotes I read

### 1. Macbeth thesis (single-page excerpt)
URL: https://www.math.auckland.ac.nz/mathwiki/images/2/21/The_Degree-Diameter_Problem%2C_and_Some_Cayley_Graphs_on_Cyclic_Groups.pdf
- pdfinfo reports `Pages: 1`. The file holds only the title and abstract page, so it cannot settle the metacyclic question. Verified by my own pdftotext run.
- Verbatim (read by me): "For Cayley graphs on abelian groups, computational evidence for small values of d suggests that for most k and d > k the maximal possible order is close to a Moore-like upper bound, approximately d^k/k!." (The fraction was reconstructed from the layout text.)
- Verbatim (read by me): "For the special case of Cayley graphs on cyclic groups, and of diameter two, computational evidence still suggests that the maximal possible order is close to this theoretical bound 1 + d + d^2/2."
- Metacyclic: grep for "metacyc" returned 0 hits.

### 2. Dougherty–Faber, arXiv:math/9412223 (full text read via pdftotext)
URL: https://arxiv.org/pdf/math/9412223 (abstract page: https://arxiv.org/abs/math/9412223)
- Verbatim: "For instance, if we only consider the Cayley graphs of Abelian groups, then we can replace F with the free Abelian group on d generators, which is simply Z^d" (rendered "Zd" in the text).
- Verbatim: "A simple path-counting argument gives upper bounds for the size n of a Cayley graph with d generators and diameter limit k".
- Verbatim: "So |S_k| and |S_k′| give upper bounds for the undirected and directed versions of this case of the degree-diameter problem."
- Proposition 2 (verbatim): "the undirected Cayley graph for G and g_1, ..., g_d has diameter at most k if and only if S_k + N = Z^d".
- Theorem 11 (verbatim): "The largest possible size for the undirected Cayley graph of an Abelian group on two generators having diameter k is 2k^2 + 2k + 1."
- The paper also quotes Fiduccia, Forcade and Zito for an Abelian digraph bound: "an Abelian Cayley digraph on three generators with diameter k has size at most 3(k + 3)^3/25" (written "3(k + 3)3 /25" in the text).
- The grep for "metacyc", "non-abelian" and "nonabelian" returned 0 hits. The paper does not treat metacyclic or non-Abelian groups.
- The arXiv abstract, read through WebFetch (quote-capped extraction, not byte-checked): "We address the degree-diameter problem for Cayley graphs of Abelian groups (Abelian graphs), both directed and undirected."

### 3. Erskine, arXiv:1403.4741 "Diameter 2 Cayley Graphs of Dihedral Groups" (WebFetch, UNVERIFIED wording)
URL: https://arxiv.org/abs/1403.4741
- Opening sentence, verbatim per WebFetch: "We consider the degree-diameter problem for Cayley graphs of dihedral groups."
- Per WebFetch's paraphrase, the upper and lower estimates for diameter 2 match d^2/2 asymptotically. The Moore-type bound is about d^2/2 for diameter 2 in any group, so this is a construction matching the trivial bound. UNVERIFIED.
- Dihedral groups are metacyclic (Z_n ⋊ Z_2). This is a diameter-2 result for one metacyclic family and says nothing about general diameter or general action order.

### 4. Erskine and Tuite, arXiv:1708.02425 "Large Cayley graphs of small diameter"
URL: https://arxiv.org/abs/1708.02425
- The abstract (read through WebFetch) does not mention metacyclic groups, Abelian bounds, or Macbeth, Šiagiová or Širáň. The introduction was not read.

### 5. Macbeth–Šiagiová–Širáň: search-engine summaries only (UNVERIFIED)
- The search tool paraphrased the abstract as: "A further result covers Cayley graphs of metacyclic groups at arbitrary degree and diameter." This is not a quote.
- The search tool also gave "(9/25)(d+3)(d−2) for cyclic groups and (3/8)(d^2−4) for Abelian groups" as lower-bound leading terms. One summary noted a conflicting labelling in a DML-CZ item. UNVERIFIED.
- The brief's quote "a result for Cayley graphs of metacyclic groups for general degree and diameter" could not be confirmed from any page I read.

### 6. Leads not read
- Rajeevsarathy and Sarkar, "Bound on the diameter of split metacyclic groups", https://arxiv.org/pdf/1802.08811. Only its title appeared in search results. It may bound a group diameter rather than a degree-diameter order. Relevance UNVERIFIED.
- A later Springer article on Abelian Cayley graphs (s10801-018-0822-6) is reported by search summaries to give stronger Abelian lower bounds. Blocked by login redirect. UNVERIFIED.

## My own observation (not from a source)
- Dougherty–Faber reduce the problem to a free object of a family and say they consider "certain families (usually varieties) of groups". Metacyclic groups are not a variety. Example: S_3 × S_3 is not metacyclic. Its abelianization is Z_2 × Z_2, so any cyclic quotient has order at most 2; a cyclic normal subgroup with cyclic quotient would then have order at least 18, which needs an element of order 18, and S_3 × S_3 has largest element order 6. So the Dougherty–Faber free-object method does not apply directly. A universal group such as Z[ζ_o]^(...) ⋊ Z_k would have to be used instead, as §2.3 does.

## Answers
- Is §2.3 or §2.4 published? Not found in anything I read. The closest published material I read is Dougherty–Faber's Abelian counting bound (Proposition 2 and the |S_k| bound). That is the Abelian analogue, not the metacyclic result.
- The Macbeth–Šiagiová–Širáň metacyclic result is still UNVERIFIED. If it is a construction, §2.3 and §2.4 still look unpublished as far as I can tell. Confidence is low because the key source was not read.

## Next steps (for the coordinator)
- Get the 2012 abstract and metacyclic theorem through a copy the sandbox can reach, for example an author copy or a library copy, or the MathSciNet review (MR2852512 is listed on the Imperial page). I did not try MathSciNet.
- If the abstract says "a result for Cayley graphs of metacyclic groups for general degree and diameter" and that result is a construction, the §2.3 and §2.4 bounds are not contradicted by it. An upper-bound result would need a direct check.
