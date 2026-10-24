# Lean for the frontier Haar records (diameters 8–10)

Goal: kernel-checked proofs (only propext, Classical.choice, Quot.sound; no sorry, admit, axiom, native_decide) for the
Haar-graph records at D = 8, 9, 10. Everything up to D = 6 is already in Lean (lean/BipartiteDD; see Axioms.out.txt).

What exists: lean/BipartiteDD/Haar/Graph.lean defines the Haar graph of a finite group G and a set S, proves it
bipartite of degree |S|, and proves diameter ≤ 5 from the covering condition (S⁻¹S)² = G = (SS⁻¹)² (haar_ediam_le_five).
Records 1152, 1728, 2620, 2640, 2662 are proved through it (Haar/Record*.lean, Cert*.lean), which is the pattern to copy.

The search side: research/frontier/haar_gen3.c, build_haar2.py (rebuilds a graph from a sol file and checks it by
two BFS), check_haar_indep.py, HAAR_GEN_NOTES.md (the covering condition for general D: words alternating s⁻¹t of
length ≤ D−1 from the identity cover G on each side). Sol files: research/frontier/sols/<cell>_<group>_<n>_s<seed>.txt.

Rules for every job
- Work on your own branch lean-haarD-<job>; push at least hourly and before you stop; pull/rebase before pushing.
- Run `bash scripts/stop_check.sh` before each long step; if it says stop, push and exit. Time limit 5 hours.
- Build only the modules you touch (`lake build BipartiteDD.Haar.<Module>`); heavy modules one at a time (memory).
- Accept nothing without: the theorem statement in the BRIEF form below, `#print axioms` showing only the three
  standard axioms (append to lean/Axioms.lean and regenerate Axioms.out.txt for your theorems), and no sorry.
- Don't use scheduling tools; wait for long builds with plain polling of the build log.
- Report in research/lean-haarD/STATUS-<job>.md: done, partial (what remains), or blocked (exact error).

Statement form for a record: `theorem nb_<Δ>_<D> : IsBipartiteDegDiam G_rec Δ D` with the vertex count proved, like
nb_8_5_haar. A record graph may be superseded by a bigger one while you work; finish the one you started anyway.

**Never end your turn while a build is running.** A cloud session stops when its turn ends, and background builds die with it.
Several workers stopped on Oct 23 with "stage builds are running" in their STATUS and nothing finished. Run builds in the
foreground, one module at a time. If a build is long, poll its log in the same turn. Keep going until the record theorem and
its Axioms file build, or until you are truly blocked.

**If the record theorem times out at `isDefEq` on a cover argument** (seen in d6D10 and d7D9b): the lemma states the cover
through the `[Group G]` instance, while a cover written for a concrete product group goes through the direct instances. The
two are defeq, but comparing them under `∃ x ∈ S` binders blows up, and heartbeats, `have hc : … := cover` and `@[irreducible]`
don't help. Fix, from STATUS-d6D10c.md: define `CoverHyp {G} [Group G] (S : Finset G) : Prop` as the lemma's hypothesis
body, write the word product once generically (`wordOf`), prove `cover : CoverHyp SS` by unfolding, and pass it directly.
See Haar/D6D10/Words.lean.
