# Local formalization task

The provided package is an uncompiled candidate, not a completed proof. Read README.md,
VERIFICATION_REPORT.md, audit/verification_status.json, and logs/compile_attempts.txt first.

Begin with the pinned Lean 4.19.0 / Mathlib environment. Check lake-manifest.json against the
Mathlib commit's own manifest. Run scripts/check_candidate.sh and save actual compiler output.
Repair source/API errors without weakening definitions or assertions. The source uses ordinary
decide, not native_decide, for the finite witness; adjust resource budgets or split certificates
if reduction is too slow, but do not introduce unproved assumptions.

Important distinctions:

- Witness.existence is intended to be an actual 46-vertex graph theorem, but has not compiled.
- Profiles.profile_threshold is explicitly a theorem about numerical profiles. Its incidence and
  cut hypotheses must be proved for arbitrary eligible graphs before it yields graph minimality.
- Arithmetic.all_orders_parameters only supplies numerical parameters. It does not realize
  a graph at each order.
- Targets.lean contains proposition definitions. No main theorem has been proved merely by
  writing those definitions or running #check on their names.

After compiling the candidate library, implement the missing graph layer. For a graph with all
degrees in {2,3,4,5}, prove:

1. The ten actual edge-type counts exhaust its edges.
2. The four incidence equations and the three weighted index/order identities.
3. For positive e25 and e33, an edge crosses the degree-3/non-degree-3 cut, and an edge crosses
   the {2,5}/{3,4} cut. These are the two numerical cut conditions used by Profiles.
4. Positive graph gap implies Profiles.positiveGap; order at most 46 implies order60 at most 2760.
5. Apply Profiles.profile_threshold and derive both MinimalityTarget and ExtremalProfileTarget.

For the infinite construction, use the exact construction in input/research_report.pdf, section 5.
For odd k>=3, use two subdivision vertices per hub-cycle edge and one per matching edge;
attach u to hub 0. For l>=3, construct the prism, subdivide one edge with w, and connect u to w.
Prove all actual graph properties and index formulas. Parallel edges must receive distinct
subdivision vertices. The final graph must be simple. Do not substitute numerical profiles
for the graph construction. Use k=7 for even orders and k=5 for odd orders.

Finish by declaring proofs of the existing target propositions (not altered versions), combine
into FullTarget, compile the entire project, print all main-theorem axioms, and preserve logs.
Report partial success exactly if anything remains. An arXiv/Substack description must not say
fully Lean-verified until the full graph statement and its proof have actually passed this process.
