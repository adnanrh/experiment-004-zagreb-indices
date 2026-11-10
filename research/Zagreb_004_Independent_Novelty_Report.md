# Experiment 004 — Independent Literature and Novelty Investigation

**Review date:** 9 November 2026  
**Proposed result:** The sharp 45/46 threshold for the normalized Zagreb inequality among connected simple graphs with minimum degree exactly 2 and maximum degree exactly 5.  
**Scope:** Literature, mathematical comparison, and bibliographic priority. This is not an independent reproduction of the completed Lean formalization or external peer review.

## 1. Executive summary

**Verdict: NOVELTY SUPPORTED, with qualifications, for the exact threshold and associated extremal results.**

No earlier proof of the exact 45/46 threshold, the stated necessary profile of every 46-vertex counterexample, or the conclusion covering every order from 46 onward was located in the accessible material examined. This supports proceeding to manuscript preparation, conditional on the separate formal-statement audit. It does not certify worldwide priority.

The investigation did uncover important prior art that must change the historical presentation:

- Connected counterexamples with degrees 2, 3, and 5, and infinite families of them, were already available in 2011 [4–6].
- Andova, Cohen, and Škrekovski explicitly give a 137-vertex example [4, p. 657]. A published degree-preserving construction also specializes to a 115-vertex counterexample; that specialization is calculated and independently reconstructed in this review.
- The historical 46-vertex example of Hansen and Vukičević has minimum degree 3 and maximum degree 10, not the required 2 and 5 [2].
- The unrestricted inequality had an equivalent walk-count formulation with counterexamples in 1984, before its later Zagreb-index formulation [10–11].

Accordingly, the defensible contribution is **a sharp finite-order extremal theorem**, not the first disproof of the unrestricted inequality, first connected counterexample with these degree restrictions, first infinite family, or invention of the edge-type method.

## 2. Exact question and interpretation

Ghalavand’s Question I asks for the largest integer up to which every connected graph with minimum degree 2 and maximum degree 5 obeys the normalized Zagreb inequality. It appears on printed page 451 of the 2026 journal paper [1]. The preprint was submitted on 9 September 2025.

For a graph with *n* vertices, *m* edges, and vertex degrees *d(v)*, the quantities under discussion are

\[
M_1=\sum_v d(v)^2,\qquad M_2=\sum_{uv\in E}d(u)d(v).
\]

The inequality is

\[
\frac{M_1}{n}\le\frac{M_2}{m}.
\]

The submitted claim would answer Question I with **45**. **46** is the first order permitting failure. These are complementary descriptions, not competing answers.

The review treats the theorem stated by the project as the object whose novelty is being tested. It does not infer correctness from a GitHub README, AI-generated report, or novelty search. The final Lean source at the specified commit could not be fetched in this browsing environment.

## 3. Historical timeline and prior-art comparison

| Date | Work | What is relevant | Does it establish the submitted threshold? |
|---|---|---|---|
| 1983–1984 | Lagarias, Mazo, Shepp, McKay [10] | Walk-count problem and counterexamples to the equivalent unrestricted inequality. | No degree-2-to-5 threshold found. |
| 2007 | Hansen–Vukičević [2] | AutoGraphiX-associated Zagreb formulation, validity for maximum degree at most four, and a connected 46-vertex counterexample. | No; their example has maximum degree 10. |
| 2009 | Sun–Chen [3] | Validity for degree spread at most two; also spread at most three when the minimum degree is not two. | These leave the exceptional interval from 2 to 5; full text was inaccessible. |
| 2009 | Ilić–Stevanović [7] | Smaller unrestricted connected counterexamples and additional valid graph classes. | Their 19-vertex bicyclic example has leaves, outside the target class. |
| 2010 | Horoldagva–Lee [8] | Connected counterexamples with prescribed positive edge surplus. | No matching degree-bounded order threshold identified. |
| 2011 | Andova–Cohen–Škrekovski [4] | Connected three-degree constructions; an explicit 137-vertex example in the required degree class. | No sharp 45/46 result found. |
| 2011 | Andova and four coauthors [5] | Classification of good degree intervals and general connected constructions. | Degree-interval classification, not minimum vertex order. |
| 2011 | Vukičević and four coauthors [6] | Explicit construction formulas relevant to both equality and failure. | Imply smaller older-method examples, but no submitted sharp result found. |
| 2011–2012 | Abdo–Dimitrov–Gutman [9] | Equality constructions, including related degree patterns. | Equality is not a strict counterexample or a minimality theorem. |
| 2016 | Täubig [11] | Explicitly relates Zagreb indices to walk counts and the earlier history. | No matching restricted threshold found. |
| 2025–2026 | Ghalavand [1] | Exhibits a family beginning at 218 vertices and states Question I. | Poses the exact question addressed here. |

Stevanović records that Hansen presented the AutoGraphiX-associated conjecture at the International Academy of Mathematical Chemistry meeting in 2006 [12]. That is the origin of the modern Zagreb formulation, distinct from the older equivalent walk-count problem.

### 3.1 The old 46-vertex example is different

Inspection of the original Hansen–Vukičević construction gives 20 vertices of degree 3, 20 of degree 5, and 6 of degree 10 [2]. Compare:

| Invariant | Hansen–Vukičević example | Submitted example |
|---|---:|---:|
| Order | 46 | 46 |
| Size | 110 | 67 |
| Minimum degree | 3 | 2 |
| Maximum degree | 10 | 5 |
| First Zagreb index | 1,280 | 436 |
| Second Zagreb index | 3,060 | 635 |

The repeated vertex count does not settle priority for the restricted problem. Conversely, advertising the project as the first 46-vertex Zagreb counterexample would be false.

Another relevant earlier example is the disconnected graph *K₂,₅ ∪ K₄*, attributed to Sun and Chen in Stevanović’s account [12]. It has 11 vertices and the required extreme degrees, but fails connectedness. It therefore does not contradict the proposed threshold.

### 3.2 Equivalent formulations matter

For the number *wₖ* of directed walks of length *k* in a simple undirected graph,

\[
w_0=n,\quad w_1=2m,\quad w_2=M_1,\quad w_3=2M_2.
\]

Thus the Zagreb inequality is equivalent to

\[
w_1w_2\le w_0w_3.
\]

The earlier walk-count literature therefore belongs in the history. Lagarias and coauthors supplied counterexamples in the odd-length-sum case, including the relevant pair of lengths 1 and 2; Täubig explicitly explains the connection [10–11]. This is why searching only for the phrase “Zagreb inequality” would have been inadequate.

The suitable historical wording is “disproved in its Zagreb-index formulation by Hansen and Vukičević in 2007,” accompanied by acknowledgement of the earlier equivalent work—not “first disproved in 2007.”

## 4. Closest prior art and a reproducible check

### 4.1 Why 218 must not be called the previous best bound

The 2011 paper of Andova, Cohen, and Škrekovski identifies a 137-vertex member of its construction on page 657 [4]. Its family has the required minimum and maximum degrees at that parameter choice. The number 137 is a statement about that construction, not a global optimality theorem.

More importantly, earlier degree-preserving constructions already imply a smaller example. Papers [4–6] connect complete bipartite pieces by replacing edges while preserving degrees. The following is **a specialization of established methods**, calculated here—not a claimed new construction.

Take *x* copies of the complete bipartite graph *K₂,₅* and *y* copies of *K₃,₃*. Connect them in a chain by two-edge switches, with one transition between the two kinds of block. Direct counting yields

\[
n=7x+6y,\qquad m=10x+9y,
\]

\[
M_1=70x+54y,\qquad M_2=100x+81y+2,
\]

and consequently

\[
D=mM_1-nM_2=3xy-14x-12y.
\]

Set *x = 7* and *y = 11*. The resulting graph has

\[
(n,m,M_1,M_2,D)=(115,169,1084,1593,1).
\]

It is connected and simple, with minimum degree 2 and maximum degree 5.

I implemented this specialization from the published method, then recomputed connectivity, degrees, edge types, and indices from its actual edge list using exact integer arithmetic. The supplied certificate and standard-library Python script reproduce the result.

**Interpretation:** Earlier published methods imply an upper bound of 115 for the minimum counterexample order. I did not find a statement that 115 was the best previously published bound, and make no such claim. Either the explicit 137-vertex example or the 115-vertex specialization suffices to rule out “218 was the previous best known bound.”

### 4.2 Earlier methods also imply eventual coverage of every order

This is another deduction in the present review, not an assertion that the cited authors stated the following numerical bound.

The six parameter pairs

\[
(x,y)=(7,13),(8,12),(9,11),(10,10),(11,9),(12,8)
\]

give orders 127 through 132, respectively, with positive gaps 19, 32, 39, 40, 35, and 24. Increasing *y* by one increases the order by six and the gap by

\[
3x-12>0.
\]

These six arithmetic progressions cover every integer order at least 127. This proves eventual all-orders existence from the older method; it is not an extrapolation from a finite computation.

The supplied program additionally checks the constructions at all orders from 127 through 500 and 324 parameter pairs. Those checks support the implementation, not the universal argument.

The submitted result remains stronger: it starts at the **sharp boundary 46**, and proves why no smaller example exists. The novelty claim must be that sharp boundary, not infinite families or eventual all-orders existence in isolation.

## 5. Assessment of each proposed contribution

The judgments below concern the accessible literature, conditional on correctness of the submitted theorem. “Likely original” is not a guarantee of priority.

| Contribution | Assessment | Basis and remaining qualification |
|---|---|---|
| **A. Exact minimum order 46** | **Likely original** | No earlier matching exact-minimum theorem found. The known unrestricted 46-vertex example is not in the required degree class. |
| **B. Universal validity through order 45** | **Likely original; central contribution** | The reviewed degree-interval results do not determine this finite-order boundary. This lower bound separates a sharp theorem from merely another construction. |
| **C. Necessary profile of all smallest counterexamples** | **Likely original** | No previous matching profile classification located. This is not a claim of graph uniqueness up to isomorphism. |
| **D. Counterexamples at every order from 46 onward** | **Likely original in this sharp form** | Infinite families and even an eventual all-orders conclusion follow from old methods. Starting at 46 is the substantive distinction. |
| **E. Combined resolution of Question I** | **Novelty supported, subject to stated access limits** | The published question matches the proposed extremal problem; no prior equivalent solution was found. |

### 5.1 What should receive explicit credit

The edge-degree counting approach, the factored interaction coefficient, classification of acceptable degree intervals, and joining incompatible degree patterns are established tools [2,4–6].

The proposed contribution is best described as a **sharp application and refinement of those tools**, using a small-order penalty bound and incidence constraints to identify the extremal profile. I found no basis to advertise a fundamentally new general proof technique.

The distinction between graph order and degree-interval width is important: the parameter in the older good-interval classification measures the width of the permitted degree interval. It must not be read as a bound on the number of vertices [5].

### 5.2 No conflicting central theorem found

No accessible source examined established a qualifying counterexample below 46, an earlier proof of the same 45/46 threshold, or the same complete extremal classification. This is a report of the investigation, not a proof that no such source exists.

As one current forward-citation check, Alotaibi and Ali’s paper, first published 25 May 2026, cites Ghalavand but studies the contraharmonic index [13]. Its inspected content did not provide a resolution of this question. That single example is not an exhaustive census of citations.

## 6. Mathematical significance and consequences

### 6.1 What would be established

Conditional on the separate correctness audit, this would resolve a published finite extremal problem: the precise point where universal validity fails in an exceptional degree class. That is a legitimate specialist graph-theory contribution even without consequences for a famous conjecture.

The proposed extremal profile also gives a structural deduction: every smallest counterexample has a single edge connecting the degree-3 vertices to the degree-2-or-5 vertices. Connectedness makes that edge a bridge, separating parts with 21 and 25 vertices. This follows from the submitted profile and degree counts; it is not a separately discovered literature theorem.

That observation could help enumerate smallest counterexamples. It does **not** answer Ghalavand’s Question II, which asks about the number of counterexamples of a given order [1]. Different graphs can share the same edge-degree profile.

### 6.2 A corollary combining the claim with prior results

Sun and Chen establish validity for degree spread at most two and for spread at most three when the minimum degree is not two [3]. Combining those results with the proposed theorem gives:

> Every connected simple graph with at least two and at most 45 vertices, whose maximum and minimum degrees differ by at most three, satisfies the normalized Zagreb inequality. The order bound is sharp.

Reason: the old results cover all cases except minimum degree 2 and maximum degree 5; the submitted theorem covers that exception and supplies sharpness at 46.

This is a **deduced corollary**, not a claim that it has been separately formalized in Lean or independently checked for bibliographic priority.

### 6.3 What is not established

No major outstanding conjecture or broad foundational theorem was identified whose resolution depends on this numerical threshold. No demonstrated application to molecular stability, reactions, or drug development follows from the theorem.

The broader research value is in a precise, reproducible extremal result and its reported formal verification. The accompanying human–AI case study is interesting, but a single successful investigation cannot isolate the causal effect of prompt wording from the model, tools, search process, and verification workflow.

## 7. Publication recommendations

**Proceed to prepare a conventional research note, while finishing the separate formal-statement audit and resolving the remaining bibliographic gap.** Another proof-development run is not called for by this literature review.

A suitable mathematical title is:

**The sharp order threshold for the Zagreb-index inequality with minimum degree two and maximum degree five**

The introduction should state the exact threshold and classification, acknowledge the earlier connected constructions, and explain that the contribution is finite-order sharpness. Include a complete human-readable proof. Keep the prompting narrative and broader AI commentary principally in the Substack article.

An arXiv preprint in **math.CO** is a natural classification recommendation because that category includes graph theory [14]. A specialist graph-theory or mathematical-chemistry research note is a reasonable journal format; MATCH is a thematically relevant possibility because it published the question and several closest predecessors. This is an assessment of fit, not a prediction of editorial acceptance.

The formalization should be linked at an immutable commit or release and accompanied by reproducibility instructions. Describe the Lean status only as strongly as the separate audit establishes. Do not equate an arXiv posting with peer review; arXiv’s policy also requires disclosure of significant generative-AI assistance and human responsibility for the contents [15].

Before submission, revise any wording equivalent to “first counterexample,” “previous best 218,” “new edge-type technique,” or “first infinite family.” Replace the earlier absolute 2007-disproof date with historically qualified wording.

The remaining priority check should request the complete Sun–Chen paper and seek a brief literature/interpretation check from Ghalavand or an author of the older constructions. Neither an email response nor another AI report alone would constitute peer review, but either could identify missed work efficiently.

A defensible public description, conditional on the formal audit, is:

> We give the exact minimum order of a connected counterexample to the normalized Zagreb-index inequality when the minimum and maximum degrees are two and five. The first failure occurs at 46 vertices. We determine the necessary edge-degree profile at this order and construct counterexamples at every larger order. Earlier work supplied counterexamples and general construction methods; the contribution here is the sharp threshold and extremal analysis.

## 8. Search scope and limitations

The investigation used exact-title, author, citation, numerical-threshold, degree-restriction, edge-profile, and equivalent walk-count searches. Primary sources were pursued through journal PDFs, arXiv, author-hosted manuscripts, and accessible reproductions. Relevant construction pages, diagrams, and tables were inspected as PDF screenshots where available.

Search terms included variants of “comparing Zagreb indices,” “minimum degree 2 maximum degree 5,” “smallest connected counterexample,” “Ghalavand Question I,” “45/46,” degree-pair counts, good degree intervals, and the walk-count inequality. Citation trails and 2025–2026 hits were examined. A representative search and access record accompanies the report; it is not an exhaustive machine-generated search transcript.

**Material limitations:**

1. **Sun–Chen full text was not obtained.** Its abstract and explicit accounts in other primary papers were available. The accessible summary does not settle the threshold, but unexamined details remain a genuine priority risk.
2. **No comprehensive authenticated MathSciNet, zbMATH, or Google Scholar survey was completed.** Google Scholar and Semantic Scholar access was blocked; Crossref and zbMATH retrieval was incomplete or unusable. Search-engine results are not equivalent to full database access.
3. **The completed GitHub source was inaccessible to the browser.** The repository and commit were supplied by the user. This review cannot authenticate the final Lean theorem or compilation logs and does not replace the separate audit.
4. **Unindexed, inaccessible, differently worded, non-English, recent, or unpublished work can be missed.** No responsible search can turn an absence of located results into a proof of global priority.

The 1984 work was examined through an accessible reprint as well as the later mathematical treatment; the large reprint’s screenshot retrieval failed, so that part of the historical check relied on parsed text, not inspection of its diagrams.

## 9. Final conclusion

**NOVELTY SUPPORTED — for the exact 45/46 threshold, the extremal edge-degree classification, and the sharp all-orders conclusion, subject to the limitations above.**

The review found substantial older ingredients, but no earlier resolution of the central exact problem in the accessible sources. The manuscript should therefore be strengthened with those citations and narrower historical claims, not abandoned or advertised as a first general disproof.

The project remains a proposed original specialist result supported by a reported Lean formalization, with formal-statement auditing and external mathematical scrutiny distinct from this literature assessment.

## References

[1] Ali Ghalavand. *On a Conjecture about Comparing the First and Second Zagreb Indices of Graphs*. MATCH **96** (2026), 441–452. DOI: 10.46793/match.96-2.04725. Question I, p. 451. [Journal PDF](https://match.pmf.kg.ac.rs/electronic_versions/Match96/n2/match96n2_441-452.pdf). [Preprint, arXiv:2509.07434](https://arxiv.org/abs/2509.07434).

[2] Pierre Hansen and Damir Vukičević. *Comparing the Zagreb Indices*. Croatica Chemica Acta **80**(2) (2007), 165–168. [Publisher record](https://hrcak.srce.hr/en/12846). [Full text](https://hrcak.srce.hr/en/file/19705).

[3] Lingli Sun and Ting Chen. *Comparing the Zagreb indices for graphs with small difference between the maximum and minimum degrees*. Discrete Applied Mathematics **157**(7) (2009), 1650–1654. [DOI](https://doi.org/10.1016/j.dam.2008.10.007). [Accessible abstract](https://www.researchgate.net/publication/222036832_Comparing_the_Zagreb_indices_for_graphs_with_small_difference_between_the_maximum_and_minimum_degrees). Full text not obtained in this review.

[4] Vesna Andova, Nathann Cohen, and Riste Škrekovski. *Graph Classes (Dis)satisfying the Zagreb Indices Inequality*. MATCH **65**(3) (2011), 647–658. Proposition 3.3; Theorem 5.1; explicit 137-vertex example, p. 657. [Full text](https://match.pmf.kg.ac.rs/electronic_versions/Match65/n3/match65n3_647-658.pdf).

[5] Vesna Andova, Sašo Bogoev, Darko Dimitrov, Marcin Pilipczuk, and Riste Škrekovski. *On the Zagreb index inequality of graphs with prescribed vertex degrees*. Discrete Applied Mathematics **159**(8) (2011), 852–858. DOI: 10.1016/j.dam.2011.01.002. [Author-hosted manuscript](https://users.fmf.uni-lj.si/skreko/Old/MyPapers/01120.pdf). Proposition 3.1 and Theorem 3.1.

[6] Damir Vukičević, Ivan Gutman, Boris Furtula, Vesna Andova, and Darko Dimitrov. *Some Observations on Comparing Zagreb Indices*. MATCH **66**(2) (2011), 627–645. Construction and invariant formulas, p. 639. [Full text](https://match.pmf.kg.ac.rs/electronic_versions/Match66/n2/match66n2_627-645.pdf).

[7] Aleksandar Ilić and Dragan Stevanović. *On comparing Zagreb indices*. MATCH **62** (2009), 681–687. [Author-hosted full text](https://draganstevanovic.wordpress.com/wp-content/uploads/2012/10/zagreb.pdf).

[8] Batmend Horoldagva and Sang-Gu Lee. *Comparing Zagreb indices for connected graphs*. Discrete Applied Mathematics **158** (2010), 1073–1078. [DOI](https://doi.org/10.1016/j.dam.2010.02.013). [Accessible article reproduction](https://www.academia.edu/14380318/Comparing_Zagreb_indices_for_connected_graphs).

[9] Hosam Abdo, Darko Dimitrov, and Ivan Gutman. *On the Zagreb Indices Equality*. Discrete Applied Mathematics **160**(1–2) (2012), 1–8. DOI: 10.1016/j.dam.2011.10.003. [Preprint, arXiv:1106.1809](https://arxiv.org/abs/1106.1809).

[10] Jeffrey C. Lagarias, James E. Mazo, Lawrence A. Shepp, and Brendan D. McKay. *An Inequality for Walks in a Graph*, Problem 83-15. SIAM Review **25**(3) (1983), 403; solution, **26**(4) (1984), 580–582. [Problem DOI](https://doi.org/10.1137/1025084). [Solution DOI](https://doi.org/10.1137/1026112). Reprinted in Murray S. Klamkin, ed., *Mathematical Modelling: Classroom Notes in Applied Mathematics* (SIAM, 1987), pp. 124–126; [accessible reprint](https://www.math.utah.edu/~cherk/teach/5740MathModeling/12mathmodel/sources/Mathematical%20Modelling%2C%20Classroom%20Notes%20in%20Applied%20Mathematics%20%28Murray%20S.%20Klamkin%29%200898712041.pdf).

[11] Hanjo Täubig. *Inequalities for the Number of Walks in Subdivision Graphs*. MATCH **76** (2016), 61–68. [Full text](https://match.pmf.kg.ac.rs/electronic_versions/Match76/n1/match76n1_61-68.pdf).

[12] Sanja Stevanović. *On a Relation Between the Zagreb Indices*. Croatica Chemica Acta **84**(1) (2011), 17–19. DOI: 10.5562/cca1579. Additional primary discussion of the Sun–Chen exception and disconnected counterexample. [Full text](https://hrcak.srce.hr/file/103904).

[13] Abdulaziz Mutlaq Alotaibi and Akbar Ali. *Contraharmonic Index: Extremal Results for Unicyclic Graphs and Bounds for General Graphs*. Journal of Mathematics **2026**, article 6674947, first published 25 May 2026. DOI: 10.1155/jom/6674947. [Full text](https://onlinelibrary.wiley.com/doi/full/10.1155/jom/6674947). Ghalavand appears as reference 14.

[14] arXiv. *Category Taxonomy*, math.CO. [Official page](https://arxiv.org/category_taxonomy). Accessed 9 November 2026.

[15] arXiv. *Content Moderation*. [Official policy](https://info.arxiv.org/help/moderation/index.html). Accessed 9 November 2026.

**Project under review, not independently fetched:** [Experiment 004 repository](https://github.com/adnanrh/experiment-004-zagreb-indices), commit `68a494573fdbd2e629c620a263dafed5853ac26e`. Repository status and completed Lean claims were supplied by the user.
