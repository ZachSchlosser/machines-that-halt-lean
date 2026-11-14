# Claims of the paper and their verdicts under the Lean formalization — 2026-11-14

This ledger lists every checkable claim of Melo, Máximo, Soma, and Castro, "Machines that halt resolve the undecidability of artificial intelligence alignment," Scientific Reports 15, 15591 (2025), doi 10.1038/s41598-025-99060-2, and records the verdict the Lean formalization in this repository settles for it. The formalization is the work of Zach Schlosser with GLM-5.3 and Claude (Anthropic). One entry per claim; each verdict cites the named theorems that settle it. The step-by-step mapping from the paper's arguments to the Lean that verifies them, with verbatim quotes at each step, lives in `ARGUMENT-MAP.md`; this ledger carries the claim-level verdicts.

## Status scheme

- **CONFIRMED** — the Lean build proves the claim as stated.
- **BOUNDARY — READING-DEPENDENT** — the sentence admits a per-system reading and a class-level reading; the build confirms the per-system reading, and the class-level reading meets a standard computability boundary that the build machine-checks.
- **CONFIRMED IN CORRECTED FORM** — the claim survives, and the formalization supplies a correction it needs.
- **AMBIGUITY RESOLVED** — the paper leaves a definition ambiguous, and the build proves the result under both readings.
- **NOT FORMALIZED** — the repository contains no formalization of the claim; each entry states the reason.

## Setting

The paper states its modeling assumption as "AI models are represented as computer programs, which, in turn, are equivalent to Turing Machines (TM)." The formalization adopts that assumption: a model is `Nat.Partrec.Code`, Mathlib's codes for computable partial functions on ℕ (`Aligned.lean:31`), and a judge is `J : ℕ → ℕ → Bool`. Because the paper does not say whether a model that never answers some input counts as aligned, every result is proved under both readings — `alignedVac` (`Aligned.lean:78`, divergence is harmless) and `alignedTot` (`Aligned.lean:111`, the model must answer every input). Passages that make no formal claim — the positioning of the result against Tegmark and Omohundro, the RLHF / Constitutional AI / Constitutional Classifiers comparison, the mortality analogy, and the engineering parameter suggestions (2^80 states, roughly 25 final states) — carry no entries; the ledger covers the paper's theorems, arguments, and constructions.

## CONFIRMED

### C1. Deciding alignment is undecidable
**Paper (Abstract; restated in Introduction and Background):** "The inner alignment problem, which asserts whether an arbitrary artificial intelligence (AI) model satisfices a non-trivial alignment function of its outputs given its inputs, is undecidable." · "We demonstrate that deciding whether an arbitrary AI system will always satisfice such a judge function is undecidable." · "By the reasoning of Rice's theorem, the property of perfect alignment of the AI should be undecidable in general, since it is a non-trivial semantic condition on the program's behavior."
**Lean:** `alignedVac_undecidable` (`Aligned.lean:186`), `alignedTot_undecidable` (`Aligned.lean:235`), `alignedVac_undecidable_by_reduction` (`Reduction.lean:160`), `alignedTot_undecidable_by_reduction` (`Reduction.lean:242`), `T2'_undecidable` (`Reduction.lean:319`).
**Verdict:** The build proves the claim under both readings of "aligned," by three independent routes — Rice's theorem, an explicit reduction to the halting problem, and the diagonal adversary of entry C3. Both theorems take as their hypothesis that the alignment property is non-trivial — some system aligned, another not, the paper's Background framing. For the vacuous reading that condition is exactly the judge rejecting some pair (alignedVac_nontrivial_iff, Aligned.lean:168); for the totality reading it holds under the judge-level conditions (alignedTot_nontrivial_of_judge, Aligned.lean:205) and needs no computability beyond them.

### C2. The proof method: Rice's theorem, equivalent to a halting reduction
**Paper (Abstract):** "This is rigorously proved by Rice's theorem, which is also equivalent to a reduction to Turing's Halting Problem, whose proof sketch is presented in this work."
**Lean:** `ComputablePred.rice₂` applied in `alignedVac_undecidable` and `alignedTot_undecidable` (`Aligned.lean:186`, `:235`); the explicit reductions contradicting `ComputablePred.halting_problem` in `alignedVac_undecidable_by_reduction` (`Reduction.lean:160`) and `alignedTot_undecidable_by_reduction` (`Reduction.lean:242`); the paper's own two-machine non-triviality argument assembled as `paper_nontriviality` (`Aligned.lean:223`) with `alignedTot_nontrivial_of_judge` (`Aligned.lean:205`).
**Verdict:** Both routes the paper names exist as machine-checked proofs, and the adversary argument (C3) supplies a third. The Formal proof's own non-triviality step — "a TM can be built to always output the dummy positive values, and a TM can be built to output at least one dummy negative value" — is assembled as `paper_nontriviality`, which builds the paper's two machines (the always-approved searcher of `exists_alignedTot`, `Aligned.lean:131`, and the constant rejected-output code of `exists_not_alignedVac`, `Aligned.lean:99`) and concludes the property's non-triviality. The reductions are explicit: for each reading the build constructs a computable gadget `g : Code → Code` such that a decider for alignment would decide whether an arbitrary code halts on input 0.

### C3. The informal adversary argument
**Paper (Informal proof):** "If we had such a verifier, we could build an adversarial model that fools the verifier." · "there would be at least one input i, if the verifier V had evaluated the bytes B_M′ of the model to be aligned, for which M′ would return a misaligned output o−, thus fooling the verifier. The complementary fooling example can also be constructed: if the verifier had evaluated the bytes B_M′ of the model to be misaligned, M′ would return an aligned output o+, thus also fooling the verifier." · "Thus, the only resolution to this apparent contradiction is the non-computability of the verifier V itself."
**Lean:** `T1_adversary` (`Adversary.lean:100`), `T1_no_verifier_vac` (`Adversary.lean:147`), `T1_no_verifier_tot` (`Adversary.lean:159`); self-reference via `Nat.Partrec.Code.fixed_point₂`; the missing computation step via `partrec_approved_select` (`Aligned.lean:125`); the base-model form of the paper's narrative — the adversary "would behave as the initial model M for most of its inputs and outputs" — as `T1_adversary_param` (`Adversary.lean:251`).
**Verdict:** The build proves the argument: every computable verifier faces one code that fools it in one direction or the other, so no computable verifier decides alignment under either reading. The formalization supplies one step the paper leaves implicit — under the per-input reading of the non-triviality condition the adversary must compute an approved output for each input, which `Nat.rfind` delivers. The self-reference the paper justifies by appeal to quines and "Turing's Proof" is Kleene's recursion theorem, which Mathlib provides. `T1_adversary_param` restores the paper's framing with an arbitrary base model `m`: the constructed code follows `m` at every input other than the designated fooling input when the verifier says aligned, and is aligned at every input when the verifier says misaligned, so "behave as the initial model M for most of its inputs and outputs" holds verbatim in the aligned-verdict branch.

### C4. The misalignment construction
**Paper (A special decidable case):** "while a model can be architecturally proven aligned, the same procedure can be employed to make a proven misaligned model. Any program that is guaranteed to halt can have its outputs altered so that it becomes misaligned, although the resulting model could have very little utility due to the dummy output nature."
**Lean:** `T6_misaligning` (`Adversary.lean:496`), with `misFun` (`Adversary.lean:473`) and `partrec₂_misFun` (`Adversary.lean:476`).
**Verdict:** Confirmed as stated. The wrapper is computable in the base model — the "same procedure" as the masking construction — and alters outputs: the designated input's answer becomes a rejected one. For every base model guaranteed to halt, the wrapped system answers every input and returns the rejected answer at the designated input, so it is misaligned under both readings. The paper's usefulness-preserving variant (translate the input, compute, translate the output back) is documented in the theorem's docstring and not formalized.

## BOUNDARY — READING-DEPENDENT

### D1. Ensuring halting decidability ensures alignment decidability
*(Recategorized 2026-11-14 from DISCONFIRMED after owner review: the sentence is ambiguous between a per-system reading and a class-level reading, and the paper's operative program is the per-system one. The entry keeps its ID.)*
**Paper (Implications):** "Ensuring the decidability of the halting property of autonomous systems also ensures the decidability of other non-trivial properties of such systems, especially their alignment. Therefore, it becomes computationally possible to verify their properties, although not necessarily tractable."
**Lean:** `T6_masking` (`Adversary.lean:418`), `T5_promise` (`Overclaim.lean:318`), `alwaysHalting_alignment_undecidable` (`Overclaim.lean:150`), with `isTotalCode` (`Overclaim.lean:54`), `judgeZero` (`Overclaim.lean:62`), and `simGadget_aligned_iff` (`Overclaim.lean:104`).
**Verdict:** The sentence carries two readings. Read per system — for each model guaranteed to halt, its alignment can be established — the build confirms it: `T6_masking` proves the wrapped model aligned for every base model guaranteed to halt, `T5_promise` decides alignment for any model that halts on the finitely many inputs below a bound, and the paper's running example, networks with fixed-size inputs, sits in that case by design. Read class-level — one procedure deciding alignment for every always-halting program — the reading meets a standard computability boundary, machine-checked here: for any code `c` and input `n` the build uses a program that halts on every input (a bounded step-count simulation, so the program under test is the one that may diverge, never the constructed one) and outputs 1 if `c` halts on `n` within `k` steps and 0 otherwise; with the judge that approves exactly 0, that program is aligned exactly when `c` never halts on `n`, so a checker of that kind would decide non-halting, contradicting `halting_problem_not_re`.

### D2. An always-halting model has its alignment asserted computationally
*(Recategorized 2026-11-14 from DISCONFIRMED with D1.)*
**Paper (Final remarks):** "Developing an AI model that always halts allows for the alignment and other properties of the AI model to be asserted computationally, a task that would be computationally impossible for arbitrary models."
**Lean:** `T6_masking` (`Adversary.lean:418`); the trailing clause is entry C1.
**Verdict:** The sentence carries the same two readings as D1. Per system it is confirmed: constructing a provably aligned always-halting model is what the masking wrapper does (`T6_masking`), and the paper's own program names it — "there is also a countable set of AIs that are proven to be aligned," whose development the Final remarks state as the objective. The class-level reading meets the same standard boundary as D1. The trailing clause — that verification is impossible for arbitrary models — is entry C1, confirmed.

## CONFIRMED IN CORRECTED FORM

### D3. Halting decidability for a class makes the alignment problem decidable
*(Recategorized 2026-11-14 from DISCONFIRMED after owner review: the paper's sentence is its own concession, read charitably as covering the classes it has in mind — its fixed-size-input networks — rather than every class with decidable halting. The entry keeps its ID.)*
**Paper (Final remarks):** "It is important to note that guaranteeing the decidability of the halting problem for a class of AI systems does not guarantee their alignment, it just guarantees that the alignment problem (and other properties) becomes decidable."
**Lean:** `alwaysHalting_alignment_undecidable` (`Overclaim.lean:148`).
**Verdict:** The hedge holds in the paper's own class — networks with fixed-size inputs, where halting is guaranteed and the alignment problem is decidable by the exhaustive check (E1). The formalization makes explicit a boundary the sentence leaves implicit: for the class of total codes over unbounded inputs, halting is trivially decidable inside the class and alignment on that class stays undecidable — a standard computability fact, machine-checked here — so halting decidability alone does not carry the implication. What the formalization adds is the explicit statement, not a refutation of the concession itself.

### E1. The exhaustive finite-input check
**Paper (A special decidable case):** "Given that their inputs are also fixed in size and have a length of L bits, we could check every possible combination, which is 2^L inputs, and verify if the J_v(i, o) results in 1 for every combination. Thus, the alignment becomes decidable, though intractable."
**Lean:** `T5_promise` (`Overclaim.lean:318`), with `t5Check` (`Overclaim.lean:262`) and `exists_settling` (`Overclaim.lean:290`).
**Verdict:** The check exists as a partial recursive procedure, and the paper's wording is accurate in its class: the check runs the model on every input, and the networks the section discusses are already guaranteed to halt, so it finishes on them. `T5_promise` makes that halting assumption explicit — for a computable judge and a bound N, a procedure that halts on every code promised to halt on all inputs below N and there decides bounded alignment. The promise form is the theorem's explicit rendering of the assumption the paper's class already satisfies, not a correction the paper needs.

### E2. The masking construction
**Paper (A special decidable case):** "we simply mask the output of the network based on the output of the judge function" · "If the judge disapproves of the output of the network, a dummy output o+ that the judge approves is returned, otherwise, it keeps the default output computed by the network" · "This proves that the resulting AI system will always be aligned" · "This solution may be applied to any model M that is guaranteed to halt."
**Lean:** `T6_masking` (`Adversary.lean:418`), with `maskSel_approved` (`Adversary.lean:398`) and `partrec₂_maskFun` (`Adversary.lean:368`).
**Verdict:** The construction is proved: the wrapper is computable in the base model, aligned under the vacuous reading for every base model, and aligned under the totality reading whenever the base model halts on every input — the paper's stated scope. The paper states each ingredient elsewhere — the judge arrives as compiled bytes, the non-triviality condition supplies the fallback, and the construction's stated scope is models guaranteed to halt — and `T6_masking` gathers all three as explicit conditions of the guarantee. The contribution is the gathering, not the discovery of hidden conditions.

### E3. The formal proof template
**Paper (Formal proof):** "On input i, M′ simulates M on i. If M halts on i, then M′ computes a partial function with property P. If M does not halt on i, then M′ computes a partial function without property P." · "Therefore, there is no Turing machine that decides P."
**Lean:** `T2'` and `T2'_undecidable` (`Reduction.lean:308`, `:319`) formalize the template as written; `alignedVac_halting_reduce` (`Reduction.lean:146`) carries the vacuous reading with the construction reversed.
**Verdict:** The template is the standard Rice reduction schema and is correct as a schema; the reading-dependence belongs to the alignment instantiation. The template works as written only under the totality reading, where a program that diverges fails alignment by failing to answer. Under the vacuous reading a program that never halts produces no outputs and is therefore aligned, so the template's "without property P" branch fails; the vacuous reading needs the gadget reversed to misbehave only after the simulation halts. Both corrected forms are proved, and `T2'_undecidable` needs weaker hypotheses than the Rice route — no computable judge, no rejected pair, only a single approved dummy output.

## AMBIGUITY RESOLVED

### F1. The definition of alignment
**Paper (Background vs. Informal proof):** Background describes alignment as "the AI system never producing harmful output and always adhering to human-specified constraints"; the Informal proof section defines the verifier to return true "if the model is aligned for every input i and output M(i) = o."
**Lean:** `alignedVac` (`Aligned.lean:78`) and `alignedTot` (`Aligned.lean:111`); both undecidable (C1).
**Verdict:** The two passages support different readings of a diverging model, and the paper never chooses. The build defines both and proves the central claim under each, so the ambiguity costs the paper nothing in the end. For the systems the paper proposes — architectures guaranteed to halt by construction — the model answers every input, so the two readings coincide there; the ambiguity concerns the theorem's stated domain of arbitrary programs. The readings differ in strength of hypotheses — the vacuous reading needs only a rejected pair, the totality reading holds even for a judge that approves everything — which is why the repository keeps both.

### F2. The non-triviality condition on the judge
**Paper (Informal proof):** "This judge is required to be nontrivial, meaning that it does not always return a constant value for every (i, o), there is at least one negative input (i−, o−) that returns 0 and at least one output o+ for every input i for which the judge returns 1."
**Lean:** constant reading in `T2'` (`Reduction.lean:308`, hypothesis `∀ j, J j op = true`); per-input reading in `partrec_approved_select` (`Aligned.lean:125`), `exists_gadgetTot` (`Reduction.lean:193`), `T1_adversary` (`Adversary.lean:100`), and `T6_masking` (`Adversary.lean:418`); witnesses for both sides in `exists_alignedVac` (`Aligned.lean:91`), `exists_not_alignedVac` (`Aligned.lean:99`), `exists_alignedTot` (`Aligned.lean:131`), `exists_not_alignedTot` (`Aligned.lean:145`).
**Verdict:** "At least one output o+ for every input i" can mean one output approved everywhere, or a possibly different approved output for each input; the paper's own usage ("a dummy output o+ that the judge approves") suggests the first. The build handles both: the constant reading drives the faithful template, the per-input reading drives the adversary and the masking wrapper, and the witnessing theorems realize the non-triviality the paper asserts.

## NOT FORMALIZED

### G1. The enumerable set of aligned AIs
**Paper (Abstract; Introduction; Discussions):** "there is an enumerable set of provenly aligned AIs that are constructed from a finite set of provenly aligned operations" · "we can compose those models and operations and construct an enumerable infinite set of AI that is guaranteed to have the desired property" · "it is possible to do so for an enumerable set of AI systems that are architecturally designed."
**Reason:** The paper never defines which operations preserve alignment, so the construction has no mathematical content to formalize. The repository's constructive result on this side is the masking wrapper (E2).

### G2. Feed-forward networks always halt
**Paper (A special decidable case):** "These feed-forward neural networks, and even recurrent neural networks (unrolled in time to a finite number of steps), are always guaranteed to have a finite runtime during their inference, in other words, they always halt."
**Reason:** The statement needs a model of neural networks and their computation cost, which Mathlib does not provide. The formalization covers abstract programs; the always-halting property itself enters as the hypothesis `isTotalCode` (`Overclaim.lean:54`).

### G3. The utility-penalty proposal
**Paper (Implications; Eqs. 1–3 and the sentence after Eq. 2):** "This preserves functionality within bounded timeframes while mathematically guaranteeing eventual halting, making alignment verification computationally tractable."
**Reason:** The proposal is stated informally, with no model of the agent, so there is no claim to formalize. The README records two further facts: the proposal's dominance condition asks for a time bound that does not depend on the input, a stronger condition than halting on every input, and the always-halting boundary of D1 does not cover it because the gadget's running time grows with the input. The tractability sentence carries no proof in the paper.

### G4. Loops, agent architectures, the θ parameter, and Test-Time Training
**Paper (Closing the loop; Implications; Final remarks):** "The problem that arises is that if the model is not guaranteed to halt, its output may not be evaluated by the judge function, and the alignment becomes undecidable." · the θ-parameter and final-state mechanism of Figures 3 and 4 · the Test-Time Training design discussion.
**Verdict:** The undecidability sentence in this passage is the central claim and is confirmed (C1). The surrounding discussion — agent loops breaking guarantees, hidden parameters forcing terminal states, TTT architectures converging to trivial solutions — consists of design proposals and informal arguments, which the repository does not formalize.

### G5. The finite-computer hierarchy
**Paper (Informal proof):** "from an engineering perspective, the main takeaway is that for every finite computer, one would need a much larger computer to ascertain a property from the smaller computer. And to make assertions about the larger computer, we would need an even larger computer, and so on."
**Reason:** The passage reasons about finite automata with 2^M states and hierarchies of machines, an informal argument with no theorem stated. The formalization covers abstract programs over ℕ; the finite-memory framing sits outside it.

## Counts

| Status | Entries |
|---|---|
| CONFIRMED | 4 (C1–C4) |
| BOUNDARY — READING-DEPENDENT | 2 (D1–D2, recategorized 2026-11-14) |
| CONFIRMED IN CORRECTED FORM | 4 (E1–E3, D3 recategorized 2026-11-14) |
| AMBIGUITY RESOLVED | 2 (F1–F2) |
| NOT FORMALIZED | 5 (G1–G5) |
| Total | 17 |

## Scope note

Every verdict above cites machine-checked theorems in this repository; the 2026-11-14 recalibration pass changed README wording and Lean comments only, with no theorem or proof touched, and the build below was re-run after it. A second pass the same day recategorized D1 and D2 from DISCONFIRMED to BOUNDARY — READING-DEPENDENT after the owner judged the class-level reading an artifact of the formal statement rather than the paper's claim; the per-system reading, which the paper's constructions carry, is confirmed by `T6_masking` and `T5_promise`, and the class-level exclusion is a standard computability result, machine-checked here. A third pass the same day closed the remaining verification gaps: the two-machine non-triviality argument is assembled (`paper_nontriviality`), the paper's misalignment construction is verified (`T6_misaligning`, entry C4), and the base-model form of the adversary is verified (`T1_adversary_param`); the step-by-step mapping is `ARGUMENT-MAP.md`. The one item the paper announces but never writes — the axiomatic enumeration of entry G1 — stays unverified for that reason. The continuous-integration build fails if any proof contains `sorry`, and each file prints its axioms — `[propext, Classical.choice, Quot.sound]` — beyond which nothing is assumed. I read the paper in full (9 pages, open-access PDF, text extracted with `pdftotext`) for every quotation; the extraction normalizes spacing around subscripts and superscripts, so the quotes render `(i−, o−)` for the paper's `(i⁻, o⁻)`, `o+` for `o⁺`, `2^L` for 2 to the power L, and `J_v(i, o)` for the paper's subscripted judge symbol. Theorem labels T1, T2′, T5, T6, and T10 are the repository's own — the paper numbers none of its results; the mapping is recorded in the README.
