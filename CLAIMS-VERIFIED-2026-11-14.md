# Claims of the paper and their verdicts under the Lean formalization — 2026-11-14

This ledger lists every checkable claim of Melo, Máximo, Soma, and Castro, "Machines that halt resolve the undecidability of artificial intelligence alignment," Scientific Reports 15, 15591 (2025), doi 10.1038/s41598-025-99060-2, and records the verdict the Lean formalization in this repository settles for it. The formalization is the work of Zach Schlosser with GLM-5.3 and Claude (Anthropic). One entry per claim; each verdict cites the named theorems that settle it.

## Status scheme

- **CONFIRMED** — the Lean build proves the claim as stated.
- **DISCONFIRMED** — the Lean build proves the claim false.
- **CONFIRMED IN CORRECTED FORM** — the claim survives, and the formalization supplies a correction it needs.
- **AMBIGUITY RESOLVED** — the paper leaves a definition ambiguous, and the build proves the result under both readings.
- **NOT FORMALIZED** — the repository contains no formalization of the claim; each entry states the reason.

## Setting

The paper states its modeling assumption as "AI models are represented as computer programs, which, in turn, are equivalent to Turing Machines (TM)." The formalization adopts that assumption: a model is `Nat.Partrec.Code`, Mathlib's codes for computable partial functions on ℕ (`Aligned.lean:19`), and a judge is `J : ℕ → ℕ → Bool`. Because the paper does not say whether a model that never answers some input counts as aligned, every result is proved under both readings — `alignedVac` (`Aligned.lean:66`, divergence is harmless) and `alignedTot` (`Aligned.lean:114`, the model must answer every input). Passages that make no formal claim — the positioning of the result against Tegmark and Omohundro, the RLHF / Constitutional AI / Constitutional Classifiers comparison, the mortality analogy, and the engineering parameter suggestions (2^80 states, roughly 25 final states) — carry no entries; the ledger covers the paper's theorems, arguments, and constructions.

## CONFIRMED

### C1. Deciding alignment is undecidable
**Paper (Abstract; restated in Introduction and Background):** "The inner alignment problem, which asserts whether an arbitrary artificial intelligence (AI) model satisfices a non-trivial alignment function of its outputs given its inputs, is undecidable." · "We demonstrate that deciding whether an arbitrary AI system will always satisfice such a judge function is undecidable." · "By the reasoning of Rice's theorem, the property of perfect alignment of the AI should be undecidable in general, since it is a non-trivial semantic condition on the program's behavior."
**Lean:** `alignedVac_undecidable` (`Aligned.lean:98`), `alignedTot_undecidable` (`Aligned.lean:160`), `alignedVac_undecidable_by_reduction` (`Reduction.lean:160`), `alignedTot_undecidable_by_reduction` (`Reduction.lean:242`), `T2'_undecidable` (`Reduction.lean:319`).
**Verdict:** The build proves the claim under both readings of "aligned," by three independent routes — Rice's theorem, an explicit reduction to the halting problem, and the diagonal adversary of entry C3. The vacuous reading needs only one rejected (input, output) pair; the totality reading needs a computable judge that approves some output of every input.

### C2. The proof method: Rice's theorem, equivalent to a halting reduction
**Paper (Abstract):** "This is rigorously proved by Rice's theorem, which is also equivalent to a reduction to Turing's Halting Problem, whose proof sketch is presented in this work."
**Lean:** `ComputablePred.rice₂` applied in `alignedVac_undecidable` and `alignedTot_undecidable` (`Aligned.lean:98`, `:160`); the explicit reductions contradicting `ComputablePred.halting_problem` in `alignedVac_undecidable_by_reduction` (`Reduction.lean:160`) and `alignedTot_undecidable_by_reduction` (`Reduction.lean:242`).
**Verdict:** Both routes the paper names exist as machine-checked proofs, and the adversary argument (C3) supplies a third. The reductions are explicit: for each reading the build constructs a computable gadget `g : Code → Code` such that a decider for alignment would decide whether an arbitrary code halts on input 0.

### C3. The informal adversary argument
**Paper (Informal proof):** "If we had such a verifier, we could build an adversarial model that fools the verifier." · "there would be at least one input i, if the verifier V had evaluated the bytes B_M′ of the model to be aligned, for which M′ would return a misaligned output o−, thus fooling the verifier. The complementary fooling example can also be constructed: if the verifier had evaluated the bytes B_M′ of the model to be misaligned, M′ would return an aligned output o+, thus also fooling the verifier." · "Thus, the only resolution to this apparent contradiction is the non-computability of the verifier V itself."
**Lean:** `T1_adversary` (`Adversary.lean:100`), `T1_no_verifier_vac` (`Adversary.lean:147`), `T1_no_verifier_tot` (`Adversary.lean:159`); self-reference via `Nat.Partrec.Code.fixed_point₂`; the missing computation step via `partrec_approved_select` (`Aligned.lean:128`).
**Verdict:** The build proves the argument: every computable verifier faces one code that fools it in one direction or the other, so no computable verifier decides alignment under either reading. The formalization supplies one step the paper leaves implicit — under the per-input reading of the non-triviality condition the adversary must compute an approved output for each input, which `Nat.rfind` delivers. The self-reference the paper justifies by appeal to quines and "Turing's Proof" is Kleene's recursion theorem, which Mathlib provides.

## DISCONFIRMED

### D1. Ensuring halting decidability ensures alignment decidability
**Paper (Implications):** "Ensuring the decidability of the halting property of autonomous systems also ensures the decidability of other non-trivial properties of such systems, especially their alignment. Therefore, it becomes computationally possible to verify their properties, although not necessarily tractable."
**Lean:** `alwaysHalting_alignment_undecidable` (`Overclaim.lean:148`), with `isTotalCode` (`Overclaim.lean:52`), `judgeZero` (`Overclaim.lean:60`), and `simGadget_aligned_iff` (`Overclaim.lean:102`).
**Verdict:** The build refutes the claim for the class of programs that halt on every input over unbounded inputs. For any code `c` and input `n` the build constructs a program that halts on every input — the construction is a bounded step-count simulation, so the program under test is the one that may diverge, never the constructed one — and that program outputs 1 if `c` halts on `n` within `k` steps and 0 otherwise; with the judge that approves exactly 0, that program is aligned exactly when `c` never halts on `n`. A checker correct on all always-halting programs would therefore decide non-halting, contradicting `halting_problem_not_re`. The claim does hold when the input space is finite — that boundary is entry E1.

### D2. An always-halting model has its alignment asserted computationally
**Paper (Final remarks):** "Developing an AI model that always halts allows for the alignment and other properties of the AI model to be asserted computationally, a task that would be computationally impossible for arbitrary models."
**Lean:** `alwaysHalting_alignment_undecidable` (`Overclaim.lean:148`); the second half of the sentence is entry C1.
**Verdict:** The first half is false by the same refutation as D1, in the unconditional form in which the sentence states it; in the paper's own finite-input setting the sentence holds. The second half, that verification is impossible for arbitrary models, is confirmed (C1); what fails beyond the finite-input setting is the claim that guaranteed halting lifts the obstacle.

## CONFIRMED IN CORRECTED FORM

### D3. Halting decidability for a class makes the alignment problem decidable
*(Recategorized 2026-11-14 from DISCONFIRMED after owner review: the paper's sentence is its own concession, read charitably as covering the classes it has in mind — its fixed-size-input networks — rather than every class with decidable halting. The entry keeps its ID.)*
**Paper (Final remarks):** "It is important to note that guaranteeing the decidability of the halting problem for a class of AI systems does not guarantee their alignment, it just guarantees that the alignment problem (and other properties) becomes decidable."
**Lean:** `alwaysHalting_alignment_undecidable` (`Overclaim.lean:148`).
**Verdict:** The hedge holds in the paper's own class — networks with fixed-size inputs, where halting is guaranteed and the alignment problem is decidable by the exhaustive check (E1). The build supplies the boundary the sentence does not state: for the class of total codes over unbounded inputs, halting is trivially decidable inside the class and alignment on that class stays undecidable, so halting decidability alone does not carry the implication. The correction the formalization adds is that stated boundary, not a refutation of the concession itself.

### E1. The exhaustive finite-input check
**Paper (A special decidable case):** "Given that their inputs are also fixed in size and have a length of L bits, we could check every possible combination, which is 2^L inputs, and verify if the J_v(i, o) results in 1 for every combination. Thus, the alignment becomes decidable, though intractable."
**Lean:** `T5_promise` (`Overclaim.lean:316`), with `t5Check` (`Overclaim.lean:260`) and `exists_settling` (`Overclaim.lean:288`).
**Verdict:** The check exists as a partial recursive procedure, and the paper's wording is accurate in its class: the check runs the model on every input, and the networks the section discusses are already guaranteed to halt, so it finishes on them. `T5_promise` makes that halting assumption explicit — for a computable judge and a bound N, a procedure that halts on every code promised to halt on all inputs below N and there decides bounded alignment. The promise form is the theorem's explicit rendering of the assumption the paper's class already satisfies, not a correction the paper needs.

### E2. The masking construction
**Paper (A special decidable case):** "we simply mask the output of the network based on the output of the judge function" · "If the judge disapproves of the output of the network, a dummy output o+ that the judge approves is returned, otherwise, it keeps the default output computed by the network" · "This proves that the resulting AI system will always be aligned" · "This solution may be applied to any model M that is guaranteed to halt."
**Lean:** `T6_masking` (`Adversary.lean:237`), with `maskSel_approved` (`Adversary.lean:217`) and `partrec₂_maskFun` (`Adversary.lean:187`).
**Verdict:** The construction is proved: the wrapper is computable in the base model, aligned under the vacuous reading for every base model, and aligned under the totality reading whenever the base model halts on every input — the paper's stated scope. The paper states each ingredient elsewhere — the judge arrives as compiled bytes, the non-triviality condition supplies the fallback, and the construction's stated scope is models guaranteed to halt — and `T6_masking` gathers all three as explicit conditions of the guarantee. The contribution is the gathering, not the discovery of hidden conditions.

### E3. The formal proof template
**Paper (Formal proof):** "On input i, M′ simulates M on i. If M halts on i, then M′ computes a partial function with property P. If M does not halt on i, then M′ computes a partial function without property P." · "Therefore, there is no Turing machine that decides P."
**Lean:** `T2'` and `T2'_undecidable` (`Reduction.lean:308`, `:319`) formalize the template as written; `alignedVac_halting_reduce` (`Reduction.lean:146`) carries the vacuous reading with the construction reversed.
**Verdict:** The template is the standard Rice reduction schema and is correct as a schema; the reading-dependence belongs to the alignment instantiation. The template works as written only under the totality reading, where a program that diverges fails alignment by failing to answer. Under the vacuous reading a program that never halts produces no outputs and is therefore aligned, so the template's "without property P" branch fails; the vacuous reading needs the gadget reversed to misbehave only after the simulation halts. Both corrected forms are proved, and `T2'_undecidable` needs weaker hypotheses than the Rice route — no computable judge, no rejected pair, only a single approved dummy output.

## AMBIGUITY RESOLVED

### F1. The definition of alignment
**Paper (Background vs. Informal proof):** Background describes alignment as "the AI system never producing harmful output and always adhering to human-specified constraints"; the Informal proof section defines the verifier to return true "if the model is aligned for every input i and output M(i) = o."
**Lean:** `alignedVac` (`Aligned.lean:66`) and `alignedTot` (`Aligned.lean:114`); both undecidable (C1).
**Verdict:** The two passages support different readings of a diverging model, and the paper never chooses. The build defines both and proves the central claim under each, so the ambiguity costs the paper nothing in the end. For the systems the paper proposes — architectures guaranteed to halt by construction — the model answers every input, so the two readings coincide there; the ambiguity concerns the theorem's stated domain of arbitrary programs. The readings differ in strength of hypotheses — the vacuous reading needs only a rejected pair, the totality reading holds even for a judge that approves everything — which is why the repository keeps both.

### F2. The non-triviality condition on the judge
**Paper (Informal proof):** "This judge is required to be nontrivial, meaning that it does not always return a constant value for every (i, o), there is at least one negative input (i−, o−) that returns 0 and at least one output o+ for every input i for which the judge returns 1."
**Lean:** constant reading in `T2'` (`Reduction.lean:308`, hypothesis `∀ j, J j op = true`); per-input reading in `partrec_approved_select` (`Aligned.lean:128`), `exists_gadgetTot` (`Reduction.lean:193`), `T1_adversary` (`Adversary.lean:100`), and `T6_masking` (`Adversary.lean:237`); witnesses for both sides in `exists_alignedVac` (`Aligned.lean:79`), `exists_not_alignedVac` (`Aligned.lean:87`), `exists_alignedTot` (`Aligned.lean:134`), `exists_not_alignedTot` (`Aligned.lean:148`).
**Verdict:** "At least one output o+ for every input i" can mean one output approved everywhere, or a possibly different approved output for each input; the paper's own usage ("a dummy output o+ that the judge approves") suggests the first. The build handles both: the constant reading drives the faithful template, the per-input reading drives the adversary and the masking wrapper, and the witnessing theorems realize the non-triviality the paper asserts.

## NOT FORMALIZED

### G1. The enumerable set of aligned AIs
**Paper (Abstract; Introduction; Discussions):** "there is an enumerable set of provenly aligned AIs that are constructed from a finite set of provenly aligned operations" · "we can compose those models and operations and construct an enumerable infinite set of AI that is guaranteed to have the desired property" · "it is possible to do so for an enumerable set of AI systems that are architecturally designed."
**Reason:** The paper never defines which operations preserve alignment, so the construction has no mathematical content to formalize. The repository's constructive result on this side is the masking wrapper (E2).

### G2. Feed-forward networks always halt
**Paper (A special decidable case):** "These feed-forward neural networks, and even recurrent neural networks (unrolled in time to a finite number of steps), are always guaranteed to have a finite runtime during their inference, in other words, they always halt."
**Reason:** The statement needs a model of neural networks and their computation cost, which Mathlib does not provide. The formalization covers abstract programs; the always-halting property itself enters as the hypothesis `isTotalCode` (`Overclaim.lean:52`).

### G3. The utility-penalty proposal
**Paper (Implications; Eqs. 1–3 and the sentence after Eq. 2):** "This preserves functionality within bounded timeframes while mathematically guaranteeing eventual halting, making alignment verification computationally tractable."
**Reason:** The proposal is stated informally, with no model of the agent, so there is no claim to formalize. The README records two further facts: the proposal's dominance condition asks for a time bound that does not depend on the input, a stronger condition than halting on every input, and the always-halting counterexample of D1 does not cover it because the gadget's running time grows with the input. The tractability sentence carries no proof in the paper.

### G4. Loops, agent architectures, the θ parameter, and Test-Time Training
**Paper (Closing the loop; Implications; Final remarks):** "The problem that arises is that if the model is not guaranteed to halt, its output may not be evaluated by the judge function, and the alignment becomes undecidable." · the θ-parameter and final-state mechanism of Figures 3 and 4 · the Test-Time Training design discussion.
**Verdict:** The undecidability sentence in this passage is the central claim and is confirmed (C1). The surrounding discussion — agent loops breaking guarantees, hidden parameters forcing terminal states, TTT architectures converging to trivial solutions — consists of design proposals and informal arguments, which the repository does not formalize.

### G5. The finite-computer hierarchy
**Paper (Informal proof):** "from an engineering perspective, the main takeaway is that for every finite computer, one would need a much larger computer to ascertain a property from the smaller computer. And to make assertions about the larger computer, we would need an even larger computer, and so on."
**Reason:** The passage reasons about finite automata with 2^M states and hierarchies of machines, an informal argument with no theorem stated. The formalization covers abstract programs over ℕ; the finite-memory framing sits outside it.

## Counts

| Status | Entries |
|---|---|
| CONFIRMED | 3 (C1–C3) |
| DISCONFIRMED | 2 (D1–D2) |
| CONFIRMED IN CORRECTED FORM | 4 (E1–E3, D3 recategorized 2026-11-14) |
| AMBIGUITY RESOLVED | 2 (F1–F2) |
| NOT FORMALIZED | 5 (G1–G5) |
| Total | 16 |

## Scope note

Every verdict above cites machine-checked theorems in this repository; the 2026-11-14 recalibration pass changed README wording and Lean comments only, with no theorem or proof touched, and the build below was re-run after it. The continuous-integration build fails if any proof contains `sorry`, and each file prints its axioms — `[propext, Classical.choice, Quot.sound]` — beyond which nothing is assumed. I read the paper in full (9 pages, open-access PDF, text extracted with `pdftotext`) for every quotation; the extraction normalizes spacing around subscripts and superscripts, so the quotes render `(i−, o−)` for the paper's `(i⁻, o⁻)`, `o+` for `o⁺`, `2^L` for 2 to the power L, and `J_v(i, o)` for the paper's subscripted judge symbol. Theorem labels T1, T2′, T5, T6, and T10 are the repository's own — the paper numbers none of its results; the mapping is recorded in the README.
