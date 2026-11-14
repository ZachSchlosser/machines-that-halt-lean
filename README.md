# A Lean formalization of *Machines that halt resolve the undecidability of artificial intelligence alignment*

[![CI](https://github.com/ZachSchlosser/machines-that-halt-lean/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/ZachSchlosser/machines-that-halt-lean/actions/workflows/lean_action_ci.yml)

This repository machine-checks, in Lean 4 with Mathlib, the paper's central
result — **no algorithm can verify whether an arbitrary AI model is aligned** —
together with its arguments and its constructions for provably aligning models
that are guaranteed to halt, and makes the hypotheses and readings behind each
claim explicit in the theorem statements. To our knowledge (based on a
literature search in October 2026), it is the first formal verification of the
undecidability of AI-alignment.

Both results come from formalizing one paper:

> Gabriel A. Melo, Marcos R. O. A. Máximo, Nei Y. Soma, Paulo A. L. Castro.
> *Machines that halt resolve the undecidability of artificial intelligence
> alignment.* Scientific Reports 15, 15591 (2025).
> [doi:10.1038/s41598-025-99060-2](https://doi.org/10.1038/s41598-025-99060-2)
> (open access).

The framing — an AI model as a program, alignment as a judge's approval of its
input/output behavior, and the claim that checking alignment is undecidable —
is the authors'. This repository verifies their central theorem, their
informal arguments, and their constructions for provably aligned
always-halting systems, and makes each claim's hypotheses and readings
explicit.

## In brief

- **Checking alignment is impossible in general.** No algorithm can take an
  arbitrary program and decide whether every output it produces is approved
  by a given judge. We prove this three independent ways.
- **Checking always-halting systems is also undecidable in general.** No
  algorithm takes an arbitrary always-halting program and decides whether it
  is aligned — a standard computability fact, machine-checked here in the
  alignment setting. The paper's provability program is per-system —
  construction, masking, and exhaustive checking over the fixed-size inputs
  its examples design in — and that program is consistent with this boundary.
- **Building aligned systems is easy.** Wrapping any model so that
  disapproved outputs are replaced by an approved fallback yields a system
  that is aligned by construction. What is impossible is certifying an
  *arbitrary* system after the fact.

## The setting

A *model* is a program `c : Nat.Partrec.Code` — Mathlib's standard model of
computable partial functions on natural numbers, equivalent in power to Turing
machines. A *judge* `J : ℕ → ℕ → Bool` approves or rejects each
(input, output) pair.

The paper does not say whether a model that never answers some input counts
as aligned, so we prove everything for both readings. (Its Background section
describes alignment as the system "never producing harmful output," which
reads most naturally as the vacuous reading; its definition in the "Informal
proof" section, "aligned for every input i and output M(i) = o," fits either.)
For the systems the paper itself proposes — architectures guaranteed to halt
by construction — the model answers every input, so the two readings coincide
there; the ambiguity concerns the theorem's stated domain of arbitrary
programs.

- **Vacuous reading** (`alignedVac J c`): every output the model produces is
  approved. A model that never answers is trivially aligned.
- **Totality reading** (`alignedTot J c`): the model answers every input, and
  every answer is approved.

The two readings differ in an important way. Under the vacuous reading,
non-triviality of the alignment property is exactly the judge rejecting
*something* — the judge does real work. Under the totality reading, the
property stays non-trivial even for a judge that approves every output,
because then "aligned" just means "halts on every input," which itself
separates systems. Results stated for the vacuous reading are therefore the
ones that say something about judges specifically.

## What is proved

The paper numbers none of its results. The labels in the theorem names are
ours: **T1** is the self-referential adversary argument ("Informal proof"),
**T2** the reduction to the halting problem ("Formal proof"; **T2′** is its
proof template), **T5** the exhaustive check over finitely many inputs ("A
special decidable case"), **T6** the output-masking construction (same
section), and **T10** the claim that decidable halting makes alignment
decidable ("Implications").

| Claim | Lean theorem(s) | File |
|---|---|---|
| Alignment is undecidable under both readings (via Rice's theorem) | `alignedVac_undecidable`, `alignedTot_undecidable` | `Aligned.lean` |
| The same, by explicit reduction from the halting problem | `alignedVac_halting_reduce`, `alignedTot_halting_reduce`, `alignedVac_undecidable_by_reduction`, `alignedTot_undecidable_by_reduction` | `Reduction.lean` |
| The paper's own proof template (its "Formal Proof" section), formalized as written | `T2'`, `T2'_undecidable` | `Reduction.lean` |
| Every computable verifier is fooled by some program that asks the verifier about itself (the paper's "Informal proof") | `T1_adversary`, `T1_no_verifier_vac`, `T1_no_verifier_tot` | `Adversary.lean` |
| The paper's adversary with its base model — follows the initial model away from the fooling input (the paper's "would behave as the initial model M for most of its inputs") | `T1_adversary_param` | `Adversary.lean` |
| Masking disapproved outputs yields an aligned system | `T6_masking` | `Adversary.lean` |
| Altering outputs yields a misaligned system, for every base model guaranteed to halt (the paper's "same procedure… proven misaligned model") | `T6_misaligning` | `Adversary.lean` |
| The paper's two machines — the always-approved searcher and the constant rejected output — establish non-triviality | `paper_nontriviality`, `alignedTot_nontrivial_of_judge` | `Aligned.lean` |
| No single checker decides alignment for every always-halting program | `alwaysHalting_alignment_undecidable` | `Overclaim.lean` |
| With finitely many inputs, exhaustive checking decides alignment for models that halt on them | `T5_promise` | `Overclaim.lean` |

The two undecidability theorems are stated about systems, not judges: their
hypothesis is that the alignment property is non-trivial — some system is
aligned and another is not, the paper's own Background framing. For the
vacuous reading that condition is exactly the judge rejecting something
(`alignedVac_nontrivial_iff` proves the equivalence); for the totality
reading it holds whenever the judge-level conditions hold
(`alignedTot_nontrivial_of_judge`), and no computability is otherwise
needed. The construction theorems keep their judge-level hypotheses, since
the constructions run the judge: the adversary results need a computable
judge that rejects something and approves some answer on every input, the
masking wrapper a computable judge with an approved fallback per input,
`T5_promise` a computable judge, and `T2'` only a single output approved on
every input — not even a computable judge.

## What formalizing the paper turned up

The core result holds: alignment verification is undecidable under either
reading of the definition. The paper's provability program — per-system
construction, masking, and the finite-input check — survives formalization
intact. The remaining arguments needed hypotheses or details the paper
leaves implicit; the formalization supplies them.

1. **The definition of alignment is ambiguous, and the paper's proof template
   only works for one reading.** The template — simulate `M` and "compute a
   partial function without property P" if `M` does not halt — is the standard
   Rice reduction schema and is correct as a schema; the reading-dependence
   comes from the alignment instantiation. Under the vacuous reading, a
   program that never halts produces no outputs and is therefore *aligned* —
   the opposite of what the template needs. The template works as written for
   the totality reading (`T2'`); the vacuous reading needs the construction
   reversed, so that the program misbehaves only *after* the simulation halts
   (`alignedVac_halting_reduce`).
2. **The non-triviality condition is ambiguous.** "At least one output `o⁺`
   for every input `i` for which the judge returns 1" can mean one output
   approved everywhere, or a possibly different approved output for each
   input. The paper's own usage ("a dummy output `o⁺` that the judge
   approves") suggests the first; we handle both.
3. **The informal adversary argument leaves a step implicit.** Under the
   per-input reading of (2), the adversary must *compute* an approved output
   for each input, which the paper does not address; we do it by unbounded
   search (`Nat.rfind`). The self-reference the argument relies on is
   Kleene's recursion theorem, which Mathlib provides.
4. **What the halting sentences establish, and where the boundary lies.** The
   paper states that
   "Ensuring the decidability of the halting property of autonomous systems
   also ensures the decidability of other non-trivial properties of such
   systems, especially their alignment," and that "Developing an AI
   model that always halts allows for the alignment and other properties of
   the AI model to be asserted computationally." Its provability program
   establishes alignment per system: the enumerable set of architecturally
   aligned AIs, the masking wrapper ("This proves that the resulting AI
   system will always be aligned"), and the exhaustive check over the
   fixed-size inputs its running example designs in — `T6_masking` and
   `T5_promise` machine-check the latter two. The class-level reading meets a
   standard computability boundary, machine-checked here
   (`alwaysHalting_alignment_undecidable`): no computable function decides
   alignment over the class of all always-halting programs on unbounded
   inputs. The proof device is a bounded simulation — for any program `c` and
   input `n`, an always-halting program `T` that, on input `k`,
   outputs 1 if `c` halts on `n` within `k` steps and 0 otherwise. With a
   judge that approves exactly the output 0, `T` is aligned exactly when `c`
   never halts on `n`, so a checker of that kind would solve the halting
   problem. The same argument rules out even a
   procedure that only confirms alignment when it holds, since non-halting is
   not recursively enumerable; this stronger form is not stated as a separate
   theorem. The paper also proposes enforcing a time bound
   through a utility penalty (its Eq. 1–3, whose "dominance condition" asks for
   a time `T` after which the cost exceeds any reward) and says this makes
   alignment verification tractable. As we read it, that is a bound on running
   time that does not depend on the input, a stronger condition than halting
   on every input. The counterexample does not apply to it (its running time
   grows with the input), and since the proposal is stated informally, without
   a model of the agent, we have not formalized it.
5. **The finite-input result, stated as a promise.** The paper's
   exhaustive check ("we could check every possible combination … Thus, the
   alignment becomes decidable, though intractable") runs the model on every
   input, so it finishes only if the model halts on all of them — an
   assumption the paper's networks, guaranteed to halt, already satisfy, so
   its wording is accurate in its class. `T5_promise` makes the assumption
   explicit: a procedure that, for any model halting on the finitely many
   inputs, halts and correctly reports whether the model is aligned on them.
6. **The masking construction's hypotheses are gathered, not new.** The
   guarantee needs a computable judge and an approved fallback output for
   every input, and the wrapped model answers every input when the base model
   does. The paper states each ingredient elsewhere — the judge arrives as
   compiled bytes, the non-triviality condition supplies the fallback, and
   the construction's stated scope is models guaranteed to halt — and
   `T6_masking` gathers all three as explicit conditions of the guarantee.

Details that informal proofs normally leave implicit are also proved — for
example, that the program transformations used in the reductions are
themselves computable (`exists_curried_code`, from Mathlib's sₙᵐ theorem).

## What this does not show

- **It is not the first formalization of Rice's theorem or the halting
  problem.** Those have been in Mathlib since Mario Carneiro's 2018
  formalization, and this work builds on them. What is new is the alignment
  statements and the formalized versions of the paper's arguments and
  constructions; the boundary theorems state standard computability facts in
  this setting.
- **It does not show that alignment is impossible.** The paper's
  constructive results — exhaustive checking over finite inputs and output
  masking — are proved here as true theorems. The impossibility concerns
  *verifying* arbitrary systems, not *building* aligned ones.
- **It does not show that misalignment cannot be detected.** Searching for an
  input on which a model produces a disapproved output will find one whenever
  one exists (a standard fact, not formalized here). What cannot be done in
  general is to certify that no such input exists.
- **It does not establish a practical limit on controlling AI systems.** The
  scope limits below say exactly what is covered.

## Scope

1. **Inner alignment only.** Every result is relative to a given judge and
   says nothing about whether the judge captures what we actually want. This
   is the paper's own stated scope: it sets outer alignment aside ("it is not
   the focus of this work") and notes that "the main difficulty of such a
   solution is the definition of the judge function `J_v(i, o)` in the first
   place, the outer alignment."
2. **Deterministic models.** A model here is a deterministic partial
   function. The paper does not address stochastic systems, and nothing here
   transfers to them automatically.
3. **Unbounded inputs.** Undecidability is over the full input space `ℕ`.
   With finitely many inputs, alignment of models that halt on them is
   decidable (`T5_promise`).
4. **Abstract programs.** Models are Mathlib's codes for computable
   functions, not literal Turing machines or compiled binaries. The two are
   equivalent in what they can compute, and the paper itself reasons at this
   level.

## Why this matters

Claims about the formal limits of AI alignment are widely cited and rarely
checked. This repository turns one of them into something anyone can verify
with a single command, and it puts every assumption in a theorem statement:
the judge conditions, the two readings of alignment, and the input-space
bounds under which each guarantee holds — certifying arbitrary systems is
impossible, no single checker covers the always-halting programs, finite
input spaces allow exhaustive checking, and building aligned systems by
construction remains possible.

The resulting message is narrower than "alignment is impossible": **even in
the most favorable formal setting — deterministic programs, and a judge
handed to us for free — post-hoc alignment verification of arbitrary systems
is impossible, no single checker covers the always-halting programs, and
provability comes per system, by construction.**

It is also an example of formalization as peer review. Writing the proofs
down for a proof checker made the paper's definitions precise enough to
check, confirmed its central theorem and its constructions, and made each
guarantee's conditions explicit.

## How to check it yourself

With the Lean toolchain installed
([instructions](https://leanprover-community.github.io/get_started.html)):

```bash
git clone https://github.com/ZachSchlosser/machines-that-halt-lean
cd machines-that-halt-lean
lake exe cache get   # download prebuilt Mathlib (a few minutes)
lake build
```

The build should end with `Build completed successfully`. For each headline
theorem it also prints the axioms the proof depends on, for example:

```
'AlignmentUndecidability.alignedTot_undecidable' depends on axioms:
  [propext, Classical.choice, Quot.sound]
```

These three are Lean's standard foundational axioms. A proof with a gap
(`sorry`) or an added assumption would show it in this list. The build also
prints the Mathlib theorems the project relies on (from `Basic.lean`), for
reference.

CI rebuilds the project on every push and fails if the word `sorry` appears in
any source file, so a green check on a commit means the proofs compile and
are complete. The project is pinned to Lean and Mathlib `v4.36.0-rc1`.

## Files

| File | Contents |
|---|---|
| `AlignmentUndecidability/Basic.lean` | Checks that the Mathlib results used are available |
| `AlignmentUndecidability/Aligned.lean` | Definitions of both readings; undecidability via Rice's theorem |
| `AlignmentUndecidability/Reduction.lean` | Computability of program transformations; explicit reductions; the paper's proof template |
| `AlignmentUndecidability/Overclaim.lean` | Boundary for the always-halting class; the finite-input result |
| `AlignmentUndecidability/Adversary.lean` | The self-referential adversary (with and without its base model); the masking wrapper and its misaligning dual |
| `ARGUMENT-MAP.md` | The paper's arguments step by step, each mapped to the Lean that verifies it, with verbatim quotes |

Each file opens with a description of what it proves and which passages of the
paper it corresponds to.

## Not formalized

- **The enumerable set of aligned systems** built from aligned "axiom"
  operations: the paper never defines which operations preserve alignment.
- **Feed-forward networks always halt:** requires a model of neural networks
  and their computation cost, which Mathlib does not have.
- **The remaining design discussions** — making a halting model deliberately
  misaligned, loops breaking guarantees, absorbing final states — and the
  passages on utility penalties and finite-computer hierarchies, which are
  informal arguments rather than mathematical claims.

## Credits

Formalization by Zach Schlosser, with GLM-5.3 and Claude (Anthropic). The
framing and the central claim belong to the paper's authors. Quotations are
from the Scientific Reports article. Released under Apache 2.0.
