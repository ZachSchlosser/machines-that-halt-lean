# Alignment Undecidability — a Lean formalization

[![CI](https://github.com/ZachSchlosser/alignment-undecidability/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/ZachSchlosser/alignment-undecidability/actions/workflows/lean_action_ci.yml)

**The first machine-checked formalization of the undecidability of
AI-alignment verification**, together with machine-checked corrections of the
source paper's overclaim.

This repository formalizes, in Lean 4 against Mathlib, the central limit
theorem of:

> de Melo, Máximo, Soma, Castro, *On the Undecidability of Artificial
> Intelligence Alignment: Machines that Halt*
> ([arXiv:2408.08995](https://arxiv.org/abs/2408.08995); published version
> Scientific Reports, 2025).

All credit for the framing — an "AI model" as a program, alignment as a
judge-approval property of its input/output behavior, and the central claim
that alignment verification is undecidable — belongs to the paper's authors.
What this repository adds is a proof they can check: every headline theorem
below compiles against current Mathlib, depends on no axioms beyond Lean's
standard three, and contains no `sorry`.

---

## What is proved

Throughout, an "AI model" is a partial recursive code `c : Nat.Partrec.Code`
and a *judge* `J : ℕ → ℕ → Bool` approves or rejects (input, output) pairs.
The paper's Definition D2 is ambiguous about whether a computation that never
produces an output counts as aligned, so **both readings are proved**:

- **(a) vacuous** — divergence is harmless: `alignedVac J c` (every output
  produced is approved);
- **(b) totality** — an aligned model must answer every input: `alignedTot J c`.

| Paper claim | Lean theorem | File |
|---|---|---|
| T2: alignment is undecidable (both readings) | `alignedVac_undecidable`, `alignedTot_undecidable` — via Rice's theorem | `Aligned.lean` |
| T2, *explicit halting reduction* (both readings, polarity-matched gadgets) | `alignedVac_halting_reduce`, `alignedTot_halting_reduce` | `Reduction.lean` |
| T2′: the paper's own gadget template, faithfully | `T2'`, `T2'_undecidable` | `Reduction.lean` |
| T1: the diagonal adversary that fools any verifier | `T1_adversary`, `T1_no_verifier_vac`, `T1_no_verifier_tot` — via Kleene's recursion theorem | `Adversary.lean` |
| T6: the masking wrapper is always aligned | `T6_masking` | `Adversary.lean` |
| **T10 / Final Remarks: refuted** — guaranteed halting does *not* make alignment decidable | `alwaysHalting_alignment_undecidable` (counterexample; not even recursively enumerable) | `Overclaim.lean` |
| T5: finite input space makes alignment decidable — restated honestly | `T5_promise` (promise semi-decision over the halting-on-domain subclass) | `Overclaim.lean` |

Two independent proof methods establish undecidability (Rice's theorem, and
explicit many-one reduction to the halting problem), and a third —
diagonalization against arbitrary verifiers — rules out verifier-based
formulations. The T1 diagonalization works for *arbitrary* computable
verifiers, without assuming extensionality.

## Corrections and improvements to the paper

Formalization forced five substantive corrections, all documented in the
source files with the corresponding paper passages:

1. **Divergence-reading ambiguity (D2).** The paper does not fix whether a
   diverging computation is aligned. Both readings are proved undecidable;
   the gadgets' polarity differs accordingly (diverge-then-misbehave vs
   behave-if-halts).
2. **Judge non-triviality quantifier (D3).** "an output `o⁺` for every input
   `i`" is ambiguous between a constant approved dummy and a per-input one.
   Both are handled — and under the paper's own (constant) usage, the main
   theorem comes out *stronger* than its Rice-based proof suggests: `T2'`
   needs no computable judge and no rejected pair.
3. **A genuine gap in T2′ closed.** The paper's reduction assumes the gadget
   construction is effective without argument. `exists_curried_code`
   (the sₙᵐ theorem in usable form) supplies the missing computability.
4. **T1 corrections.** The paper's second fooling case mislabels the
   verifier's verdict (typo), and the positive witness it invokes is never
   shown computable. Both are fixed; the witness is built by `Nat.rfind`.
5. **The overclaim refuted.** The paper closes with: *"Developing an AI model
   that always halts allows for the alignment … to be asserted
   computationally"* (and, in Implications, that halting decidability ensures
   decidability of alignment). This is false. `alwaysHalting_alignment_
   undecidable` exhibits, for every program `c` and input `n`, a *total* model
   that is aligned exactly when `c` diverges on `n`; a decider working even
   only on always-halting models would decide non-halting — contradicting
   `halting_problem_not_re` (not even semi-decidable). The true statement is
   T5's, which the paper reaches only with the additional finite-input
   hypothesis; `T5_promise` formalizes that version as a promise procedure.

Also made explicit: T6's silently assumed hypotheses (judge computable and
total, existence of an approved dummy, base model guaranteed to halt).

## What this does *not* say

- **Not** "the first formalization of Rice's theorem." The underlying
  mathematics (Rice, halting) has been in Mathlib since Carneiro's 2018
  formalization. The novelty here is the alignment wrapper and the
  corrections above.
- **Not** "alignment is impossible." The paper's own constructive escapes —
  exhaustive checking over finite inputs (T5) and output masking (T6) — are
  formalized *here*, as true theorems. Undecidability of *verification* is
  not impossibility of *construction*.
- **Not** "a practical limit on controlling AI systems." The three scope
  caveats below bound exactly what has been proved.

## Scope caveats

1. **Inner alignment only.** This is the *paper's own* stated scope: "This is
   an example of outer alignment, but it is not the focus of this work … the
   main difficulty of such a solution is the definition of the judge function
   `J_v(i,o)` in the first place." Every theorem here is judge-relative: it
   says nothing about whether any given judge is the *right* one.
2. **Deterministic models.** The formal model is a deterministic partial
   function; the paper never considers stochastic systems, and nothing here
   transfers to them.
3. **Unbounded inputs.** Undecidability holds over the full input space
   `ℕ`. With finitely many inputs and guaranteed halting, alignment *is*
   decidable (`T5_promise`) — the paper's error was dropping the finiteness.

## Why this matters

Claims about the formal limits of AI alignment circulate widely but are
rarely checked. This repository turns one such claim into an artifact anyone
can verify with one command, and in doing so locates the boundary precisely:

- *verification* of arbitrary systems is impossible — in the strongest sense
  available (not decidable, not even semi-decidable, and immune to
  guaranteed halting);
- *construction* of aligned systems is easy (T6);
- the dividing line is the input space (unbounded vs finite).

The sharpened honest message: **even in the most favorable formal setting —
deterministic programs, a judge handed to us for free — post-hoc alignment
verification of arbitrary systems is impossible, and guaranteed halting
provably does not escape it.**

The exercise is also a case study in formalization as peer review: a
peer-reviewed paper's central limit theorem required five corrections — an
ambiguous definition, an ambiguous quantifier, a proof gap, a typo with
mathematical content, and a false closing claim — before it could be proved
at all.

## How to verify

```
git clone https://github.com/ZachSchlosser/alignment-undecidability
cd alignment-undecidability
lake exe cache get   # fetch prebuilt Mathlib artifacts (~minutes)
lake build
```

You should see `Build completed successfully` and, for every headline
theorem, a line of the form

```
'AlignmentUndecidability.alignedTot_undecidable' depends on axioms:
  [propext, Classical.choice, Quot.sound]
```

Those three are Lean's built-in foundational axioms — anything beyond them
(including `sorry`) would appear here. The CI additionally fails if the string
`sorry` occurs anywhere, so a green check on any commit means: compiles clean
and no proof holes. In an editor with the Lean toolchain, every theorem above
can be inspected interactively.

## Not formalized, and why

T3 (enumerable axiomatic-aligned set — "property-preserving operations"
undefined, and preservation fails for plain composition), T4 (D-ANNs always
halt — needs a cost model), T7–T9 (design-argument constructions, informal),
and the utility-penalty / finite-computer hierarchy passages (not mathematical
claims as stated). See `Aligned.lean`'s header and the scoping notes for the
per-claim analysis.

## Credits and license

Formalization: Zach Schlosser, with Claude (Anthropic). All results
formalize and correct the paper of de Melo, Máximo, Soma, Castro
([arXiv:2408.08995](https://arxiv.org/abs/2408.08995)); the framing and the
central claim are theirs. Released under Apache 2.0.
