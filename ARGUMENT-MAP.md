# Argument map — from the paper's arguments to the Lean that verifies them

This file maps each argument of Melo, Máximo, Soma, and Castro, "Machines that
halt resolve the undecidability of artificial intelligence alignment,"
Scientific Reports 15, 15591 (2025), to the Lean that verifies it, step by
step. Claim-level verdicts for every checkable statement live in
`CLAIMS-VERIFIED-2026-11-14.md`; this file goes one level deeper and follows
the arguments as the paper gives them. The intended readers are the paper's
authors and anyone checking whether this verification did a good job: every
statement about the paper carries a verbatim quote, and every mapping names
the theorem and its file and line at this commit.

Conventions. Quotes are verbatim from the article. Items marked **OURS** are
this project's design choices — added readings, hypotheses, or constructions —
and are never corrections of the paper. The undecidability theorems are stated
about AI systems, with the judge's conditions as background (`Aligned.lean`,
"stated about systems"); each theorem's exact hypotheses sit in its statement,
which is the display we intend a reader to check.

## 1. The Informal proof: the verifier thought experiment

The paper supposes a verifier and destroys the supposition with an adversary.
Step by step, with the mapping:

**Step 1 — the verifier hypothesis.** "Suppose we have a verifier V that takes
the sequence of bytes B_M that defines the compiled code of an arbitrary AI
model and the same for B_Jv, the alignment judge, and returns either True
(byte 1) if the model is aligned for every input i and output M (i) = o
(aligned), or it returns False (byte 0) (misaligned)."
Mapped: the verifier is `V : Code → Bool` with `Computable V`, and the judge
is `J : ℕ → ℕ → Bool` with its conditions (`Computable₂ J`, a rejected pair,
an approved answer per input) — the hypotheses of `T1_adversary`
(`Adversary.lean:100`).

**Step 2 — the adversary with its base model.** The adversary "would behave as
the initial model M for most of its inputs and outputs, but it would have the
knowledge of the verifier by executing its bytes B_V on the bytes of the judge
B_Jv and its own bytes B_M′."
Mapped: `T1_adversary_param` (`Adversary.lean:251`). Given a base model `m`,
the constructed code follows `m` at every input other than the designated one
when the verifier says aligned, and is aligned at every input when the
verifier says misaligned. The behavior's acceptance predicate
(`advParamPred`, `Adversary.lean:185`) branches on the verifier's verdict
about the code itself and searches a witness carrying `(fuel, value)`: the
fuel bounds a step-indexed simulation of the base model, so the search
reproduces the base model's answers where it mimics and diverges where the
base model diverges. `T1_adversary` (`Adversary.lean:100`) is the same fooling
structure built from the verifier and the judge alone, which is the form the
paper's contradiction needs.

**Step 3 — the two fooling cases.** "There would be at least one input i, if
the verifier V had evaluated the bytes B_M′ of the model to be aligned, for
which M′ would return a misaligned output o−, thus fooling the verifier. The
complementary fooling example can also be constructed: if the verifier had
evaluated the bytes B_M′ of the model to be misaligned, M′ would return an
aligned output o+."
Mapped: the two disjuncts of `T1_adversary` and `T1_adversary_param` —
`(V c = true ∧ ¬ alignedVac J c)` and `(V c = false ∧ alignedTot J c)`. The
search inside the behavior supplies the approved output the second case
returns, which is the step the paper's text leaves to the reader (finding an
approved output is an unbounded search and needs the judge to be a program).

**Step 4 — self-generation.** "While some may question how the model M′ could
be compiled to a sequence of bytes B_M′ that can generate itself, it is a
procedure that can be applied to any program, similar to a quine. This has
been formally demonstrated in Turing's Proof for the Halting Problem."
Mapped: Kleene's recursion theorem, which Mathlib provides as
`Nat.Partrec.Code.fixed_point₂`; both adversary theorems obtain their code
from it.

**Step 5 — the conclusion.** "Thus, the only resolution to this apparent
contradiction is the non-computability of the verifier V itself."
Mapped: `T1_no_verifier_vac` and `T1_no_verifier_tot`
(`Adversary.lean:147,159`) — no computable verifier decides alignment, under
either reading of "aligned."

## 2. The Formal proof

**The Rice restatement.** "The formal proof could simply be reduced to a
restatement of Rice's Theorem, given the equivalence of an AI model to its
Turing Machine."
Mapped: `alignedVac_undecidable` and `alignedTot_undecidable`
(`Aligned.lean:186,235`) apply Mathlib's `rice₂`. Both are stated with the
hypothesis that some systems are aligned and some are not — the paper's own
Background framing ("some programs (e.g., trivial safe ones that halt
immediately or only print approved statements) satisfy it, while others (e.g.,
a rogue AI that eventually outputs something disallowed) do not").

**The language-property claim.** "The property as defined by the acceptance of
the output given the input by a judge function is a property of the language
of the TM, as for any two TMs that accept the same language, either both
satisfice the judge function or neither."
Mapped: `alignedVac_ext` and `alignedTot_ext` (`Aligned.lean:86,118`) —
codes with equal evaluation have equal alignment; this extensionality is what
lets `rice₂` apply.

**The two-machine non-triviality argument.** "The non-triviality of the judge
function guarantees the non-triviality of the property, as a TM can be built
to always output the dummy positive values, and a TM can be built to output
at least one dummy negative value."
Mapped: `paper_nontriviality` (`Aligned.lean:223`) assembles exactly this
argument for the silence-acceptable reading — the positive machine is
`exists_alignedTot`'s (`Aligned.lean:131`), which selects an approved output
for every input by unbounded search and so always answers with approved
values; the negative machine is `exists_not_alignedVac`'s
(`Aligned.lean:99`), the constant code emitting a rejected output.
`alignedTot_nontrivial_of_judge` (`Aligned.lean:205`) assembles the same
argument for the must-answer reading. **OURS:** the nowhere-defined system
used in `alignedVac_nontrivial_iff` (`Aligned.lean:168`) is this project's
witness — it needs no approved-answer condition — and is not one of the
paper's two machines.

**The halting-reduction template.** "Let M be a Turing machine and i be an
input to M. We want to decide whether M halts on i. We construct a new Turing
machine M′ as follows: On input i, M′ simulates M on i. If M halts on i, then
M′ computes a partial function with property P. If M does not halt on i, then
M′ computes a partial function without property P." Then M_P decides halting,
"which is a contradiction. Therefore, there is no Turing machine that decides
P."
Mapped: `T2'` and `T2'_undecidable` (`Reduction.lean:308,319`) formalize the
template as written: the constructed machine computes the constant approved
function when the simulation halts and diverges otherwise, so a decider for
the property decides halting. Reading note, stated neutrally: the template as
printed carries the reading in which a system must answer to count as
aligned; under the reading in which silence is acceptable, a program that
never halts produces no outputs and so is aligned, and the construction runs
in reverse — **OURS:** `alignedVac_halting_reduce` (`Reduction.lean:146`)
supplies that reversed gadget, and `alignedVac_undecidable_by_reduction` /
`alignedTot_undecidable_by_reduction` (`Reduction.lean:160,242`) carry the
explicit reductions for both readings.

## 3. A special decidable case

**Feed-forward networks always halt.** "These feed-forward neural networks,
and even recurrent neural networks (unrolled in time to a finite number of
steps), are always guaranteed to have a finite runtime during their
inference, in other words, they always halt."
Not formalized: Mathlib has no model of neural networks or their computation
cost. The always-halting property enters the formalization as the hypothesis
`isTotalCode` (`Overclaim.lean:54`).

**The exhaustive check.** "Given that their inputs are also fixed in size and
have a length of L bits, we could check every possible combination, which is
2^L inputs, and verify if the J_v (i, o) results in 1 for every combination.
Thus, the alignment becomes decidable, though intractable."
Mapped: `T5_promise` (`Overclaim.lean:318`). For a computable judge and a
bound on the inputs, the check is a partial recursive procedure that halts on
every model guaranteed to halt on the checked inputs and there decides
bounded alignment. The halting assumption is free for the models the paper
describes, which always halt. "Though intractable" is the paper's own
observation about cost; the theorem verifies decidability, not cost.

**The partition proposal.** "Instead of enumerating all the possible inputs, a
more tractable approach would be to enumerate all the possible partitions
(decision boundaries) of the network, with the procedure described by
Balestriero and LeCun."
Not formalized: the procedure is external to the paper and needs a model of
network geometry that Mathlib does not provide.

**The masking construction.** "A more tractable approach is that instead of
verifying, we simply mask the output of the network based on the output of
the judge function, which would also need to be run during inference. If the
judge disapproves of the output of the network, a dummy output o+ that the
judge approves is returned, otherwise, it keeps the default output computed
by the network." And: "This proves that the resulting AI system will always
be aligned. … This solution may be applied to any model M that is guaranteed
to halt."
Mapped: `T6_masking` (`Adversary.lean:418`). The wrapper is computable in the
base model (**OURS:** its computability is stated and proved, where the paper
implies it by saying the judge "would also need to be run during inference");
the wrapped system is aligned under the silence-acceptable reading for every
base model, and aligned under the must-answer reading for every base model
guaranteed to halt — the paper's stated scope. The conditions the theorem
names — a computable judge, an approved answer per input — are the paper's
own judge requirements, gathered into one statement.

**The misalignment construction.** "While a model can be architecturally
proven aligned, the same procedure can be employed to make a proven misaligned
model. Any program that is guaranteed to halt can have its outputs altered so
that it becomes misaligned."
Mapped: `T6_misaligning` (`Adversary.lean:496`), the dual of `T6_masking`.
The wrapper runs the base model and alters its answer — the designated
input's answer becomes a rejected one — and for every base model guaranteed
to halt the wrapped system answers every input and returns the rejected
answer, so it is misaligned under both readings. The paper's
usefulness-preserving variant — "translate the desired input to an input the
model would accept, let it perform its computations, and then translate the
output back to the desired misaligned form" — is recorded here and not
formalized.

## 4. The Implications and Final-remarks sentences

"Ensuring the decidability of the halting property of autonomous systems also
ensures the decidability of other non-trivial properties of such systems,
especially their alignment. Therefore, it becomes computationally possible to
verify their properties, although not necessarily tractable." And: "Developing
an AI model that always halts allows for the alignment and other properties of
the AI model to be asserted computationally." And: "guaranteeing the
decidability of the halting problem for a class of AI systems does not
guarantee their alignment, it just guarantees that the alignment problem (and
other properties) becomes decidable."

These sentences carry two readings, and the verification maps each. Read per
system — for each model guaranteed to halt, its alignment can be established
— the sentences hold, and the constructions above are the evidence: the
exhaustive check decides alignment over the bounded inputs the paper's
examples design in (`T5_promise`), and the masking wrapper delivers an aligned
system for any guaranteed-to-halt base (`T6_masking`). Read at the level of
the whole class — one procedure deciding alignment for every always-halting
system — the sentence meets a standard fact of computability, which this
project machine-checks in the alignment setting:
`alwaysHalting_alignment_undecidable` (`Overclaim.lean:150`) shows no
computable checker is correct on every always-halting program, even for the
simplest judge, which approves a single answer and rejects the rest. **OURS:**
that theorem records the classical boundary; the paper's own per-system
program sits inside it. The unbounded-input scope matters on both sides: the
paper bounds the inputs by design in its running example, and the boundary
applies when inputs are unbounded.

## 5. What the paper promises but does not write

The axiomatic enumeration is announced four times and never constructed. The
abstract: "there is an enumerable set of provenly aligned AIs that are
constructed from a finite set of provenly aligned operations." The
introduction: "we show that starting from a finite set of base models and
operations that are proved to have the desired property, we can compose those
models and operations and construct an enumerable infinite set of AI that is
guaranteed to have the desired property," with the roadmap listing "the
construction of enumerable set" as a component of the work. The Discussions:
"This enumeration derives from an initial set of finite models and operations
that obey and preserve the property, these are called the axioms." The Final
remarks: "it is our objective to develop and utilize such a countable set of
proven aligned AIs."

The argument this promise would require — name the base models, define the
operations, prove each preserves alignment, and show the closure is
enumerable — has no counterpart anywhere in the paper: no operation is ever
defined. The verification therefore cannot check it, and this project adds
nothing in its place beyond the one operation the paper does supply with an
argument, the masking wrapper (`T6_masking`), which delivers an aligned system
for every base model and so an infinite family of provably aligned systems.

## 6. What we cannot formalize, and why

- Feed-forward and unrolled-recurrent networks always halting — needs a model
  of neural networks and their computation cost, which Mathlib does not
  provide.
- The Balestriero–LeCun partition enumeration — an external procedure over
  network geometry.
- The utility-penalty design (the paper's Eqs. 1–3, including "making
  alignment verification computationally tractable") — stated without a model
  of the agent, so there is no claim to check.
- The loops discussion, the θ-parameter and counter designs, and the
  test-time-training proposals — engineering discussions, not formal
  arguments.

Each of these is recorded in `CLAIMS-VERIFIED-2026-11-14.md` with the same
reasons, at the claim level.
