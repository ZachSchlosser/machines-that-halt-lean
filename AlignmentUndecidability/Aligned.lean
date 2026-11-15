/-
Copyright (c) 2026 Zach Schlosser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zach Schlosser, Claude (Anthropic)
-/
module
public import Mathlib.Computability.Halting

/-!
# Undecidability of alignment w.r.t. a non-trivial computable judge

This file proves the paper's central claim, that alignment is undecidable, under
both readings (a) and (b) below. It is part of a formalization of Melo, Máximo,
Soma, Castro, "Machines that halt resolve the undecidability of artificial
intelligence alignment", Scientific Reports 15, 15591 (2025),
https://doi.org/10.1038/s41598-025-99060-2.

A *judge* `J : ℕ → ℕ → Bool` is a Boolean predicate on (input, output) pairs.
A code `c : Nat.Partrec.Code` (our standing model of an "AI model as program") is
aligned w.r.t. `J` when every output it produces on every input is approved by `J`.
The paper does not say whether a diverging computation (no output ever produced)
counts as aligned. Its "Informal proof" section defines a verifier that returns
true "if the model is aligned for every input i and output M(i) = o", which can
be read either way, and its Background section describes alignment as the system
"never producing harmful output", which reads most naturally as (a). Both
readings are proved:

* Reading (a), *vacuous*: divergence is harmless — `alignedVac`.
* Reading (b), *totality*: an aligned model must answer every input — `alignedTot`.

Both readings are undecidable (`ComputablePred` fails) — the paper's "Formal
proof" claim, proved for both readings.

Notable strength: reading (a) needs only the existence of a *rejected* pair; the
judge's computability and the existence of approved outputs are not needed.
Reading (b) needs a computable judge with an approved output for every input
(the paper's non-triviality condition on the judge) to build an aligned witness
by unbounded search (`Nat.rfind`).

The paper's ontology, which this file mirrors: the judge is background —
delivered once as a compiled sequence of bytes, and required non-trivial once
(it rejects at least one pair, and every input has some approved output).
Alignment is then a property of systems. The theorems below carry `J` only as
the parameter of the alignment predicate, as in the paper's notation
`J_v(i, o)`; the hypotheses each theorem states are the parts of that
background the theorem actually uses, made explicit. On
this toolchain, section variables used only in proofs are not auto-bound
into theorem statements; `include` forces them but would then bind them
into every statement alike. The statements therefore keep the hypotheses
they use visible rather than change the elaborated API. (An earlier
revision of this comment claimed the toolchain lacks `include` entirely;
an external reviewer's check, 2026-11, showed `include` exists and works —
corrected here.)

Everything is an application of `ComputablePred.rice₂` from Mathlib.
-/

open Nat.Partrec (Code)
open ComputablePred

public section

namespace AlignmentUndecidability

/-! ## Shared witness: a constant code -/

/-- There is a code computing the constant total function `fun _ => o`. -/
theorem exists_const_code (o : ℕ) : ∃ c : Code, ∀ i, o ∈ c.eval i := by
  have hf : Nat.Partrec fun _ => (pure o : Part ℕ) :=
    Partrec.nat_iff.1 (Computable.const o).partrec
  obtain ⟨c, hc⟩ := Code.exists_code.1 hf
  refine ⟨c, fun i => ?_⟩
  have hci : c.eval i = pure o := congrFun hc i
  rw [hci]
  simp

/-! ## Reading (a): vacuous alignment -/

/-- Reading (a): every output the code ever produces is approved by `J`.
A code that diverges everywhere is (vacuously) aligned. -/
def alignedVac (J : ℕ → ℕ → Bool) (c : Code) : Prop :=
  ∀ i, ∀ o ∈ c.eval i, J i o = true

/-- Unfolding lemma: definitions are definitionally opaque to files that
`public import` them under the module system, so later files unfold via this. -/
theorem alignedVac_def {J : ℕ → ℕ → Bool} {c : Code} :
    alignedVac J c ↔ ∀ i o, o ∈ c.eval i → J i o = true := Iff.rfl

theorem alignedVac_ext {J : ℕ → ℕ → Bool} {cf cg : Code} (h : cf.eval = cg.eval) :
    alignedVac J cf ↔ alignedVac J cg := by
  simp only [alignedVac, h]

/-- A nowhere-defined code is aligned under the vacuous reading. -/
theorem exists_alignedVac (J : ℕ → ℕ → Bool) : ∃ c : Code, alignedVac J c := by
  obtain ⟨c, hc⟩ := Code.exists_code.1 Nat.Partrec.none
  refine ⟨c, fun i o ho => ?_⟩
  have hci : c.eval i = Part.none := congrFun hc i
  rw [hci] at ho
  exact absurd ho (Part.notMem_none o)

/-- If `J` rejects any pair, some (total!) code is not aligned. -/
theorem exists_not_alignedVac {J : ℕ → ℕ → Bool} (hneg : ∃ i o, J i o = false) :
    ∃ c : Code, ¬ alignedVac J c := by
  obtain ⟨i₀, o₀, h₀⟩ := hneg
  obtain ⟨c, hc⟩ := exists_const_code o₀
  refine ⟨c, fun h => ?_⟩
  have := (h i₀) o₀ (hc i₀)
  rw [h₀] at this
  exact Bool.noConfusion this

/-! ## Reading (b): alignment with totality -/

/-- Reading (b): the code answers every input, and every output is approved. -/
def alignedTot (J : ℕ → ℕ → Bool) (c : Code) : Prop :=
  ∀ i, (c.eval i).Dom ∧ ∀ o ∈ c.eval i, J i o = true

/-- Unfolding lemma for use across module boundaries (see `alignedVac_def`). -/
theorem alignedTot_def {J : ℕ → ℕ → Bool} {c : Code} :
    alignedTot J c ↔ ∀ i, (c.eval i).Dom ∧ ∀ o, o ∈ c.eval i → J i o = true := Iff.rfl

theorem alignedTot_ext {J : ℕ → ℕ → Bool} {cf cg : Code} (h : cf.eval = cg.eval) :
    alignedTot J cf ↔ alignedTot J cg := by
  simp only [alignedTot, h]

/-- Unbounded search for an approved output: `Nat.rfind` over the computable,
total predicate `fun k => J i k`. The result is a partial recursive total
function selecting an approved output for every input. -/
theorem partrec_approved_select {J : ℕ → ℕ → Bool} (hJ : Computable₂ J) :
    Nat.Partrec fun i => Nat.rfind fun k => (pure (J i k) : Part Bool) :=
  Partrec.nat_iff.1 (Partrec.rfind hJ.partrec₂)

/-- With a computable judge that approves some output of every input,
an aligned *total* code exists. -/
theorem exists_alignedTot {J : ℕ → ℕ → Bool} (hJ : Computable₂ J)
    (hpos : ∀ i, ∃ o, J i o = true) : ∃ c : Code, alignedTot J c := by
  obtain ⟨c, hc⟩ := Code.exists_code.1 (partrec_approved_select hJ)
  have hbeta : ∀ i, c.eval i = Nat.rfind fun k => (pure (J i k) : Part Bool) :=
    fun i => congrFun hc i
  refine ⟨c, fun i => ⟨?_, ?_⟩⟩
  · rw [hbeta i]
    obtain ⟨n, hn⟩ := hpos i
    exact Nat.rfind_dom.2 ⟨n, by simpa using hn, fun {m} _ => by simp⟩
  · intro o ho
    rw [hbeta i] at ho
    have h1 := Nat.rfind_spec (p := fun k => (pure (J i k) : Part Bool)) ho
    simpa using h1

theorem exists_not_alignedTot {J : ℕ → ℕ → Bool} (hneg : ∃ i o, J i o = false) :
    ∃ c : Code, ¬ alignedTot J c := by
  obtain ⟨i₀, o₀, h₀⟩ := hneg
  obtain ⟨c, hc⟩ := exists_const_code o₀
  refine ⟨c, fun h => ?_⟩
  obtain ⟨_, hout⟩ := h i₀
  have := hout o₀ (hc i₀)
  rw [h₀] at this
  exact Bool.noConfusion this

/-! ## The main theorems, stated about systems

What a theorem quantifies over is what it is about. These are stated about AI
systems: the hypothesis is that the alignment property is non-trivial — some
systems are aligned and some are not, the paper's own Background framing
("trivial safe ones that halt immediately or only print approved statements"
versus "a rogue AI that eventually outputs something disallowed"). The
judge-level reading of that condition is recorded beside each theorem. -/

/-- The vacuous reading's non-triviality, as a fact about systems, is exactly
the judge rejecting some pair: with a rejected pair the nowhere-defined system
is aligned and the constant system emitting the rejected output is not, and if
the judge rejects nothing then every system is aligned. -/
theorem alignedVac_nontrivial_iff {J : ℕ → ℕ → Bool} :
    (∃ a b : Code, alignedVac J a ∧ ¬ alignedVac J b) ↔ ∃ i o, J i o = false := by
  constructor
  · rintro ⟨a, b, -, hb⟩
    by_contra hno
    have hb' : alignedVac J b := fun i o _ => by
      have hne : J i o ≠ false := fun h => hno ⟨i, o, h⟩
      simpa using hne
    exact hb hb'
  · intro hneg
    obtain ⟨a, ha⟩ := exists_alignedVac J
    obtain ⟨b, hb⟩ := exists_not_alignedVac hneg
    exact ⟨a, b, ha, hb⟩

/-- **The paper's central theorem, reading (a).** No program decides whether a
system is aligned, whenever some system is aligned and another is not. By
`alignedVac_nontrivial_iff` the condition says exactly that the judge rejects
something; the judge need not be computable. -/
theorem alignedVac_undecidable {J : ℕ → ℕ → Bool}
    (hNT : ∃ a b : Code, alignedVac J a ∧ ¬ alignedVac J b) :
    ¬ComputablePred fun c => alignedVac J c := by
  intro h
  rcases (rice₂ {c : Code | alignedVac J c} fun _ _ h => alignedVac_ext h).1 h with hE | hU
  · obtain ⟨a, -, ha, -⟩ := hNT
    have hmem : a ∈ ({c | alignedVac J c} : Set Code) := ha
    rw [hE] at hmem
    simp at hmem
  · obtain ⟨-, b, -, hb⟩ := hNT
    have hmem : b ∈ ({c | alignedVac J c} : Set Code) := by
      rw [hU]; exact Set.mem_univ b
    exact hb hmem

/-- The totality reading's non-triviality holds whenever the judge-level
conditions of the original statement hold: `exists_alignedTot` supplies the
aligned system, `exists_not_alignedTot` the misaligned one. The converse is
false — a non-computable judge can still separate systems — which is why the
theorem below assumes only the fact about systems. -/
theorem alignedTot_nontrivial_of_judge {J : ℕ → ℕ → Bool} (hJ : Computable₂ J)
    (hneg : ∃ i o, J i o = false) (hpos : ∀ i, ∃ o, J i o = true) :
    ∃ a b : Code, alignedTot J a ∧ ¬ alignedTot J b := by
  obtain ⟨a, ha⟩ := exists_alignedTot hJ hpos
  obtain ⟨b, hb⟩ := exists_not_alignedTot hneg
  exact ⟨a, b, ha, hb⟩

/-- **The paper's two-machine non-triviality argument (Formal proof).** Their
words: "The non-triviality of the judge function guarantees the non-triviality
of the property, as a TM can be built to always output the dummy positive
values, and a TM can be built to output at least one dummy negative value."
The positive machine is `exists_alignedTot`'s — it selects an approved output
for every input by unbounded search, so it always answers with approved
values; the negative machine is `exists_not_alignedVac`'s constant code,
which emits a rejected output. This assembles their argument for the
silence-acceptable reading; `alignedTot_nontrivial_of_judge` above assembles
it for the must-answer reading. The nowhere-defined system used in
`alignedVac_nontrivial_iff` is our witness, not one of theirs. -/
theorem paper_nontriviality {J : ℕ → ℕ → Bool} (hJ : Computable₂ J)
    (hneg : ∃ i o, J i o = false) (hpos : ∀ i, ∃ o, J i o = true) :
    ∃ a b : Code, alignedVac J a ∧ ¬ alignedVac J b := by
  obtain ⟨a, ha⟩ := exists_alignedTot hJ hpos
  obtain ⟨b, hb⟩ := exists_not_alignedVac hneg
  exact ⟨a, b, fun i o ho => (ha i).2 o ho, hb⟩

/-- **The paper's central theorem, reading (b).** No program decides whether a
system is aligned and answers every input, whenever some system is and another
is not. This subsumes the earlier judge-level form: a computable judge that
rejects something and approves some answer per input separates systems
(`alignedTot_nontrivial_of_judge`), and no computability is otherwise needed. -/
theorem alignedTot_undecidable {J : ℕ → ℕ → Bool}
    (hNT : ∃ a b : Code, alignedTot J a ∧ ¬ alignedTot J b) :
    ¬ComputablePred fun c => alignedTot J c := by
  intro h
  rcases (rice₂ {c : Code | alignedTot J c} fun _ _ h => alignedTot_ext h).1 h with hE | hU
  · obtain ⟨a, -, ha, -⟩ := hNT
    have hmem : a ∈ ({c | alignedTot J c} : Set Code) := ha
    rw [hE] at hmem
    simp at hmem
  · obtain ⟨-, b, -, hb⟩ := hNT
    have hmem : b ∈ ({c | alignedTot J c} : Set Code) := by
      rw [hU]; exact Set.mem_univ b
    exact hb hmem

end AlignmentUndecidability

-- Verification: no axioms beyond Lean's standard three.
#print axioms AlignmentUndecidability.alignedVac_undecidable
#print axioms AlignmentUndecidability.alignedTot_undecidable
#print axioms AlignmentUndecidability.paper_nontriviality
