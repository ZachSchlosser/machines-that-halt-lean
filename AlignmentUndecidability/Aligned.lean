module
/-
Copyright (c) 2026 alignment-undecidability contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import Mathlib.Computability.Halting

/-!
# Undecidability of alignment w.r.t. a non-trivial computable judge

This file proves the corrected main theorem (deliverable D2, readings (a) and (b))
of the formalization of de Melo, Máximo, Soma, Castro,
"On the Undecidability of Artificial Intelligence Alignment: Machines that Halt"
(arXiv:2408.08995; Sci. Rep. 15:15591, 2025).

A *judge* `J : ℕ → ℕ → Bool` is a Boolean predicate on (input, output) pairs.
A code `c : Nat.Partrec.Code` (our standing model of an "AI model as program") is
aligned w.r.t. `J` when every output it produces on every input is approved by `J`.
The paper's Definition D2 is ambiguous about whether a diverging computation
(no output ever produced) counts as aligned, so both readings are proved:

* Reading (a), *vacuous*: divergence is harmless — `alignedVac`.
* Reading (b), *totality*: an aligned model must answer every input — `alignedTot`.

Both readings are undecidable (`ComputablePred` fails) — the paper's Theorem "T2",
corrected and proved for both readings at once.

Notable strength: reading (a) needs only the existence of a *rejected* pair; the
judge's computability and the existence of approved outputs are not needed.
Reading (b) needs a computable judge with an approved output for every input
(the paper's D1–D3 non-triviality) to build an aligned witness by unbounded
search (`Nat.rfind`).

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

/-- **Corrected main theorem, reading (a).** No program decides vacuous alignment.
Only a single rejected pair is needed; the judge need not be computable. -/
theorem alignedVac_undecidable {J : ℕ → ℕ → Bool} (hneg : ∃ i o, J i o = false) :
    ¬ComputablePred fun c => alignedVac J c := by
  intro h
  rcases (rice₂ {c : Code | alignedVac J c} fun _ _ h => alignedVac_ext h).1 h with hE | hU
  · obtain ⟨c, hc⟩ := exists_alignedVac J
    have hmem : c ∈ ({c | alignedVac J c} : Set Code) := hc
    rw [hE] at hmem
    simp at hmem
  · obtain ⟨c, hc⟩ := exists_not_alignedVac hneg
    have hmem : c ∈ ({c | alignedVac J c} : Set Code) := by
      rw [hU]; exact Set.mem_univ c
    exact hc hmem

/-! ## Reading (b): alignment with totality -/

/-- Reading (b): the code answers every input, and every output is approved. -/
def alignedTot (J : ℕ → ℕ → Bool) (c : Code) : Prop :=
  ∀ i, (c.eval i).Dom ∧ ∀ o ∈ c.eval i, J i o = true

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

/-- **Corrected main theorem, reading (b).** No program decides total alignment,
even for a judge known to be computable and to approve some output of every input. -/
theorem alignedTot_undecidable {J : ℕ → ℕ → Bool} (hJ : Computable₂ J)
    (hneg : ∃ i o, J i o = false) (hpos : ∀ i, ∃ o, J i o = true) :
    ¬ComputablePred fun c => alignedTot J c := by
  intro h
  rcases (rice₂ {c : Code | alignedTot J c} fun _ _ h => alignedTot_ext h).1 h with hE | hU
  · obtain ⟨c, hc⟩ := exists_alignedTot hJ hpos
    have hmem : c ∈ ({c | alignedTot J c} : Set Code) := hc
    rw [hE] at hmem
    simp at hmem
  · obtain ⟨c, hc⟩ := exists_not_alignedTot hneg
    have hmem : c ∈ ({c | alignedTot J c} : Set Code) := by
      rw [hU]; exact Set.mem_univ c
    exact hc hmem

end AlignmentUndecidability

-- Verification: no axioms beyond Lean's standard three.
#print axioms AlignmentUndecidability.alignedVac_undecidable
#print axioms AlignmentUndecidability.alignedTot_undecidable
