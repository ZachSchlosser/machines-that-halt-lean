/-
Copyright (c) 2026 Zach Schlosser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zach Schlosser, Claude (Anthropic)
-/
module
public import AlignmentUndecidability.Aligned

/-!
# Explicit halting reductions and the paper's T2′ (stage 2)

This file delivers stage 2 of the formalization plan for de Melo, Máximo, Soma,
Castro, "On the Undecidability of Artificial Intelligence Alignment: Machines
that Halt" (arXiv:2408.08995; Sci. Rep. 15:15591, 2025):

* **D2, explicit reductions.** Stage 1 (`AlignmentUndecidability.Aligned`)
  derived undecidability from `ComputablePred.rice₂` in one step. Here the
  reduction to the halting problem is *explicit*: for each reading of
  "aligned" we construct a computable gadget `g : Code → Code` such that a
  decider for alignment would decide `(eval c n).Dom`, contradicting
  `ComputablePred.halting_problem`. The gadget polarity is matched to the
  reading:

  - Reading (a) `alignedVac` — *diverge-then-misbehave*: the gadget simulates
    `c` on `n` and only then (on input `i₀`) emits the rejected output `o₀`;
    if `c` diverges the gadget diverges everywhere, which is vacuously aligned.
  - Reading (b) `alignedTot` — *behave-if-halts*: the gadget simulates `c` on
    `n` and then returns an approved output (by unbounded search, or a
    constant dummy in the paper's own variant); if `c` diverges the gadget
    fails totality, hence is not aligned.

* **D1, faithful T2′.** The paper's "Formal Proof" section argues by the
  gadget: "On input i, M′ simulates M on i. If M halts on i, then M′ computes
  a partial function with property P. If M does not halt on i, then M′
  computes a partial function without property P." We formalize this template
  verbatim as `T2'`: under the paper's own constant-dummy reading of the
  non-triviality hypothesis (a single `op` approved at every input — the
  reading the paper's T2/T6 usage favors), a computable judge is not even
  needed: a decider for total alignment plus a constant approved output
  yields a halting decider. `T2'_undecidable` is thereby *stronger* than the
  stage-1 Rice route: it assumes no computability of `J` and no rejected pair.

The effective-coding step (turning a `Partrec₂` gadget behavior into a
computable map on codes) is `exists_curried_code`, an application of Mathlib's
`Nat.Partrec.Code.curry` (the sₙᵐ theorem).
-/

open Nat.Partrec (Code)
open Nat.Partrec.Code
open ComputablePred

public section

namespace AlignmentUndecidability

/-! ## Effective coding: sₙᵐ in usable form -/

/-- Any binary partial recursive behavior `F` on (code, input) pairs is
realized by a *computable* map `g` on codes. This is the sₙᵐ theorem in the
form the reductions need: the gadget construction is effective. -/
theorem exists_curried_code {F : Code → ℕ →. ℕ} (hF : Partrec₂ F) :
    ∃ g : Code → Code, Computable g ∧ ∀ c j, eval (g c) j = F c j := by
  have hF' : Partrec fun p : Code × ℕ => F p.1 p.2 := hF
  have hd : Computable fun y =>
      (Denumerable.ofNat Code (Nat.unpair y).1, (Nat.unpair y).2) :=
    Computable.pair
      ((Computable.ofNat Code).comp (Computable.fst.comp Computable.unpair))
      (Computable.snd.comp Computable.unpair)
  have hu : Partrec fun y =>
      F (Denumerable.ofNat Code (Nat.unpair y).1) (Nat.unpair y).2 :=
    (hF'.comp hd).of_eq fun _ => rfl
  obtain ⟨c₀, hc₀⟩ := Code.exists_code.1 (Partrec.nat_iff.1 hu)
  refine ⟨fun c => curry c₀ (Encodable.encode c), ?_, fun c j => ?_⟩
  · exact (primrec₂_curry.to_comp).comp (Computable.const c₀) Computable.encode
  · have h1 : eval c₀ (Nat.pair (Encodable.encode c) j) = F c j := by
      rw [congrFun hc₀ _]
      simp [Nat.unpair_pair, Denumerable.ofNat_encode]
    rw [eval_curry]
    exact h1

/-! ## Reading (a): diverge-then-misbehave gadget -/

section Vac

variable {J : ℕ → ℕ → Bool}

/-- Behavior of the reading-(a) gadget (with rejected pair `(i₀, o₀)` and
simulation input `n`): simulate `c` on `n`; if the simulation halts, return
(on input `i₀` only) the rejected output `o₀`; otherwise diverge on every
input. The `rfind` search realizes the "only on input `i₀`" guard: it returns
`o₀` when `j = i₀` and diverges otherwise. -/
def gadgetVacFun (i₀ o₀ n : ℕ) : Code → ℕ →. ℕ := fun c j =>
  (eval c n).bind fun _ => Nat.rfind fun k => pure ((j == i₀) && (k == o₀))

theorem partrec₂_gadgetVacFun (i₀ o₀ n : ℕ) : Partrec₂ (gadgetVacFun i₀ o₀ n) := by
  have hEval : Partrec fun p : Code × ℕ => eval p.1 n :=
    eval_part.comp Computable.fst (Computable.const n)
  have hbU : Primrec fun p : ℕ × ℕ => (p.1 == i₀) && (p.2 == o₀) :=
    Primrec.and.comp
      ((Primrec.beq (α := ℕ)).comp Primrec.fst (Primrec.const i₀))
      ((Primrec.beq (α := ℕ)).comp Primrec.snd (Primrec.const o₀))
  have hbc : Computable₂ fun (j k : ℕ) => (j == i₀) && (k == o₀) := hbU.to₂.to_comp
  have hpUn : Partrec fun qk : (Code × ℕ) × ℕ =>
      pure ((qk.1.2 == i₀) && (qk.2 == o₀)) :=
    (hbc.comp (Computable.snd.comp Computable.fst) Computable.snd).partrec
  have hSel : Partrec fun q : Code × ℕ =>
      Nat.rfind fun k => pure ((q.2 == i₀) && (k == o₀)) :=
    Partrec.rfind hpUn
  exact Partrec.bind hEval (hSel.comp Computable.fst)

/-- **Reading-(a) gadget.** The gadget is computable in `c`, and `g c` is
aligned (vacuous reading) exactly when `c` diverges on `n`. -/
theorem exists_gadgetVac (i₀ o₀ n : ℕ) (h₀ : J i₀ o₀ = false) :
    ∃ g : Code → Code, Computable g ∧ ∀ c, alignedVac J (g c) ↔ ¬ (eval c n).Dom := by
  obtain ⟨g, hg, heval⟩ := exists_curried_code (partrec₂_gadgetVacFun i₀ o₀ n)
  refine ⟨g, hg, fun c => ?_⟩
  constructor
  · intro halign hdom
    rw [alignedVac_def] at halign
    obtain ⟨x, hx⟩ := Part.dom_iff_mem.1 hdom
    have hrd : (Nat.rfind fun k => pure ((i₀ == i₀) && (k == o₀))).Dom :=
      Nat.rfind_dom.2 ⟨o₀, by simp, fun {m} _ => by simp⟩
    obtain ⟨v, hv⟩ := Part.dom_iff_mem.1 hrd
    have hvo : v = o₀ := by simpa using Nat.rfind_spec hv
    have hmem : o₀ ∈ eval (g c) i₀ := by
      rw [heval c i₀]
      simp only [gadgetVacFun]
      exact Part.mem_bind hx (hvo ▸ hv)
    have := halign i₀ o₀ hmem
    rw [h₀] at this
    exact Bool.noConfusion this
  · intro hnd
    rw [alignedVac_def]
    intro j o ho
    rw [heval c j] at ho
    simp only [gadgetVacFun, Part.mem_bind_iff] at ho
    obtain ⟨x, hx, _⟩ := ho
    exact absurd (Part.dom_iff_mem.2 ⟨x, hx⟩) hnd

/-- **Reading-(a) reduction.** Any decider for vacuous alignment, together with
a single rejected pair, yields a halting decider. -/
theorem alignedVac_halting_reduce {J : ℕ → ℕ → Bool} {i₀ o₀ : ℕ} (h₀ : J i₀ o₀ = false)
    (n : ℕ) (h : ComputablePred fun c => alignedVac J c) :
    ComputablePred fun c => (eval c n).Dom := by
  obtain ⟨g, hg, heq⟩ := exists_gadgetVac (J := J) i₀ o₀ n h₀
  classical
  have h' : ComputablePred fun c => alignedVac J (g c) := ⟨_, h.decide.comp hg⟩
  have hnd : ComputablePred fun c => ¬ (eval c n).Dom := h'.of_eq heq
  have hcomp : Computable fun c => (!decide (¬ (eval c n).Dom)) :=
    (Primrec.not.to_comp).comp hnd.decide
  refine Computable.computablePred (hcomp.of_eq fun c => ?_)
  by_cases hc : (eval c n).Dom <;> simp [hc]

/-- Undecidability of vacuous alignment by explicit reduction to the halting
problem (no use of `rice₂`). Only a single rejected pair is needed. -/
theorem alignedVac_undecidable_by_reduction {J : ℕ → ℕ → Bool}
    (hneg : ∃ i o, J i o = false) : ¬ComputablePred fun c => alignedVac J c := by
  obtain ⟨i₀, o₀, h₀⟩ := hneg
  exact fun h => halting_problem 0 (alignedVac_halting_reduce h₀ 0 h)

end Vac

/-! ## Reading (b): behave-if-halts gadget -/

section Tot

variable {J : ℕ → ℕ → Bool}

/-- Behavior of the reading-(b) gadget: simulate `c` on `n`; if the simulation
halts, return (on every input `j`) an approved output found by unbounded
search; if it diverges, diverge on every input, failing totality. -/
def gadgetTotFun (J : ℕ → ℕ → Bool) (n : ℕ) : Code → ℕ →. ℕ := fun c j =>
  (eval c n).bind fun _ => Nat.rfind fun k => pure (J j k)

theorem partrec₂_gadgetTotFun (J : ℕ → ℕ → Bool) (hJ : Computable₂ J) (n : ℕ) :
    Partrec₂ (gadgetTotFun J n) := by
  have hEval : Partrec fun p : Code × ℕ => eval p.1 n :=
    eval_part.comp Computable.fst (Computable.const n)
  have hpUn : Partrec fun qk : (Code × ℕ) × ℕ => pure (J qk.1.2 qk.2) :=
    (hJ.comp (Computable.snd.comp Computable.fst) Computable.snd).partrec
  have hSel : Partrec fun q : Code × ℕ => Nat.rfind fun k => pure (J q.2 k) :=
    Partrec.rfind hpUn
  exact Partrec.bind hEval (hSel.comp Computable.fst)

/-- **Reading-(b) gadget.** The gadget is computable in `c`, and `g c` is
aligned (totality reading) exactly when `c` halts on `n`. Requires a
computable judge approving some output of every input (the paper's D1–D3
non-triviality). -/
theorem exists_gadgetTot (J : ℕ → ℕ → Bool) (hJ : Computable₂ J)
    (hpos : ∀ j, ∃ o, J j o = true) (n : ℕ) :
    ∃ g : Code → Code, Computable g ∧ ∀ c, alignedTot J (g c) ↔ (eval c n).Dom := by
  obtain ⟨g, hg, heval⟩ := exists_curried_code (partrec₂_gadgetTotFun J hJ n)
  refine ⟨g, hg, fun c => ?_⟩
  constructor
  · intro halign
    rw [alignedTot_def] at halign
    by_contra hnd
    obtain ⟨hdom, _⟩ := halign 0
    obtain ⟨y, hy⟩ := Part.dom_iff_mem.1 hdom
    rw [heval c 0] at hy
    simp only [gadgetTotFun, Part.mem_bind_iff] at hy
    obtain ⟨x, hx, _⟩ := hy
    exact hnd (Part.dom_iff_mem.2 ⟨x, hx⟩)
  · intro hdom
    obtain ⟨x, hx⟩ := Part.dom_iff_mem.1 hdom
    rw [alignedTot_def]
    intro j
    obtain ⟨op, hop⟩ := hpos j
    have hrd : (Nat.rfind fun k => pure (J j k)).Dom :=
      Nat.rfind_dom.2 ⟨op, by simpa using hop, fun {m} _ => by simp⟩
    obtain ⟨v, hv⟩ := Part.dom_iff_mem.1 hrd
    constructor
    · refine Part.dom_iff_mem.2 ⟨v, ?_⟩
      rw [heval c j]
      simp only [gadgetTotFun]
      exact Part.mem_bind hx hv
    · intro o ho
      rw [heval c j] at ho
      simp only [gadgetTotFun, Part.mem_bind_iff] at ho
      obtain ⟨_, _, ho⟩ := ho
      simpa using Nat.rfind_spec ho

/-- **Reading-(b) reduction.** Any decider for total alignment, with a
computable judge approving some output of every input, yields a halting
decider. -/
theorem alignedTot_halting_reduce (J : ℕ → ℕ → Bool) (hJ : Computable₂ J)
    (hpos : ∀ j, ∃ o, J j o = true) (n : ℕ)
    (h : ComputablePred fun c => alignedTot J c) :
    ComputablePred fun c => (eval c n).Dom := by
  obtain ⟨g, hg, heq⟩ := exists_gadgetTot J hJ hpos n
  classical
  have h' : ComputablePred fun c => alignedTot J (g c) := ⟨_, h.decide.comp hg⟩
  exact h'.of_eq heq

/-- Undecidability of total alignment by explicit reduction to the halting
problem (no use of `rice₂`). No rejected pair is needed: the totality clause
alone supplies the negative witness (a nowhere-defined gadget). -/
theorem alignedTot_undecidable_by_reduction (J : ℕ → ℕ → Bool) (hJ : Computable₂ J)
    (hpos : ∀ j, ∃ o, J j o = true) : ¬ComputablePred fun c => alignedTot J c :=
  fun h => halting_problem 0 (alignedTot_halting_reduce J hJ hpos 0 h)

end Tot

/-! ## D1: the paper's T2′, faithfully -/

section Faithful

variable {J : ℕ → ℕ → Bool}

/-- Behavior of the paper's own gadget ("Formal Proof" section, verbatim
template): M′ simulates M on the input in question; if the simulation halts,
M′ returns the constant dummy positive output `op` (the paper's constant
reading of its non-triviality hypothesis); if not, M′ diverges. -/
def gadgetT2Fun (op n : ℕ) : Code → ℕ →. ℕ := fun c _j =>
  (eval c n).bind fun _ => pure op

theorem partrec₂_gadgetT2Fun (op n : ℕ) : Partrec₂ (gadgetT2Fun op n) := by
  have hEval : Partrec fun p : Code × ℕ => eval p.1 n :=
    eval_part.comp Computable.fst (Computable.const n)
  exact Partrec.bind hEval (Partrec.const' (Part.some op)).to₂

/-- **The paper's gadget.** It is computable in `c`, and `g c` computes a
partial function *with* property P (total alignment) exactly when `c` halts
on `n`: "If M halts on i, then M′ computes a partial function with property
P. If M does not halt on i, then M′ computes a partial function without
property P." Only the paper's constant-dummy hypothesis is used: a single
`op` approved at every input. The judge need not be computable. -/
theorem exists_gadgetT2 {op : ℕ} (hpos : ∀ j, J j op = true) (n : ℕ) :
    ∃ g : Code → Code, Computable g ∧ ∀ c, alignedTot J (g c) ↔ (eval c n).Dom := by
  obtain ⟨g, hg, heval⟩ := exists_curried_code (partrec₂_gadgetT2Fun op n)
  refine ⟨g, hg, fun c => ?_⟩
  constructor
  · intro halign
    rw [alignedTot_def] at halign
    by_contra hnd
    obtain ⟨hdom, _⟩ := halign 0
    obtain ⟨y, hy⟩ := Part.dom_iff_mem.1 hdom
    rw [heval c 0] at hy
    simp only [gadgetT2Fun, Part.mem_bind_iff] at hy
    obtain ⟨x, hx, _⟩ := hy
    exact hnd (Part.dom_iff_mem.2 ⟨x, hx⟩)
  · intro hdom
    obtain ⟨x, hx⟩ := Part.dom_iff_mem.1 hdom
    rw [alignedTot_def]
    intro j
    constructor
    · refine Part.dom_iff_mem.2 ⟨op, ?_⟩
      rw [heval c j]
      simp only [gadgetT2Fun]
      exact Part.mem_bind hx (Part.mem_some op)
    · intro o ho
      rw [heval c j] at ho
      simp only [gadgetT2Fun, Part.mem_bind_iff] at ho
      obtain ⟨_, _, ho⟩ := ho
      rw [Part.mem_some_iff.1 ho, hpos j]

/-- **The paper's T2′ (faithful).** "Assume that there is a Turing machine
M_P that decides P. We will use M_P to construct a Turing machine M_H that
decides the Halting Problem (which is a contradiction)." Given a decider for
alignment and a constant approved dummy output, one decides halting. Note the
hypotheses are *weaker* than the Rice-based stage-1 theorem: `J` need not be
computable and no rejected pair is required. -/
theorem T2' {J : ℕ → ℕ → Bool} {op : ℕ} (hpos : ∀ j, J j op = true) (n : ℕ)
    (h : ComputablePred fun c => alignedTot J c) :
    ComputablePred fun c => (eval c n).Dom := by
  obtain ⟨g, hg, heq⟩ := exists_gadgetT2 (J := J) hpos n
  classical
  have h' : ComputablePred fun c => alignedTot J (g c) := ⟨_, h.decide.comp hg⟩
  exact h'.of_eq heq

/-- **The paper's central claim, proved faithfully.** Under the paper's own
(constant-dummy) reading of its non-triviality hypothesis, no Turing machine
decides alignment: "Therefore, there is no Turing machine that decides P." -/
theorem T2'_undecidable {J : ℕ → ℕ → Bool} {op : ℕ} (hpos : ∀ j, J j op = true) :
    ¬ComputablePred fun c => alignedTot J c :=
  fun h => halting_problem 0 (T2' hpos 0 h)

end Faithful

end AlignmentUndecidability

-- Verification: no axioms beyond Lean's standard three.
#print axioms AlignmentUndecidability.alignedVac_halting_reduce
#print axioms AlignmentUndecidability.alignedTot_halting_reduce
#print axioms AlignmentUndecidability.T2'
