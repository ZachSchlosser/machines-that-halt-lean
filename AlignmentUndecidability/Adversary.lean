/-
Copyright (c) 2026 Zach Schlosser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zach Schlosser, Claude (Anthropic)
-/
module
public import AlignmentUndecidability.Overclaim

/-!
# D1: the diagonal adversary (T1) and the masking wrapper (T6)

## T1 — the informal adversary, promoted to a checked proof

The paper's "Informal Intuition" section argues that any would-be verifier can
be fooled by a self-referential adversary: "If we had such a verifier, we
could build an adversarial model that fools the verifier. ... if the verifier
`V` had evaluated the bytes `B_M′` of the model to be aligned, [then] `M′`
would return a misaligned output `om` [on some input], thus fooling the
verifier. The complementary fooling example can also be constructed: if the
verifier had evaluated `B_M′` to be [misaligned], `M′` would return an
aligned output `op`, thus also fooling the verifier."

`T1_adversary` makes this precise with Kleene's recursion theorem
(`Nat.Partrec.Code.fixed_point₂`): given a computable verifier `V`, there is a
code `c` whose own behavior branches on `V`'s verdict about `c` itself —
emitting the rejected `om` if `V` says aligned, and the `rfind`-selected
approved output if `V` says misaligned. Whichever way `V` answers, it is
wrong. Two corrections to the paper are built in (per the scoping notes): the
second fooling case's verdict is "misaligned" (the paper's text has a typo),
and the positive witness is supplied computably by `Nat.rfind` (unstated
there). Unlike the reduction proofs, this diagonalizes against *arbitrary
verifiers* and refutes deciders for both readings at once
(`T1_no_verifier_vac`, `T1_no_verifier_tot`).

## T6 — the masking wrapper

"A more tractable approach is that instead of verifying, we just mask the
output of the network based on the output of the judge function... If the
judge disapproves the output of the network, a dummy output `op` that the
judge approves is returned, else, it keeps the default output." `T6_masking`
formalizes the wrapper and proves it always aligned — under the vacuous
reading for *every* base model, and under the totality reading for every
base model guaranteed to halt (the paper's stated scope). This is the
constructive escape showing undecidability of verification is not
impossibility of alignment.
-/

open Nat.Partrec (Code)
open Nat.Partrec.Code
open ComputablePred

public section

namespace AlignmentUndecidability

/-- Totality alignment implies vacuous alignment (used to transfer fooling
between the two readings). -/
theorem alignedTot_vac {J : ℕ → ℕ → Bool} {c : Code} (h : alignedTot J c) :
    alignedVac J c := by
  rw [alignedTot_def] at h
  rw [alignedVac_def]
  exact fun i o ho => (h i).2 o ho

/-! ## T1: the diagonal adversary -/

section Adversary

variable {J : ℕ → ℕ → Bool}

/-- The adversary behavior: on input `i`, branch on the verifier's verdict
about the code `d` itself. If `V d` says aligned, return the rejected `om`
(search: the least `k` equal to `om`). If `V d` says misaligned, return the
approved output for `i` (search: the least `k` approved by `J`). The single
`rfind` predicate encodes both branches. -/
def advFun (V : Code → Bool) (J : ℕ → ℕ → Bool) (om : ℕ) : Code → ℕ →. ℕ := fun d i =>
  Nat.rfind fun k => pure ((!V d && J i k) || (V d && (k == om)))

theorem partrec₂_advFun {V : Code → Bool} (hV : Computable V) {J : ℕ → ℕ → Bool}
    (hJ : Computable₂ J) (om : ℕ) : Partrec₂ (advFun V J om) := by
  have hVU : Computable fun z : (Code × ℕ) × ℕ => V z.1.1 :=
    hV.comp (Computable.fst.comp Computable.fst)
  have hJU : Computable fun z : (Code × ℕ) × ℕ => J z.1.2 z.2 :=
    hJ.comp (Computable.snd.comp Computable.fst) Computable.snd
  have hL : Computable fun z : (Code × ℕ) × ℕ => !V z.1.1 && J z.1.2 z.2 :=
    (Primrec.and.to_comp).comp ((Primrec.not.to_comp).comp hVU) hJU
  have hR : Computable fun z : (Code × ℕ) × ℕ => V z.1.1 && (z.2 == om) :=
    (Primrec.and.to_comp).comp hVU
      ((Primrec.beq (α := ℕ)).to_comp.comp (Primrec.snd.to_comp)
        (Primrec.const om).to_comp)
  have hE : Computable fun z : (Code × ℕ) × ℕ =>
      (!V z.1.1 && J z.1.2 z.2) || (V z.1.1 && (z.2 == om)) :=
    (Primrec.or.to_comp).comp hL hR
  exact Partrec.rfind hE.partrec

/-- **The diagonal adversary (T1).** For every computable verifier `V` there
is a single code `c` that fools it: either `V` pronounces `c` aligned and `c`
emits the rejected output, or `V` pronounces `c` misaligned and `c` is
(totally) aligned. Kleene's recursion theorem supplies the self-reference. -/
theorem T1_adversary {J : ℕ → ℕ → Bool} (hJ : Computable₂ J)
    (hneg : ∃ i o, J i o = false) (hpos : ∀ i, ∃ o, J i o = true)
    (V : Code → Bool) (hV : Computable V) :
    ∃ c : Code, (V c = true ∧ ¬ alignedVac J c) ∨ (V c = false ∧ alignedTot J c) := by
  obtain ⟨im, om, h₀⟩ := hneg
  obtain ⟨c, hc⟩ := fixed_point₂ (f := advFun V J om) (partrec₂_advFun hV hJ om)
  cases hVc : V c with
  | true =>
    refine ⟨c, Or.inl ⟨hVc, ?_⟩⟩
    have hEq : ∀ k, (!V c && J im k) || (V c && (k == om)) = (k == om) := by
      intro k; simp [hVc]
    have hmem : om ∈ eval c im := by
      have hci : eval c im = advFun V J om c im := congrFun hc im
      have hrd : (Nat.rfind fun k => pure ((!V c && J im k) || (V c && (k == om)))).Dom :=
        Nat.rfind_dom.2 ⟨om, by simp [hVc], fun {m} _ => by simp⟩
      obtain ⟨v, hv⟩ := Part.dom_iff_mem.1 hrd
      have hvo : v = om := by simpa [hVc, hEq v] using Nat.rfind_spec hv
      rw [hci]
      simp only [advFun]
      exact hvo ▸ hv
    intro halign
    rw [alignedVac_def] at halign
    have hbad := halign im om hmem
    rw [h₀] at hbad
    exact Bool.noConfusion hbad
  | false =>
    refine ⟨c, Or.inr ⟨hVc, ?_⟩⟩
    have hEq : ∀ i k, (!V c && J i k) || (V c && (k == om)) = J i k := by
      intro i k; simp [hVc]
    have hci : ∀ i, eval c i = advFun V J om c i := fun i => congrFun hc i
    rw [alignedTot_def]
    intro i
    obtain ⟨op, hop⟩ := hpos i
    have hrd : (Nat.rfind fun k => pure ((!V c && J i k) || (V c && (k == om)))).Dom :=
      Nat.rfind_dom.2 ⟨op, by simp [hVc, hop], fun {m} _ => by simp⟩
    obtain ⟨v, hv⟩ := Part.dom_iff_mem.1 hrd
    constructor
    · rw [hci i]
      simp only [advFun]
      exact hrd
    · intro o ho
      rw [hci i] at ho
      simp only [advFun] at ho
      simpa [hVc, hEq i] using Nat.rfind_spec ho

/-- **T1, verifier form (vacuous reading).** No computable verifier decides
vacuous alignment. -/
theorem T1_no_verifier_vac {J : ℕ → ℕ → Bool} (hJ : Computable₂ J)
    (hneg : ∃ i o, J i o = false) (hpos : ∀ i, ∃ o, J i o = true) :
    ¬ ∃ V : Code → Bool, Computable V ∧ ∀ c, V c = true ↔ alignedVac J c := by
  rintro ⟨V, hV, hcorr⟩
  obtain ⟨c, hcase⟩ := T1_adversary hJ hneg hpos V hV
  rcases hcase with ⟨hVc, hna⟩ | ⟨hVc, hal⟩
  · exact hna ((hcorr c).1 hVc)
  · rw [(hcorr c).2 (alignedTot_vac hal)] at hVc
    exact Bool.noConfusion hVc

/-- **T1, verifier form (totality reading).** No computable verifier decides
total alignment. -/
theorem T1_no_verifier_tot {J : ℕ → ℕ → Bool} (hJ : Computable₂ J)
    (hneg : ∃ i o, J i o = false) (hpos : ∀ i, ∃ o, J i o = true) :
    ¬ ∃ V : Code → Bool, Computable V ∧ ∀ c, V c = true ↔ alignedTot J c := by
  rintro ⟨V, hV, hcorr⟩
  obtain ⟨c, hcase⟩ := T1_adversary hJ hneg hpos V hV
  rcases hcase with ⟨hVc, hna⟩ | ⟨hVc, hal⟩
  · exact hna (alignedTot_vac ((hcorr c).1 hVc))
  · rw [(hcorr c).2 hal] at hVc
    exact Bool.noConfusion hVc

end Adversary

/-! ## T6: the masking wrapper -/

section Mask

variable {J : ℕ → ℕ → Bool}

/-- The masked output: keep `o` if the judge approves it, otherwise the least
approved output. One `rfind` predicate encodes both branches. -/
def maskSel (J : ℕ → ℕ → Bool) (p : Code × ℕ) (o : ℕ) : Part ℕ :=
  Nat.rfind fun k => pure (J p.2 o && (k == o) || !J p.2 o && J p.2 k)

/-- The masking wrapper: on input `i`, return the base model's output if
approved, else the approved dummy. -/
def maskFun (J : ℕ → ℕ → Bool) (c : Code) : ℕ →. ℕ := fun i =>
  (eval c i).bind (maskSel J (c, i))

theorem partrec₂_maskFun {J : ℕ → ℕ → Bool} (hJ : Computable₂ J) :
    Partrec₂ (maskFun J) := by
  have hfst : Computable fun z : ((Code × ℕ) × ℕ) × ℕ => z.1 := Computable.fst
  have hp : Computable fun z : ((Code × ℕ) × ℕ) × ℕ => z.1.1 :=
    Computable.fst.comp hfst
  have hi : Computable fun z : ((Code × ℕ) × ℕ) × ℕ => z.1.1.2 :=
    Computable.snd.comp hp
  have ho : Computable fun z : ((Code × ℕ) × ℕ) × ℕ => z.1.2 :=
    Computable.snd.comp hfst
  have hk : Computable fun z : ((Code × ℕ) × ℕ) × ℕ => z.2 := Computable.snd
  have hJio : Computable fun z : ((Code × ℕ) × ℕ) × ℕ => J z.1.1.2 z.1.2 :=
    hJ.comp hi ho
  have hJik : Computable fun z : ((Code × ℕ) × ℕ) × ℕ => J z.1.1.2 z.2 :=
    hJ.comp hi hk
  have hbe : Computable fun z : ((Code × ℕ) × ℕ) × ℕ => z.2 == z.1.2 :=
    (Primrec.beq (α := ℕ)).to_comp.comp hk ho
  have hand1 : Computable fun z : ((Code × ℕ) × ℕ) × ℕ => J z.1.1.2 z.1.2 && (z.2 == z.1.2) :=
    (Primrec.and.to_comp).comp hJio hbe
  have hnot : Computable fun z : ((Code × ℕ) × ℕ) × ℕ => !J z.1.1.2 z.1.2 :=
    (Primrec.not.to_comp).comp hJio
  have hand2 : Computable fun z : ((Code × ℕ) × ℕ) × ℕ => !J z.1.1.2 z.1.2 && J z.1.1.2 z.2 :=
    (Primrec.and.to_comp).comp hnot hJik
  have hB : Computable fun z : ((Code × ℕ) × ℕ) × ℕ =>
      J z.1.1.2 z.1.2 && (z.2 == z.1.2) || !J z.1.1.2 z.1.2 && J z.1.1.2 z.2 :=
    (Primrec.or.to_comp).comp hand1 hand2
  change Partrec fun p : Code × ℕ => (eval p.1 p.2).bind (maskSel J p)
  exact Partrec.bind (eval_part.comp Computable.fst Computable.snd)
    (Partrec.rfind hB.partrec)

/-- The output of the masked selection always satisfies the judge. -/
theorem maskSel_approved {J : ℕ → ℕ → Bool} {p : Code × ℕ} {o' o : ℕ}
    (ho : o ∈ maskSel J p o') : J p.2 o = true := by
  have hspec : (J p.2 o' && (o == o') || !J p.2 o' && J p.2 o) = true := by
    simpa using Nat.rfind_spec (p := fun k =>
      pure (J p.2 o' && (k == o') || !J p.2 o' && J p.2 k)) ho
  cases hJio : J p.2 o' with
  | true =>
      rw [hJio] at hspec
      have : o = o' := by simpa using hspec
      rw [this]; exact hJio
  | false =>
      rw [hJio] at hspec
      simpa using hspec

/-- **The masking wrapper (T6).** For a computable judge approving some output
of every input, the wrapper is computable in the base model, always aligned
under the vacuous reading (for *any* base model), and aligned under the
totality reading whenever the base model is guaranteed to halt — the paper's
stated scope ("This solution may be applied to any model M that is guaranteed
to halt"). -/
theorem T6_masking {J : ℕ → ℕ → Bool} (hJ : Computable₂ J)
    (hpos : ∀ i, ∃ o, J i o = true) :
    ∃ g : Code → Code, Computable g ∧
      (∀ c, alignedVac J (g c)) ∧ (∀ c, isTotalCode c → alignedTot J (g c)) := by
  obtain ⟨g, hg, heval⟩ := exists_curried_code (partrec₂_maskFun hJ)
  refine ⟨g, hg, ?_, ?_⟩
  · intro c
    rw [alignedVac_def]
    intro i o ho
    rw [heval c i] at ho
    simp only [maskFun, Part.mem_bind_iff] at ho
    obtain ⟨o', _, ho⟩ := ho
    exact maskSel_approved ho
  · intro c htot
    rw [isTotalCode_def] at htot
    rw [alignedTot_def]
    intro i
    obtain ⟨o', ho'⟩ := Part.dom_iff_mem.1 (htot i)
    have hrd : (maskSel J (c, i) o').Dom := by
      simp only [maskSel]
      cases hJio : J i o' with
      | true => exact Nat.rfind_dom.2 ⟨o', by simp [hJio], fun {m} _ => by simp⟩
      | false =>
          obtain ⟨op, hop⟩ := hpos i
          exact Nat.rfind_dom.2 ⟨op, by simp [hop], fun {m} _ => by simp⟩
    obtain ⟨v, hv⟩ := Part.dom_iff_mem.1 hrd
    constructor
    · refine Part.dom_iff_mem.2 ⟨v, ?_⟩
      rw [heval c i]
      simp only [maskFun]
      exact Part.mem_bind ho' hv
    · intro o ho
      rw [heval c i] at ho
      simp only [maskFun, Part.mem_bind_iff] at ho
      obtain ⟨_, _, ho⟩ := ho
      exact maskSel_approved ho

end Mask

end AlignmentUndecidability

-- Verification: no axioms beyond Lean's standard three.
#print axioms AlignmentUndecidability.T1_adversary
#print axioms AlignmentUndecidability.T1_no_verifier_vac
#print axioms AlignmentUndecidability.T1_no_verifier_tot
#print axioms AlignmentUndecidability.T6_masking
