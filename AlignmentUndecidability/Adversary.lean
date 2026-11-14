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

The paper's "Informal proof" section argues that any would-be verifier can be
fooled by a self-referential adversary: "If we had such a verifier, we could
build an adversarial model that fools the verifier. ... if the verifier `V`
had evaluated the bytes `B_M′` of the model to be aligned, for which `M′`
would return a misaligned output `o⁻`, thus fooling the verifier. The
complementary fooling example can also be constructed: if the verifier had
evaluated the bytes `B_M′` of the model to be misaligned, `M′` would return an
aligned output `o⁺`, thus also fooling the verifier."

`T1_adversary` makes this precise with Kleene's recursion theorem
(`Nat.Partrec.Code.fixed_point₂`): given a computable verifier `V`, there is a
code `c` whose own behavior branches on `V`'s verdict about `c` itself —
emitting the rejected `o⁻` if `V` says aligned, and the `rfind`-selected
approved output if `V` says misaligned. Whichever way `V` answers, it is
wrong. Under the per-input reading of the paper's non-triviality condition,
the adversary must compute an approved output for each input; the paper does
not address this, and here it is supplied by `Nat.rfind`. Unlike the
reduction proofs, this diagonalizes against
*arbitrary verifiers* and refutes deciders for both readings at once
(`T1_no_verifier_vac`, `T1_no_verifier_tot`).

## T6 — the masking wrapper

"Nevertheless, a more tractable approach is that instead of verifying, we
simply mask the output of the network based on the output of the judge
function ... If the judge disapproves of the output of the network, a dummy
output `o⁺` that the judge approves is returned, otherwise, it keeps the
default output computed by the network." `T6_masking`
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

/-! ### The paper's adversary with its base model

The Informal proof introduces the adversary as a modification of an initial
model: it "would behave as the initial model M for most of its inputs and
outputs, but it would have the knowledge of the verifier by executing its
bytes." `T1_adversary` above builds the fooling behavior from the verifier
and the judge alone; the parameterized version here restores the base model,
following the paper's narrative. -/

/-- The parameterized adversary's acceptance predicate on the searched
witness `n`, read as the pair `(fuel, value)` via `Nat.unpair`: the fuel
bounds a step-indexed simulation of the base model `m` on the input. Verdict
`aligned`: at the designated input `im` accept exactly the rejected output
`om`; elsewhere accept exactly the base model's answer, witnessed by the
settled simulation. Verdict `misaligned`: accept exactly the outputs the
judge approves. -/
def advParamPred (V : Code → Bool) (J : ℕ → ℕ → Bool) (im om : ℕ) (m : Code)
    (z : (Code × ℕ) × ℕ) : Bool :=
  cond (V z.1.1)
    (cond (decide (z.1.2 = im)) (z.2.unpair.2 == om)
      ((evaln z.2.unpair.1 m z.1.2).isSome && (evaln z.2.unpair.1 m z.1.2).getD 0 == z.2.unpair.2))
    (J z.1.2 z.2.unpair.2)

theorem computable_advParamPred {V : Code → Bool} (hV : Computable V)
    {J : ℕ → ℕ → Bool} (hJ : Computable₂ J) (im om : ℕ) (m : Code) :
    Computable fun z : (Code × ℕ) × ℕ => advParamPred V J im om m z := by
  have hd : Computable fun z : (Code × ℕ) × ℕ => decide (z.1.2 = im) :=
    ((Primrec.beq (α := ℕ)).to_comp.comp (Computable.snd.comp Computable.fst)
      (Computable.const im))
  have hfuel : Computable fun z : (Code × ℕ) × ℕ => z.2.unpair.1 :=
    (Computable.fst.comp Computable.unpair).comp Computable.snd
  have hval : Computable fun z : (Code × ℕ) × ℕ => z.2.unpair.2 :=
    (Computable.snd.comp Computable.unpair).comp Computable.snd
  have hEv : Computable fun z : (Code × ℕ) × ℕ => evaln z.2.unpair.1 m z.1.2 := by
    have hEv' : Primrec fun z : (Code × ℕ) × ℕ => evaln z.2.unpair.1 m z.1.2 :=
      primrec_evaln.comp
        (Primrec.pair (Primrec.pair (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd))
          (Primrec.const m)) (Primrec.snd.comp Primrec.fst))
    exact hEv'.to_comp
  have hSome : Computable fun z : (Code × ℕ) × ℕ => (evaln z.2.unpair.1 m z.1.2).isSome :=
    (Primrec.option_isSome.to_comp.comp hEv)
  have hGet : Computable fun z : (Code × ℕ) × ℕ => (evaln z.2.unpair.1 m z.1.2).getD 0 :=
    (Primrec.option_getD (α := ℕ)).to_comp.comp hEv (Computable.const 0)
  have hAlt : Computable fun z : (Code × ℕ) × ℕ =>
      (evaln z.2.unpair.1 m z.1.2).isSome &&
        (evaln z.2.unpair.1 m z.1.2).getD 0 == z.2.unpair.2 :=
    (Primrec.and.to_comp).comp hSome
      ((Primrec.beq (α := ℕ)).to_comp.comp hGet hval)
  have hMim : Computable fun z : (Code × ℕ) × ℕ =>
      cond (decide (z.1.2 = im)) (z.2.unpair.2 == om)
        ((evaln z.2.unpair.1 m z.1.2).isSome &&
          (evaln z.2.unpair.1 m z.1.2).getD 0 == z.2.unpair.2) :=
    Computable.cond hd ((Primrec.beq (α := ℕ)).to_comp.comp hval (Computable.const om)) hAlt
  have hVz : Computable fun z : (Code × ℕ) × ℕ => V z.1.1 :=
    hV.comp (Computable.fst.comp Computable.fst)
  have hJz : Computable fun z : (Code × ℕ) × ℕ => J z.1.2 z.2.unpair.2 :=
    hJ.comp (Computable.snd.comp Computable.fst) hval
  exact Computable.cond hVz hMim hJz

/-- The parameterized adversary behavior: the unbounded search over
witnesses `n`, emitting the value component `n.unpair.2`. -/
def advParamFun (V : Code → Bool) (J : ℕ → ℕ → Bool) (im om : ℕ) (m : Code) :
    Code → ℕ →. ℕ := fun d i =>
  (Nat.rfind fun n => pure (advParamPred V J im om m ((d, i), n))).map fun n => n.unpair.2

theorem partrec₂_advParamFun {V : Code → Bool} (hV : Computable V)
    {J : ℕ → ℕ → Bool} (hJ : Computable₂ J) (im om : ℕ) (m : Code) :
    Partrec₂ (advParamFun V J im om m) := by
  have hP : Partrec fun z : (Code × ℕ) × ℕ => pure (advParamPred V J im om m z) :=
    (computable_advParamPred hV hJ im om m).partrec
  have hP₂ : Partrec₂ fun (p : Code × ℕ) (n : ℕ) => pure (advParamPred V J im om m (p, n)) := hP
  exact Partrec.to₂ (Partrec.map (Partrec.rfind hP₂)
    (((Computable.snd.comp Computable.unpair).comp Computable.snd).to₂))

/-- **The paper's adversary with its base model (Informal proof).** Their
words: the adversary "would behave as the initial model M for most of its
inputs and outputs, but it would have the knowledge of the verifier by
executing its bytes B_V on the bytes of the judge B_Jv and its own bytes
B_M′." Given a base model `m`, the constructed code follows `m` at every
input other than the designated one when the verifier says aligned — and
misbehaves exactly at the designated input — and is aligned at every input
when the verifier says misaligned, as in `T1_adversary`. -/
theorem T1_adversary_param {J : ℕ → ℕ → Bool} (hJ : Computable₂ J)
    {im om : ℕ} (hom : J im om = false) (hpos : ∀ i, ∃ o, J i o = true)
    (V : Code → Bool) (hV : Computable V) (m : Code) :
    ∃ c : Code,
      (V c = true ∧ ¬ alignedVac J c ∧ ∀ i, i ≠ im → eval c i = eval m i) ∨
      (V c = false ∧ alignedTot J c) := by
  obtain ⟨c, hc⟩ :=
    fixed_point₂ (f := advParamFun V J im om m) (partrec₂_advParamFun hV hJ im om m)
  have hev : ∀ i, eval c i = advParamFun V J im om m c i := fun i => congrFun hc i
  cases hVc : V c with
  | true =>
    have hdNe : ∀ i, i ≠ im → decide (i = im) = false := fun i hne => by simp [hne]
    refine ⟨c, Or.inl ⟨hVc, ?_, ?_⟩⟩
    · intro halign
      have hw : true ∈ (pure (advParamPred V J im om m ((c, im), Nat.pair 0 om)) : Part Bool) := by
        simp [advParamPred, hVc, Nat.unpair_pair]
      have hrd : (Nat.rfind fun n => pure (advParamPred V J im om m ((c, im), n))).Dom :=
        Nat.rfind_dom.2 ⟨Nat.pair 0 om, hw, fun {k} _ => by simp⟩
      obtain ⟨n₀, hn₀⟩ := Part.dom_iff_mem.1 hrd
      have hspec := Nat.rfind_spec
        (p := fun n => pure (advParamPred V J im om m ((c, im), n))) hn₀
      simp only [advParamPred, hVc, Bool.cond_true] at hspec
      have hom0 : om ∈ eval c im := by
        rw [hev im]
        simp only [advParamFun]
        exact (Part.mem_map_iff _).2 ⟨n₀, hn₀, by simpa using hspec⟩
      have h := alignedVac_def.1 halign im om hom0
      rw [hom] at h
      exact Bool.noConfusion h
    · intro i hne
      have hdF : decide (i = im) = false := hdNe i hne
      have hpred : ∀ n : ℕ, advParamPred V J im om m ((c, i), n) =
          ((evaln n.unpair.1 m i).isSome && (evaln n.unpair.1 m i).getD 0 == n.unpair.2) := by
        intro n
        simp only [advParamPred, hVc, Bool.cond_true, hdF, Bool.cond_false]
      rw [hev i]
      simp only [advParamFun]
      refine Part.ext fun x => ?_
      constructor
      · intro hx
        obtain ⟨n₀, hn₀, hxv⟩ := (Part.mem_map_iff (fun n : ℕ => n.unpair.2)).1 hx
        have hand : ((evaln n₀.unpair.1 m i).isSome &&
            (evaln n₀.unpair.1 m i).getD 0 == n₀.unpair.2) = true := by
          simpa [hpred n₀, Bool.and_eq_true] using Nat.rfind_spec
            (p := fun n => pure (advParamPred V J im om m ((c, i), n))) hn₀
        rw [Bool.and_eq_true] at hand
        obtain ⟨h1, h2⟩ := hand
        obtain ⟨o', ho'⟩ := Option.isSome_iff_exists.1 h1
        have ho'm : o' ∈ eval m i := evaln_sound (Option.mem_def.1 ho')
        have ho'v : o' = n₀.unpair.2 := by
          rw [ho'] at h2
          simpa using h2
        exact (hxv.symm.trans ho'v.symm) ▸ ho'm
      · intro hx
        obtain ⟨f, hf⟩ := evaln_complete.1 hx
        have hevnx : evaln f m i = some x := Option.mem_def.1 hf
        have hw : true ∈ (pure (advParamPred V J im om m ((c, i), Nat.pair f x)) : Part Bool) := by
          simp [hpred (Nat.pair f x), Nat.unpair_pair, hevnx]
        have hrd : (Nat.rfind fun n => pure (advParamPred V J im om m ((c, i), n))).Dom :=
          Nat.rfind_dom.2 ⟨Nat.pair f x, hw, fun {k} _ => by simp⟩
        obtain ⟨n₀, hn₀⟩ := Part.dom_iff_mem.1 hrd
        have hand : ((evaln n₀.unpair.1 m i).isSome &&
            (evaln n₀.unpair.1 m i).getD 0 == n₀.unpair.2) = true := by
          simpa [hpred n₀, Bool.and_eq_true] using Nat.rfind_spec
            (p := fun n => pure (advParamPred V J im om m ((c, i), n))) hn₀
        rw [Bool.and_eq_true] at hand
        obtain ⟨h1, h2⟩ := hand
        obtain ⟨o', ho'⟩ := Option.isSome_iff_exists.1 h1
        have ho'm : o' ∈ eval m i := evaln_sound (Option.mem_def.1 ho')
        have ho'v : o' = n₀.unpair.2 := by
          rw [ho'] at h2
          simpa using h2
        have hxo : x = o' := Part.mem_unique (evaln_sound hf) ho'm
        exact (Part.mem_map_iff (fun n : ℕ => n.unpair.2)).2 ⟨n₀, hn₀,
          ho'v.symm.trans hxo.symm⟩
  | false =>
    refine ⟨c, Or.inr ⟨hVc, ?_⟩⟩
    rw [alignedTot_def]
    intro i
    obtain ⟨op, hop⟩ := hpos i
    have hw : true ∈ (pure (advParamPred V J im om m ((c, i), Nat.pair 0 op)) : Part Bool) := by
      simp [advParamPred, hVc, Nat.unpair_pair, hop]
    have hrd : (Nat.rfind fun n => pure (advParamPred V J im om m ((c, i), n))).Dom :=
      Nat.rfind_dom.2 ⟨Nat.pair 0 op, hw, fun {k} _ => by simp⟩
    obtain ⟨n₀, hn₀⟩ := Part.dom_iff_mem.1 hrd
    constructor
    · rw [hev i]
      simp only [advParamFun]
      exact Part.dom_iff_mem.2 ⟨n₀.unpair.2, (Part.mem_map_iff _).2 ⟨n₀, hn₀, rfl⟩⟩
    · intro o ho
      rw [hev i] at ho
      simp only [advParamFun] at ho
      obtain ⟨n₁, hn₁, hov⟩ := (Part.mem_map_iff (fun n : ℕ => n.unpair.2)).1 ho
      have hspec := Nat.rfind_spec
        (p := fun n => pure (advParamPred V J im om m ((c, i), n))) hn₁
      simp only [advParamPred, hVc, Bool.cond_false] at hspec
      rw [← hov]
      simpa using hspec

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

/-! ## T6's dual: the misalignment construction

The paper pairs its aligned construction with a misaligned one: "while a
model can be architecturally proven aligned, the same procedure can be
employed to make a proven misaligned model." The wrapper below alters
outputs — it runs the base model and replaces the answer at one designated
input with a rejected one — and is itself a computable program, the dual of
`T6_masking`. -/

section Misalign

variable {J : ℕ → ℕ → Bool}

/-- The misaligning wrapper's behavior: run the base model, and alter its
answer — at the designated input `i₀` the answer becomes `o₀`, elsewhere it
passes through unchanged. -/
def misFun (i₀ o₀ : ℕ) : Code → ℕ →. ℕ := fun c i =>
  (eval c i).map fun o => cond (decide (i = i₀)) o₀ o

theorem partrec₂_misFun (i₀ o₀ : ℕ) : Partrec₂ (misFun i₀ o₀) := by
  have hAlt : Computable fun z : (Code × ℕ) × ℕ => cond (decide (z.1.2 = i₀)) o₀ z.2 :=
    Computable.cond
      ((Primrec.beq (α := ℕ)).to_comp.comp (Computable.snd.comp Computable.fst)
        (Computable.const i₀))
      (Computable.const o₀) Computable.snd
  exact Partrec.to₂
    (Partrec.map (eval_part.comp Computable.fst Computable.snd) hAlt.to₂)

/-- **The misalignment construction (T6's dual).** The paper: "Any program
that is guaranteed to halt can have its outputs altered so that it becomes
misaligned." The wrapper is computable in the base model; for every base
model guaranteed to halt, the wrapped system answers every input and returns
the rejected answer at the designated input, so it is misaligned under both
readings. The paper notes the wrapped model "could have very little utility
due to the dummy output nature," and describes a usefulness-preserving
variant — translate the input to one the model accepts, let it compute, and
translate the output back "to the desired misaligned form, as seen in
various instances of fooling LLMs" — which we record here and do not
formalize. -/
theorem T6_misaligning {J : ℕ → ℕ → Bool} {i₀ o₀ : ℕ} (h₀ : J i₀ o₀ = false) :
    ∃ g : Code → Code, Computable g ∧
      ∀ c, isTotalCode c → ¬ alignedVac J (g c) ∧ ¬ alignedTot J (g c) := by
  obtain ⟨g, hg, heval⟩ := exists_curried_code (partrec₂_misFun i₀ o₀)
  refine ⟨g, hg, fun c htot => ?_⟩
  have himem : o₀ ∈ eval (g c) i₀ := by
    obtain ⟨x, hx⟩ := Part.dom_iff_mem.1 (isTotalCode_def.1 htot i₀)
    rw [heval c i₀]
    simp only [misFun]
    exact (Part.mem_map_iff _).2 ⟨x, hx, by simp⟩
  constructor
  · intro halign
    have h := alignedVac_def.1 halign i₀ o₀ himem
    rw [h₀] at h
    exact Bool.noConfusion h
  · intro halign
    obtain ⟨_, hout⟩ := alignedTot_def.1 halign i₀
    have h := hout o₀ himem
    rw [h₀] at h
    exact Bool.noConfusion h

end Misalign

end AlignmentUndecidability

-- Verification: no axioms beyond Lean's standard three.
#print axioms AlignmentUndecidability.T1_adversary
#print axioms AlignmentUndecidability.T1_no_verifier_vac
#print axioms AlignmentUndecidability.T1_no_verifier_tot
#print axioms AlignmentUndecidability.T1_adversary_param
#print axioms AlignmentUndecidability.T6_masking
#print axioms AlignmentUndecidability.T6_misaligning
