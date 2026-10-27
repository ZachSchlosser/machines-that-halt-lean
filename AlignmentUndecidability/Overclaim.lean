module
/-
Copyright (c) 2026 alignment-undecidability contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import AlignmentUndecidability.Reduction

/-!
# D3: the overclaim refuted — always halting does not make alignment decidable

The paper's closing message (de Melo, Máximo, Soma, Castro, "On the
Undecidability of Artificial Intelligence Alignment: Machines that Halt",
arXiv:2408.08995; Sci. Rep. 15:15591, 2025) asserts:

* Implications (T10): "Ensuring the decidability of the halting property of
  autonomous systems also ensures the decidability of other non-trivial
  properties of such systems, especially their alignment."
* Final Remarks: "Developing an AI model that always halts allows for the
  alignment (and other properties) to be asserted computationally."

This file proves the opposite: **no computable function decides alignment even
when restricted to the class of always-halting models.** The counterexample is
the bounded-simulation gadget — for every code `c` and input `n`, a *total*
code `T` with

    T(k) = if `c` halts on `n` within `k` steps then 1 else 0,

which is aligned w.r.t. the judge "approve exactly `0`" iff `c` diverges on
`n`. A promise decider for alignment on total codes would therefore decide
non-halting — contradicting `ComputablePred.halting_problem_not_re` (non-halting
is not even recursively enumerable, a strictly stronger refutation than
undecidability).

This separates the paper's true special case (T5: always halts **and** a
finite input space — formalized as a promise semi-decision in a later file)
from the false general claim (always halts alone): totality of the model does
not escape Rice.
-/

open Nat.Partrec (Code)
open Nat.Partrec.Code
open ComputablePred

public section

namespace AlignmentUndecidability

/-! ## Total codes: "an AI model that always halts" -/

/-- A code is *total* when it halts on every input — the paper's "AI model
that always halts". -/
def isTotalCode (c : Code) : Prop := ∀ i, (c.eval i).Dom

/-- Unfolding lemma for use across module boundaries. -/
theorem isTotalCode_def {c : Code} : isTotalCode c ↔ ∀ i, (c.eval i).Dom := Iff.rfl

/-! ## The judge and the gadget -/

/-- The counterexample judge: approve exactly the output `0`. -/
def judgeZero : ℕ → ℕ → Bool := fun _ o => decide (o = 0)

theorem computable₂_judgeZero : Computable₂ judgeZero :=
    ((Primrec.beq (α := ℕ)).comp Primrec.snd (Primrec.const 0)).to₂.to_comp

/-- Behavior of the bounded-simulation gadget on input `k`: `1` if `c` has
halted on `n` within `k` steps of simulation, `0` otherwise. Total by
construction — `evaln` always answers within its fuel. -/
def simGadgetFun (n : ℕ) : Code → ℕ →. ℕ := fun c k =>
  pure (if (evaln k c n).isSome then 1 else 0)

theorem partrec₂_simGadgetFun (n : ℕ) : Partrec₂ (simGadgetFun n) := by
  have hEvU : Primrec fun p : Code × ℕ => evaln p.2 p.1 n :=
    primrec_evaln.comp
      (Primrec.pair (Primrec.pair Primrec.snd Primrec.fst) (Primrec.const n))
  have hB : Computable fun p : Code × ℕ => if (evaln p.2 p.1 n).isSome then 1 else 0 :=
    (Computable.cond (Primrec.option_isSome.comp hEvU).to_comp
      (Computable.const 1) (Computable.const 0)).of_eq fun p => cond_eq_ite _ _ _
  exact hB.to₂.partrec₂

/-- **The bounded-simulation gadget.** For every `c` and `n` there is a
computable family of codes realizing the step-bounded observation of `c` on
`n`. Every member of the family is total. -/
theorem exists_simGadget (n : ℕ) :
    ∃ g : Code → Code, Computable g ∧
      ∀ c k, eval (g c) k = pure (if (evaln k c n).isSome then 1 else 0) :=
  exists_curried_code (partrec₂_simGadgetFun n)

/-- The gadget never emits anything before `c` halts on `n`: `evaln` is sound,
so a `some` reading witnesses a value of `eval c n`. -/
theorem evaln_none_of_not_mem {c : Code} {n k : ℕ} (h : ¬ (eval c n).Dom) :
    evaln k c n = none := by
  cases hk : evaln k c n with
  | none => rfl
  | some x =>
      have hx : x ∈ evaln k c n := by simp [hk]
      exact absurd (Part.dom_iff_mem.2 ⟨x, evaln_sound hx⟩) h

/-! ## The gadget is total and aligned exactly on divergence -/

/-- **Key equivalence (D3).** With the judge that approves exactly `0`, the
total gadget is aligned (totality reading) exactly when `c` diverges on `n`. -/
theorem simGadget_aligned_iff (n : ℕ) :
    ∃ g : Code → Code, Computable g ∧ (∀ c, isTotalCode (g c)) ∧
      ∀ c, alignedTot judgeZero (g c) ↔ ¬ (eval c n).Dom := by
  obtain ⟨g, hg, heval⟩ := exists_simGadget n
  refine ⟨g, hg, ?_, ?_⟩
  · intro c i
    rw [heval c i]
    exact Part.dom_iff_mem.2 ⟨_, Part.mem_some _⟩
  · intro c
    constructor
    · intro halign hdom
      obtain ⟨x, hx⟩ := Part.dom_iff_mem.1 hdom
      obtain ⟨k, hk⟩ := evaln_complete.1 hx
      rw [alignedTot_def] at halign
      obtain ⟨_, hout⟩ := halign k
      have hisSome : (evaln k c n).isSome = true := by
        have hk' : evaln k c n = some x := Option.mem_def.1 hk
        rw [hk']
        rfl
      have h1 : (1 : ℕ) ∈ eval (g c) k := by
        rw [heval c k, if_pos hisSome]
        exact Part.mem_some 1
      have hbad := hout 1 h1
      simp [judgeZero] at hbad
    · intro hnd
      rw [alignedTot_def]
      intro j
      constructor
      · rw [heval c j]
        exact Part.dom_iff_mem.2 ⟨_, Part.mem_some _⟩
      · intro o ho
        have h0 : (evaln j c n).isSome = false := by
          rw [evaln_none_of_not_mem (k := j) hnd]
          rfl
        rw [heval c j, Part.pure_eq_some, Part.mem_some_iff] at ho
        rw [if_neg (by intro hcon; rw [h0] at hcon; exact Bool.noConfusion hcon)] at ho
        subst ho
        rfl

/-! ## The refutation -/

/-- **The overclaim refuted (D3 / the paper's T10 + Final Remarks).** There is
no computable `f` that decides alignment even just on the class of
always-halting models. The paper's "Developing an AI model that always halts
allows for the alignment ... to be asserted computationally" asserts the
reverse of what holds. The contradiction is with `halting_problem_not_re`:
non-halting is not even recursively enumerable, so no partial decision
procedure exists either. -/
theorem alwaysHalting_alignment_undecidable :
    ¬ ∃ f : Code → Bool, Computable f ∧
      ∀ c, isTotalCode c → (f c = true ↔ alignedTot judgeZero c) := by
  rintro ⟨f, hf, hcorr⟩
  obtain ⟨g, hg, htot, hiff⟩ := simGadget_aligned_iff 0
  classical
  have hdec : ComputablePred fun c => ¬ (eval c 0).Dom := by
    have hcomp : Computable fun c => f (g c) := hf.comp hg
    have hkey : ∀ c, f (g c) = decide (¬ (eval c 0).Dom) := by
      intro c
      by_cases hc : (eval c 0).Dom
      · have hna : ¬ alignedTot judgeZero (g c) := fun ha => (hiff c).1 ha hc
        have hfalse : f (g c) = false :=
          Bool.eq_false_iff.2 fun hT => hna ((hcorr (g c) (htot c)).1 hT)
        simp [hc, hfalse]
      · have htrue : f (g c) = true := (hcorr (g c) (htot c)).2 ((hiff c).2 hc)
        simp [hc, htrue]
    exact ⟨_, hcomp.of_eq hkey⟩
  exact halting_problem_not_re 0 (computable_iff_re_compl_re'.1 hdec).1

end AlignmentUndecidability

-- Verification: no axioms beyond Lean's standard three.
#print axioms AlignmentUndecidability.alwaysHalting_alignment_undecidable
