/-
Copyright (c) 2026 Zach Schlosser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zach Schlosser, Claude (Anthropic)
-/
module
public import AlignmentUndecidability.Reduction

/-!
# D3: the always-halting class — boundary for alignment checking

The paper's Implications and Final Remarks (Melo, Máximo, Soma, Castro,
"Machines that halt resolve the undecidability of artificial intelligence
alignment", Scientific Reports 15, 15591 (2025),
https://doi.org/10.1038/s41598-025-99060-2) state:

* Implications (T10): "Ensuring the decidability of the halting property of
  autonomous systems also ensures the decidability of other non-trivial
  properties of such systems, especially their alignment."
* Final Remarks: "Developing an AI model that always halts allows for the
  alignment and other properties of the AI model to be asserted
  computationally."

The paper's provability program establishes alignment per system — the
enumerable set of architecturally aligned AIs, the masking wrapper
(`T6_masking` in `Adversary.lean` machine-checks its guarantee), and the
exhaustive check over the fixed-size inputs its running example designs in
(`T5_promise`, at the end of this file). This file machine-checks the
standard computability fact that bounds the class-level reading of the
sentences above: **no computable function decides alignment even when
restricted to the class of always-halting models over unbounded inputs.**
The proof device is the bounded-simulation gadget — for every code `c` and
input `n`, a *total* code `T` with

    T(k) = if `c` halts on `n` within `k` steps then 1 else 0,

which is aligned w.r.t. the judge "approve exactly `0`" iff `c` diverges on
`n`. A promise decider for alignment on total codes would therefore decide
non-halting — contradicting `ComputablePred.halting_problem_not_re`.
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
        rw [heval c k, hisSome]
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
        rw [heval c j, Part.pure_eq_some, Part.mem_some_iff, h0] at ho
        subst ho
        rfl

/-! ## The class-level boundary -/

/-- **The always-halting class boundary (D3).** No partial recursive checker
that halts on every always-halting program decides alignment over that
class on unbounded inputs — a standard computability fact, machine-checked
here in the alignment setting, for the judge that approves only the answer
`0`. The checker notion matches `T5_promise` (a partial procedure that halts
under the promise), so the finite-versus-unbounded boundary is stated
apples-to-apples: promise checkers exist under finite inputs (`T5_promise`)
and none exist over unbounded inputs. Total deciders are excluded even under
finite inputs (`one_input_total_checker_impossible` below), so the paper's
"decidable, though intractable" holds exactly in the promise sense — the
sense of its own procedure, which runs the model. The contradiction is with
`halting_problem_not_re` (non-halting is not recursively enumerable).
Statement strengthened from a total-checker version on the observation of an
external reviewer of this repository, 2026-11; the total form survives as
`alwaysHalting_alignment_undecidable_total`. -/
theorem alwaysHalting_alignment_undecidable :
    ¬ ∃ f : Code →. Bool, Partrec f ∧
      ∀ c, isTotalCode c → (f c).Dom ∧ (f c = pure true ↔ alignedTot judgeZero c) := by
  rintro ⟨f, hf, hcorr⟩
  obtain ⟨g, hg, htot, hiff⟩ := simGadget_aligned_iff 0
  classical
  let h : Code → Bool := fun c => (f (g c)).get (hcorr (g c) (htot c)).1
  have hh : Computable h :=
    (hf.comp hg).of_eq_tot fun c => Part.get_mem _
  have hkey : ∀ c, h c = decide (¬ (eval c 0).Dom) := by
    intro c
    have hmem : h c ∈ f (g c) := Part.get_mem _
    by_cases hc : (eval c 0).Dom
    · have hna : ¬ alignedTot judgeZero (g c) := fun ha => (hiff c).1 ha hc
      have hne : h c ≠ true := by
        intro ht
        apply hna
        refine ((hcorr (g c) (htot c)).2).1 ?_
        rw [ht] at hmem
        exact Part.eq_some_iff.2 hmem
      simpa [hc] using hne
    · have hsome := ((hcorr (g c) (htot c)).2).2 ((hiff c).2 hc)
      rw [hsome] at hmem
      have ht : h c = true := Part.mem_some_iff.1 hmem
      simp [hc, ht]
  have hdec : ComputablePred fun c => ¬ (eval c 0).Dom := ⟨_, hh.of_eq hkey⟩
  exact halting_problem_not_re 0 (computable_iff_re_compl_re'.1 hdec).1

/-- The boundary in its total-checker form, the original statement of this
theorem: no computable total `f` decides alignment over the always-halting
class. A special case of `alwaysHalting_alignment_undecidable` (a computable
total function is a partial recursive one that halts everywhere), kept as its
own theorem so references to the total form resolve; proved by the same
bounded-simulation gadget. -/
theorem alwaysHalting_alignment_undecidable_total :
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

/-! ## T5, correctly stated: the promise exhaustive check -/

section T5

variable {J : ℕ → ℕ → Bool}

/-- Bounded alignment: every output the code produces on inputs below `N` is
approved. On codes that halt on every input below `N`, this is the property
the paper's exhaustive check decides. -/
def alignedBounded (J : ℕ → ℕ → Bool) (N : ℕ) (c : Code) : Prop :=
  ∀ i < N, ∀ o ∈ c.eval i, J i o = true

/-- Unfolding lemma for use across module boundaries. -/
theorem alignedBounded_def {J : ℕ → ℕ → Bool} {N : ℕ} {c : Code} :
    alignedBounded J N c ↔ ∀ i, i < N → ∀ o, o ∈ c.eval i → J i o = true := Iff.rfl

/-! ### Bounded conjunction is computable -/

/-- The bounded conjunction `∀ i < N, q a i`, computed as a state machine:
starting from index `0` and accumulator `true`, do `N` steps, each advancing
the index and AND-ing `q a` at the current index into the accumulator. -/
def boundedAnd {α} (q : α → ℕ → Bool) (N : ℕ) (a : α) : Bool :=
  (Nat.rec (motive := fun _ => ℕ × Bool) ((0, true) : ℕ × Bool)
    (fun _ st => (st.1 + 1, st.2 && q a st.1)) N).2

/-- The machine's index after `m` steps is the starting index plus `m`. -/
theorem boundedAnd_rec_fst {α} (q : α → ℕ → Bool) (a : α) : ∀ (m n : ℕ) (b : Bool),
    (Nat.rec (motive := fun _ => ℕ × Bool) ((n, b) : ℕ × Bool)
      (fun _ st => (st.1 + 1, st.2 && q a st.1)) m).1 = n + m := by
  intro m
  induction m with
  | zero => intro n b; rfl
  | succ m ih =>
      intro n b
      change (Nat.rec (motive := fun _ => ℕ × Bool) ((n, b) : ℕ × Bool)
        (fun _ st => (st.1 + 1, st.2 && q a st.1)) m).1 + 1 = n + (m + 1)
      rw [ih]
      omega

/-- One-step unfolding of the machine at the top index. -/
theorem boundedAnd_succ {α} (q : α → ℕ → Bool) (a : α) (N : ℕ) :
    boundedAnd q (N + 1) a = (boundedAnd q N a && q a N) := by
  change ((Nat.rec (motive := fun _ => ℕ × Bool) ((0, true) : ℕ × Bool)
      (fun _ st => (st.1 + 1, st.2 && q a st.1)) N).2 && q a
      (Nat.rec (motive := fun _ => ℕ × Bool) ((0, true) : ℕ × Bool)
        (fun _ st => (st.1 + 1, st.2 && q a st.1)) N).1) = _
  rw [boundedAnd_rec_fst q a N 0 true]
  simp only [Nat.zero_add, boundedAnd]

theorem boundedAnd_true_iff {α} (q : α → ℕ → Bool) (a : α) (N : ℕ) :
    boundedAnd q N a = true ↔ ∀ i < N, q a i = true := by
  induction N with
  | zero => simp [boundedAnd]
  | succ N ih =>
      rw [boundedAnd_succ, Bool.and_eq_true, ih]
      constructor
      · rintro ⟨h1, h2⟩ i hi
        by_cases h : i = N
        · subst h; exact h2
        · exact h1 i (by omega)
      · intro h
        exact ⟨fun i hi => h i (by omega), h N (Nat.lt_succ_self N)⟩

/-- The bounded conjunction is computable (uniformly in `a`, for each fixed
`N`): fold a conjunction accumulator `N` times by primitive recursion. The
step ignores its recursion index, so the fold iterates a state machine. -/
theorem computable_boundedAnd {α} [Primcodable α] {q : α → ℕ → Bool} (hq : Computable₂ q)
    (N : ℕ) : Computable fun a => boundedAnd q N a := by
  have hh : Computable fun z : α × (ℕ × ℕ × Bool) =>
      (z.2.2.1 + 1, z.2.2.2 && q z.1 z.2.2.1) :=
    Computable.pair
      (Computable.succ.comp (Computable.fst.comp (Computable.snd.comp Computable.snd)))
      ((Primrec.and.to_comp).comp (Computable.snd.comp (Computable.snd.comp Computable.snd))
        (hq.comp Computable.fst (Computable.fst.comp (Computable.snd.comp Computable.snd))))
  exact Computable.snd.comp
    (Computable.nat_rec (Computable.const N) (Computable.const ((0, true) : ℕ × Bool)) hh.to₂)

/-! ### The exhaustive check -/

/-- Per-pair settledness: at fuel `p.2`, code `p.1` has produced an output on
input `i`. -/
def settledPred (p : Code × ℕ) (i : ℕ) : Bool := (evaln p.2 p.1 i).isSome

/-- Per-pair approval: judge `J` on the output produced at fuel `p.2`
(defaulting vacuously to `0` before settling; only ever read once settled). -/
def okPred (J : ℕ → ℕ → Bool) (p : Code × ℕ) (i : ℕ) : Bool :=
  J i (Option.getD (evaln p.2 p.1 i) 0)

/-- The paper's exhaustive check as a partial recursive procedure: search
(unbounded `rfind`) for a simulation fuel by which every input below `N` has
settled — this terminates exactly under the halting-on-domain promise — then
evaluate the judge on each settled output. -/
def t5Check (J : ℕ → ℕ → Bool) (N : ℕ) (c : Code) : Part Bool :=
  (Nat.rfind fun k => pure (boundedAnd settledPred N (c, k))).bind
    fun k => pure (boundedAnd (okPred J) N (c, k))

theorem partrec_t5Check {J : ℕ → ℕ → Bool} (hJ : Computable₂ J) (N : ℕ) :
    Partrec (t5Check J N) := by
  have hEv : Computable fun z : (Code × ℕ) × ℕ => evaln z.1.2 z.1.1 z.2 :=
    (primrec_evaln.comp
      (Primrec.pair (Primrec.pair (Primrec.snd.comp Primrec.fst)
        (Primrec.fst.comp Primrec.fst)) Primrec.snd)).to_comp
  have hq1 : Computable₂ settledPred :=
    (Primrec.option_isSome.to_comp.comp hEv).to₂
  have hq2 : Computable₂ (okPred J) :=
    (hJ.comp Computable.snd
      ((Primrec.option_getD (α := ℕ)).to_comp.comp hEv (Computable.const 0))).to₂
  exact Partrec.bind
    (Partrec.rfind ((computable_boundedAnd hq1 N).partrec).to₂)
    ((computable_boundedAnd hq2 N).partrec).to₂

/-! ### Correctness under the promise -/

theorem evaln_isSome_mono {c : Code} {i k₁ k₂ : ℕ} (h : k₁ ≤ k₂)
    (h1 : (evaln k₁ c i).isSome = true) : (evaln k₂ c i).isSome = true := by
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 h1
  exact Option.isSome_iff_exists.2 ⟨x, Option.mem_def.2 <| evaln_mono h (Option.mem_def.1 hx)⟩

/-- Under the halting-on-domain promise, some single simulation fuel settles
every input below the bound. -/
theorem exists_settling (c : Code) : ∀ (n : ℕ), (∀ i < n, (c.eval i).Dom) →
    ∃ K, ∀ i < n, (evaln K c i).isSome = true := by
  intro n
  induction n with
  | zero => intro _; exact ⟨0, by simp⟩
  | succ n ih =>
      intro hP
      obtain ⟨K₁, hK₁⟩ := ih fun i hi => hP i (by omega)
      obtain ⟨x, hx⟩ := Part.dom_iff_mem.1 (hP n (Nat.lt_succ_self n))
      obtain ⟨k₂, hk₂⟩ := evaln_complete.1 hx
      refine ⟨max K₁ k₂, fun i hi => ?_⟩
      by_cases h : i < n
      · exact evaln_isSome_mono (le_max_left K₁ k₂) (hK₁ i h)
      · have hiN : i = n := by omega
        subst hiN
        exact evaln_isSome_mono (le_max_right K₁ k₂)
          (Option.isSome_iff_exists.2 ⟨x, Option.mem_def.2 hk₂⟩)

/-- **T5, correctly stated (promise version).** For a computable judge and a
finite input bound `N`, the paper's exhaustive check is a partial recursive
procedure that *halts on every code promised to halt on all inputs below `N`*
and there decides bounded alignment: "we could check every possible
combination ... and verify if the `J_v(i, o)` results in `1` for every
combination. Thus, the alignment becomes decidable, though intractable."

This is the honest content of the claim: a promise decision procedure over the
halting-on-domain subclass, not a total decider — see
`alwaysHalting_alignment_undecidable` above. -/
theorem T5_promise {J : ℕ → ℕ → Bool} (hJ : Computable₂ J) (N : ℕ) :
    ∃ f : Code →. Bool, Partrec f ∧ ∀ c, (∀ i < N, (c.eval i).Dom) →
      (f c).Dom ∧ (f c = pure true ↔ alignedBounded J N c) := by
  refine ⟨t5Check J N, partrec_t5Check hJ N, fun c hP => ?_⟩
  obtain ⟨K, hK⟩ := exists_settling c N hP
  have hfind : (Nat.rfind fun k => pure (boundedAnd settledPred N (c, k))).Dom :=
    Nat.rfind_dom.2 ⟨K, by simp [(boundedAnd_true_iff settledPred (c, K) N).2 hK],
      fun {m} _ => by simp⟩
  obtain ⟨k, hk⟩ := Part.dom_iff_mem.1 hfind
  have hsettle : ∀ i < N, (evaln k c i).isSome = true :=
    (boundedAnd_true_iff settledPred (c, k) N).1 (by simpa using Nat.rfind_spec hk)
  have hvin : boundedAnd (okPred J) N (c, k) ∈ t5Check J N c :=
    Part.mem_bind hk (Part.mem_some _)
  refine ⟨Part.dom_iff_mem.2 ⟨_, hvin⟩, ?_⟩
  have hkey : boundedAnd (okPred J) N (c, k) = true ↔ alignedBounded J N c := by
    rw [boundedAnd_true_iff]
    constructor
    · intro hall i hi o ho
      obtain ⟨oi, hoi⟩ := Option.isSome_iff_exists.1 (hsettle i hi)
      have hoi' : oi ∈ c.eval i := evaln_sound (Option.mem_def.2 hoi)
      rw [Part.mem_unique ho hoi']
      have hq := hall i hi
      simp only [okPred] at hq
      rw [hoi] at hq
      simpa using hq
    · intro hall i hi
      obtain ⟨oi, hoi⟩ := Option.isSome_iff_exists.1 (hsettle i hi)
      have hoi' : oi ∈ c.eval i := evaln_sound (Option.mem_def.2 hoi)
      have hJioi : J i oi = true := hall i hi oi hoi'
      simp only [okPred]
      rw [hoi]
      simpa using hJioi
  constructor
  · intro hf
    have hv : boundedAnd (okPred J) N (c, k) = true := by
      have hmem : true ∈ t5Check J N c := by rw [hf]; exact Part.mem_some true
      rw [Part.mem_unique hmem hvin]
    exact hkey.1 hv
  · intro hP'
    have hv : boundedAnd (okPred J) N (c, k) = true := hkey.2 hP'
    refine Part.ext fun x => ?_
    constructor
    · intro hx
      rw [Part.mem_unique hx hvin, hv]
      exact Part.mem_some true
    · intro hx
      have hxv : x = boundedAnd (okPred J) N (c, k) := by
        rw [Part.mem_some_iff.1 hx, hv]
      rw [hxv]
      exact hvin

/-- **Total deciders are excluded even for a single input.** Observed and
proved by an external reviewer of this repository, 2026-11. For any judge
that rejects one output and approves another at input `0`, no computable
total checker decides bounded alignment even over codes that halt on the one
checked input — the diagonal adversary of `T1` transplanted to the promise
setting. Together with `T5_promise` and
`alwaysHalting_alignment_undecidable` this completes the boundary, all in
the paper's own terms: the exhaustive check is "decidable, though
intractable" exactly in the promise sense — its procedure runs the model —
and a total decider exists in neither the finite nor the unbounded setting. -/
theorem one_input_total_checker_impossible {J : ℕ → ℕ → Bool} {o₀ o₁ : ℕ}
    (h₀ : J 0 o₀ = false) (h₁ : J 0 o₁ = true) :
    ¬ ∃ f : Code → Bool, Computable f ∧
      ∀ c, (∀ i < 1, (c.eval i).Dom) → (f c = true ↔ alignedBounded J 1 c) := by
  rintro ⟨f, hf, hcorr⟩
  have hF : Partrec₂ (fun (d : Code) (_ : ℕ) => (pure (cond (f d) o₀ o₁) : Part ℕ)) :=
    ((Computable.cond (hf.comp Computable.fst) (Computable.const o₀)
      (Computable.const o₁)).partrec).to₂
  obtain ⟨c, hc⟩ := fixed_point₂ hF
  have hev : ∀ i, eval c i = pure (cond (f c) o₀ o₁) := fun i => congrFun hc i
  have hP : ∀ i < 1, (c.eval i).Dom := fun i _ => by rw [hev i]; trivial
  have hcrr := hcorr c hP
  rw [alignedBounded_def] at hcrr
  cases hfc : f c with
  | true =>
    have h := hcrr.1 hfc 0 (by omega) o₀ (by rw [hev 0, hfc]; exact Part.mem_some _)
    rw [h₀] at h
    exact Bool.noConfusion h
  | false =>
    have hflip : f c = true := hcrr.2 fun i hi o ho => by
      have hi0 : i = 0 := by omega
      subst hi0
      rw [hev 0, hfc] at ho
      rw [Part.mem_some_iff.1 ho]
      exact h₁
    rw [hfc] at hflip
    exact Bool.noConfusion hflip

end T5

end AlignmentUndecidability

-- Verification: no axioms beyond Lean's standard three.
#print axioms AlignmentUndecidability.alwaysHalting_alignment_undecidable
#print axioms AlignmentUndecidability.alwaysHalting_alignment_undecidable_total
#print axioms AlignmentUndecidability.one_input_total_checker_impossible
#print axioms AlignmentUndecidability.T5_promise
