import Mathlib.Computability.Halting
import Mathlib.Computability.Partrec
import Mathlib.Computability.RE

/-!
# Smoke test — do the plan's building blocks exist in this Mathlib revision (v4.36.0-rc1)?

If this file compiles, every theorem named below is available with the expected shape.
-/

-- The corrected main theorem (D2) rides on this:
#check @ComputablePred.rice₂
-- The explicit halting reduction (D2 / faithful T2′):
#check @ComputablePred.halting_problem
-- The C7 refutation (D3) needs the non-r.e.-ness of non-halting:
#check @ComputablePred.halting_problem_not_re
-- The T1 adversary (D1):
#check @Nat.Partrec.Code.fixed_point₂
-- The bounded-simulation total gadget (D3):
#check @Nat.Partrec.Code.evaln
#check @Nat.Partrec.Code.evaln_complete
-- The computable o⁺ witness (D1/D2 non-triviality):
#check @Nat.rfind
#check @Partrec.rfind
-- The finite-input exhaustive check (T5 companion):
#check @Fintype.decidableForallFintype
