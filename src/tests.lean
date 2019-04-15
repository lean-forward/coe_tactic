/-
unit tests suggested by Kevin Buzzard
-/

import data.complex.basic -- ℕ, ℤ, ℚ, ℝ, ℂ
import norm_coe lemmas_norm_coe lemmas_simp_coe

constants (an bn cn dn : ℕ) (az bz cz dz : ℤ) (aq bq cq dq : ℚ)
constants (ar br cr dr : ℝ) (ac bc cc dc : ℂ)

example : (an : ℤ) = bn → an = bn := by {intro, assumption_mod_coe}
example : an = bn → (an : ℤ) = bn := by {intro, assumption_mod_coe}
example : az = bz ↔ (az : ℚ) = bz := by {norm_coe1}

example : (aq : ℝ) = br ↔ (aq : ℂ) = br := by {norm_coe1}
example : (an : ℚ) = bz ↔ (an : ℂ) = bz := by {norm_coe1}
example : (((an : ℤ) : ℚ) : ℝ) = bq ↔ ((an : ℚ) : ℂ) = (bq : ℝ) :=
by {norm_coe1}

example : (an : ℤ) < bn ↔ an < bn             := by {norm_coe1}
example : (an : ℚ) < bz ↔ (an : ℝ) < bz       := by {norm_coe1}
example : ((an : ℤ) : ℝ) < bq ↔ (an : ℚ) < bq := by {norm_coe1}

-- zero and one cause special problems
example : 0 < (bq : ℝ) ↔ 0 < bq             := by {norm_coe1}
example : aq < (1 : ℕ) ↔ (aq : ℝ) < (1 : ℤ) := by {norm_coe1}

example : (an : ℤ) + bn = (an + bn : ℕ)   := by {norm_coe1}
example : (an : ℂ) + bq = ((an + bq) : ℚ) := by {norm_coe1}
example : (((an : ℤ) : ℚ) : ℝ) + bn = (an + (bn : ℤ)) := by {norm_coe1}

example : (((((an : ℚ) : ℝ) * bq) + (cq : ℝ) ^ dn) : ℂ) = (an : ℂ) * (bq : ℝ) + cq ^ dn :=
by {norm_coe1}
example : ((an : ℤ) : ℝ) < bq ∧ (cr : ℂ) ^ 2 = dz ↔ (an : ℚ) < bq ∧ ((cr ^ 2) : ℂ) = dz :=
by {norm_coe1}

example : (an : ℤ) = 1 → an = 1 := by {intro, assumption_mod_coe}
example : (an : ℤ) < 5 → an < 5 := by {intro, assumption_mod_coe}
example : an < 5 → (an : ℤ) < 5 := by {intro, assumption_mod_coe}
example : (an + 5) < 10 → (an : ℤ) + 5 < 10 := by {intro, assumption_mod_coe}
example : (an : ℤ) + 5 < 10 → (an + 5) < 10 := by {intro, assumption_mod_coe}
example : ((an + 5 : ℕ) : ℤ) < 10 → an + 5 < 10 := by {intro, assumption_mod_coe}
example : an + 5 < 10 → ((an + 5 : ℕ) : ℤ) < 10 := by {intro, assumption_mod_coe}

example : az < 1 :=
begin
    -- this is bad
    norm_coe1,
    norm_coe1,
    norm_coe1,
    sorry
end

example (h : (cz : ℚ) = az / bz) : (cz : ℝ) = az / bz :=
by sorry
