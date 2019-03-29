/-
unit tests suggested by Kevin Buzzard
-/

import data.complex.basic -- ℕ, ℤ, ℚ, ℝ, ℂ

import norm_coe

variables (an bn cn dn : ℕ) (az bz cz dz : ℤ) (aq bq cq dq : ℚ)
variables (ar br cr dr : ℝ) (ac bc cc dc : ℂ)

example : (an : ℤ) = bn → an = bn := by {norm_coe1, intro, assumption}
example : an = bn → (an : ℤ) = bn := by {norm_coe1, intro, assumption}
example : az = bz ↔ (az : ℚ) = bz := by {norm_coe1, refl}

example : (aq : ℝ) = br ↔ (aq : ℂ) = br := by {norm_coe1, refl}
example : (an : ℚ) = bz ↔ (an : ℂ) = bz := by {norm_coe1, refl}
example : (((an : ℤ) : ℚ) : ℝ) = bq ↔ ((an : ℚ) : ℂ) = (bq : ℝ) := by {norm_coe1, refl}

example : (an : ℤ) < bn ↔ an < bn             := sorry
example : (an : ℚ) < bz ↔ (an : ℝ) < bz       := sorry
example : ((an : ℤ) : ℝ) < bq ↔ (an : ℚ) < bq := sorry

-- zero and one cause special problems
example : 0 < (bq : ℝ) ↔ 0 < bq             := sorry
example : aq < (1 : ℕ) ↔ (aq : ℝ) < (1 : ℤ) := sorry

example : (an : ℤ) + bn = (an + bn : ℕ)   := by {norm_coe1, refl}
example : (an : ℂ) + bq = ((an + bq) : ℚ) := by {norm_coe1, refl}
example : (((an : ℤ) : ℚ) : ℝ) + bn = (an + (bn : ℤ)) := by {norm_coe1, refl}

example : (((((an : ℚ) : ℝ) * bq) + (cq : ℝ) ^ dn) : ℂ) = (an : ℂ) * (bq : ℝ) + cq ^ dn := sorry
example : ((an : ℤ) : ℝ) < bq ∧ (cr : ℂ) ^ 2 = dz ↔ (an : ℚ) < bq ∧ ((cr ^ 2) : ℂ) = dz := sorry