import data.complex.basic data.nat.enat
import norm_coe

/- --------
    EQ
-------- -/

attribute [norm_coe] nat.cast_succ
attribute [norm_coe] int.coe_nat_succ

attribute [norm_coe] nat.cast_add
attribute [norm_coe] int.coe_nat_add
attribute [norm_coe] int.cast_add
attribute [norm_coe] rat.cast_add
attribute [norm_coe] complex.of_real_add
#check @int.coe_nat_add_out
#check @int.eq_cast

attribute [norm_coe] int.cast_neg_succ_of_nat
attribute [norm_coe] int.cast_neg_of_nat
attribute [norm_coe] int.cast_neg
attribute [norm_coe] rat.cast_neg
attribute [norm_coe] complex.of_real_neg

attribute [norm_coe] nat.cast_sub
attribute [norm_coe] int.cast_sub_nat_nat
attribute [norm_coe] int.coe_nat_sub
attribute [norm_coe] int.cast_sub
attribute [norm_coe] rat.cast_sub
attribute [norm_coe] complex.of_real_sub

attribute [norm_coe] nat.cast_mul
attribute [norm_coe] int.coe_nat_mul
attribute [norm_coe] int.cast_mul
attribute [norm_coe] rat.cast_mul
attribute [norm_coe] complex.of_real_mul

attribute [norm_coe] rat.cast_inv
attribute [norm_coe] complex.of_real_inv

attribute [norm_coe] int.coe_nat_div
attribute [norm_coe] rat.cast_div
attribute [norm_coe] complex.of_real_div

attribute [norm_coe] nat.cast_min
attribute [norm_coe] int.cast_min
attribute [norm_coe] rat.cast_min

attribute [norm_coe] nat.cast_max
attribute [norm_coe] int.cast_max
attribute [norm_coe] rat.cast_max

attribute [norm_coe] int.coe_nat_abs
attribute [norm_coe] int.cast_abs
attribute [norm_coe] rat.cast_abs

attribute [norm_coe] nat.cast_pow
attribute [norm_coe] int.coe_nat_pow
attribute [norm_coe] int.cast_pow
attribute [norm_coe] rat.cast_pow
attribute [norm_coe] complex.of_real_pow
attribute [norm_coe] complex.of_real_fpow

attribute [norm_coe] nat.cast_bit0
attribute [norm_coe] int.cast_bit0
attribute [norm_coe] rat.cast_bit0
attribute [norm_coe] complex.of_real_bit0

attribute [norm_coe] nat.cast_bit1
attribute [norm_coe] int.cast_bit1
attribute [norm_coe] rat.cast_bit1
attribute [norm_coe] complex.of_real_bit1

@[norm_coe]
lemma int.coe_nat_bit0 (n : ℕ) : (↑(bit0 n) : ℤ) = bit0 ↑n :=
by {unfold bit0, simp}
@[norm_coe]
lemma int.coe_nat_bit1 (n : ℕ) : (↑(bit1 n) : ℤ) = bit1 ↑n :=
by {unfold bit1, unfold bit0, simp}
@[norm_coe]
lemma int.cast_coe_nat_one {α} [add_monoid α] [has_one α] [has_neg α] :
    (((1 : ℕ) : ℤ) : α) = (1 : α) :=
by simp

/- --------
    IFF
 -------- -/

attribute [norm_coe] int.coe_nat_eq_coe_nat_iff

attribute [norm_coe] nat.cast_eq_zero
attribute [norm_coe] int.coe_nat_eq_zero
attribute [norm_coe] int.cast_eq_zero
attribute [norm_coe] rat.cast_eq_zero
attribute [norm_coe] complex.of_real_eq_zero

attribute [norm_coe] nat.cast_ne_zero
attribute [norm_coe] int.coe_nat_ne_zero
attribute [norm_coe] int.cast_ne_zero
attribute [norm_coe] rat.cast_ne_zero
attribute [norm_coe] complex.of_real_ne_zero

attribute [norm_coe] nat.cast_le
attribute [norm_coe] int.coe_nat_le
attribute [norm_coe] int.cast_le
attribute [norm_coe] rat.cast_le

attribute [norm_coe] nat.cast_lt
attribute [norm_coe] int.coe_nat_lt
attribute [norm_coe] int.cast_lt
attribute [norm_coe] rat.cast_lt

@[norm_coe]
lemma ge_from_le {α} [has_le α] : ∀ (x y : α), x ≥ y ↔ y ≤ x :=
by simp
@[norm_coe]
lemma gt_from_lt {α} [has_lt α] : ∀ (x y : α), x > y ↔ y < x :=
by simp

attribute [norm_coe] nat.cast_pos
attribute [norm_coe] int.coe_nat_pos
attribute [norm_coe] int.cast_pos
attribute [norm_coe] rat.cast_pos

attribute [norm_coe] nat.cast_nonneg
attribute [norm_coe] int.coe_nat_nonneg
attribute [norm_coe] int.cast_nonneg
attribute [norm_coe] rat.cast_nonneg

attribute [norm_coe] int.cast_nonpos
attribute [norm_coe] rat.cast_nonpos

attribute [norm_coe] int.cast_lt_zero
attribute [norm_coe] rat.cast_lt_zero

attribute [norm_coe] nat.cast_inj
attribute [norm_coe] int.coe_nat_inj'
attribute [norm_coe] int.cast_inj
attribute [norm_coe] rat.cast_inj
attribute [norm_coe] complex.of_real_inj

attribute [norm_coe] int.coe_nat_dvd
attribute [norm_coe] enat.coe_le_coe
attribute [norm_coe] enat.coe_lt_coe
--attribute [norm_coe] enat.coe_get

run_cmd (norm_coe.norm_coe_attr.get_cache >>= tactic.trace)