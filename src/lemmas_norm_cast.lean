import data.complex.basic data.nat.enat
import norm_cast lemmas_simp_cast

/- --------
    EQ
-------- -/

attribute [norm_cast] nat.cast_succ
attribute [norm_cast] int.coe_nat_succ

attribute [norm_cast] nat.cast_add
attribute [norm_cast] int.coe_nat_add
attribute [norm_cast] int.cast_add
attribute [norm_cast] rat.cast_add
attribute [norm_cast] complex.of_real_add
#check @int.coe_nat_add_out
#check @int.eq_cast

attribute [norm_cast] int.cast_neg_succ_of_nat
attribute [norm_cast] int.cast_neg_of_nat
attribute [norm_cast] int.cast_neg
attribute [norm_cast] rat.cast_neg
attribute [norm_cast] complex.of_real_neg

attribute [norm_cast] nat.cast_sub
attribute [norm_cast] int.cast_sub_nat_nat
attribute [norm_cast] int.coe_nat_sub
attribute [norm_cast] int.cast_sub
attribute [norm_cast] rat.cast_sub
attribute [norm_cast] complex.of_real_sub

attribute [norm_cast] nat.cast_mul
attribute [norm_cast] int.coe_nat_mul
attribute [norm_cast] int.cast_mul
attribute [norm_cast] rat.cast_mul
attribute [norm_cast] complex.of_real_mul

attribute [norm_cast] rat.cast_inv
attribute [norm_cast] complex.of_real_inv

attribute [norm_cast] int.coe_nat_div
attribute [norm_cast] rat.cast_div
attribute [norm_cast] complex.of_real_div

attribute [norm_cast] nat.cast_min
attribute [norm_cast] int.cast_min
attribute [norm_cast] rat.cast_min

attribute [norm_cast] nat.cast_max
attribute [norm_cast] int.cast_max
attribute [norm_cast] rat.cast_max

attribute [norm_cast] int.coe_nat_abs
attribute [norm_cast] int.cast_abs
attribute [norm_cast] rat.cast_abs

attribute [norm_cast] nat.cast_pow
attribute [norm_cast] int.coe_nat_pow
attribute [norm_cast] int.cast_pow
attribute [norm_cast] rat.cast_pow
attribute [norm_cast] complex.of_real_pow
attribute [norm_cast] complex.of_real_fpow

attribute [norm_cast] nat.cast_bit0
attribute [norm_cast] int.cast_bit0
attribute [norm_cast] rat.cast_bit0
attribute [norm_cast] complex.of_real_bit0

attribute [norm_cast] nat.cast_bit1
attribute [norm_cast] int.cast_bit1
attribute [norm_cast] rat.cast_bit1
attribute [norm_cast] complex.of_real_bit1

attribute [norm_cast] int.coe_nat_bit0
attribute [norm_cast] int.coe_nat_bit1

attribute [norm_cast] enat.top_add
attribute [norm_cast] enat.add_top
attribute [norm_cast] enat.coe_add

/- --------
    IFF
 -------- -/

attribute [norm_cast] int.coe_nat_eq_coe_nat_iff

attribute [norm_cast] nat.cast_eq_zero
attribute [norm_cast] int.coe_nat_eq_zero
attribute [norm_cast] int.cast_eq_zero
attribute [norm_cast] rat.cast_eq_zero
attribute [norm_cast] complex.of_real_eq_zero

attribute [norm_cast] nat.cast_ne_zero
attribute [norm_cast] int.coe_nat_ne_zero
attribute [norm_cast] int.cast_ne_zero
attribute [norm_cast] rat.cast_ne_zero
attribute [norm_cast] complex.of_real_ne_zero

attribute [norm_cast] nat.cast_le
attribute [norm_cast] int.coe_nat_le
attribute [norm_cast] int.cast_le
attribute [norm_cast] rat.cast_le

attribute [norm_cast] nat.cast_lt
attribute [norm_cast] int.coe_nat_lt
attribute [norm_cast] int.cast_lt
attribute [norm_cast] rat.cast_lt

@[norm_cast]
lemma ge_from_le {α} [has_le α] : ∀ (x y : α), x ≥ y ↔ y ≤ x :=
by simp
@[norm_cast]
lemma gt_from_lt {α} [has_lt α] : ∀ (x y : α), x > y ↔ y < x :=
by simp

attribute [norm_cast] nat.cast_pos
attribute [norm_cast] int.coe_nat_pos
attribute [norm_cast] int.cast_pos
attribute [norm_cast] rat.cast_pos

attribute [norm_cast] nat.cast_nonneg
attribute [norm_cast] int.coe_nat_nonneg
attribute [norm_cast] int.cast_nonneg
attribute [norm_cast] rat.cast_nonneg

attribute [norm_cast] int.cast_nonpos
attribute [norm_cast] rat.cast_nonpos

attribute [norm_cast] int.cast_lt_zero
attribute [norm_cast] rat.cast_lt_zero

attribute [norm_cast] nat.cast_inj
attribute [norm_cast] int.coe_nat_inj'
attribute [norm_cast] int.cast_inj
attribute [norm_cast] rat.cast_inj
attribute [norm_cast] complex.of_real_inj

attribute [norm_cast] int.coe_nat_dvd
attribute [norm_cast] enat.coe_le_coe
attribute [norm_cast] enat.coe_lt_coe

attribute [norm_cast] rat.zero_iff_num_zero
attribute [norm_cast] rat.num_ne_zero_of_ne_zero

run_cmd (norm_cast.norm_cast_attr.get_cache >>= tactic.trace)