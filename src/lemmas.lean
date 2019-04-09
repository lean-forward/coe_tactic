import data.complex.basic
import norm_coe

attribute [norm_coe] int.coe_nat_add
attribute [norm_coe] int.coe_nat_mul
attribute [norm_coe] int.coe_nat_succ
attribute [norm_coe] int.coe_nat_eq_coe_nat_iff
attribute [norm_coe] nat.cast_add
attribute [norm_coe] nat.cast_sub
attribute [norm_coe] nat.cast_mul
attribute [norm_coe] nat.cast_le
attribute [norm_coe] nat.cast_lt
attribute [norm_coe] nat.cast_pos
attribute [norm_coe] nat.cast_min
attribute [norm_coe] nat.cast_max
attribute [norm_coe] nat.cast_inj
attribute [norm_coe] nat.cast_eq_zero
attribute [norm_coe] nat.cast_ne_zero
attribute [norm_coe] int.coe_nat_le
attribute [norm_coe] int.coe_nat_lt
attribute [norm_coe] int.coe_nat_inj'
attribute [norm_coe] int.coe_nat_pos
attribute [norm_coe] int.coe_nat_eq_zero
attribute [norm_coe] int.coe_nat_ne_zero
attribute [norm_coe] int.coe_nat_abs --
attribute [norm_coe] int.coe_nat_div
attribute [norm_coe] int.cast_sub_nat_nat
attribute [norm_coe] int.cast_neg_of_nat
attribute [norm_coe] int.cast_add
attribute [norm_coe] int.cast_neg
attribute [norm_coe] int.cast_sub
attribute [norm_coe] int.cast_eq_zero
attribute [norm_coe] int.cast_inj
attribute [norm_coe] int.cast_ne_zero
attribute [norm_coe] int.cast_mul
attribute [norm_coe] int.cast_nonneg
attribute [norm_coe] int.cast_le
attribute [norm_coe] int.cast_lt
attribute [norm_coe] int.cast_nonpos
attribute [norm_coe] int.cast_pos
attribute [norm_coe] int.cast_lt_zero
attribute [norm_coe] int.cast_min
attribute [norm_coe] int.cast_max
attribute [norm_coe] int.cast_abs
attribute [norm_coe] rat.cast_inj
attribute [norm_coe] rat.cast_eq_zero
attribute [norm_coe] rat.cast_ne_zero
attribute [norm_coe] rat.cast_add
attribute [norm_coe] rat.cast_sub
attribute [norm_coe] rat.cast_mul
attribute [norm_coe] rat.cast_inv
attribute [norm_coe] rat.cast_div
attribute [norm_coe] rat.cast_pow
attribute [norm_coe] rat.cast_nonneg
attribute [norm_coe] rat.cast_le
attribute [norm_coe] rat.cast_lt
attribute [norm_coe] rat.cast_nonpos
attribute [norm_coe] rat.cast_pos
attribute [norm_coe] rat.cast_lt_zero
attribute [norm_coe] rat.cast_min
attribute [norm_coe] rat.cast_max
attribute [norm_coe] rat.cast_abs
attribute [norm_coe] complex.of_real_inj
attribute [norm_coe] complex.of_real_eq_zero
attribute [norm_coe] complex.of_real_ne_zero
attribute [norm_coe] complex.of_real_add
attribute [norm_coe] complex.of_real_neg
attribute [norm_coe] complex.of_real_mul
attribute [norm_coe] complex.of_real_inv
attribute [norm_coe] complex.of_real_div
attribute [norm_coe] complex.of_real_fpow

attribute [simp_coe] int.coe_nat_zero
attribute [simp_coe] int.coe_nat_one
attribute [simp_coe] nat.cast_zero
attribute [simp_coe] nat.cast_succ
attribute [simp_coe] nat.cast_one
attribute [simp_coe] nat.cast_bit0
attribute [simp_coe] nat.cast_bit1
attribute [simp_coe] nat.cast_id
attribute [simp_coe] int.cast_zero
attribute [simp_coe] int.cast_coe_nat
attribute [simp_coe] int.cast_coe_nat'
attribute [norm_coe] int.cast_neg_succ_of_nat
attribute [simp_coe] int.cast_one
attribute [simp_coe] int.cast_bit0
attribute [simp_coe] int.cast_bit1
attribute [simp_coe] int.cast_id
attribute [simp_coe] rat.cast_coe_int
attribute [simp_coe] rat.cast_coe_nat
attribute [simp_coe] rat.cast_zero
attribute [simp_coe] rat.cast_one
attribute [simp_coe] rat.cast_neg
attribute [simp_coe] rat.cast_bit0
attribute [simp_coe] rat.cast_bit1
attribute [simp_coe] rat.cast_id
attribute [simp_coe] complex.of_real_zero
attribute [simp_coe] complex.of_real_bit0
attribute [simp_coe] complex.of_real_bit1
attribute [simp_coe] complex.of_real_int_cast
attribute [simp_coe] complex.of_real_nat_cast
attribute [simp_coe] complex.of_real_rat_cast

#check @int.coe_nat_add_out
#check @int.eq_cast
