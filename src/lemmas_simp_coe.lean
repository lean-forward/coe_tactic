import data.complex.basic data.nat.enat
import norm_coe

attribute [simp_coe] nat.cast_zero
attribute [simp_coe] int.coe_nat_zero
attribute [simp_coe] int.cast_zero
attribute [simp_coe] rat.cast_zero
attribute [simp_coe] complex.of_real_zero

attribute [simp_coe] nat.cast_one
attribute [simp_coe] int.coe_nat_one
attribute [simp_coe] int.cast_one
attribute [simp_coe] rat.cast_one
attribute [simp_coe] complex.of_real_one

attribute [simp_coe] nat.cast_id
attribute [simp_coe] int.cast_id
attribute [simp_coe] rat.cast_id

attribute [simp_coe] int.cast_coe_nat
attribute [simp_coe] int.cast_coe_nat'
attribute [simp_coe] rat.cast_coe_nat
attribute [simp_coe] rat.cast_coe_int
attribute [simp_coe] complex.of_real_int_cast
attribute [simp_coe] complex.of_real_nat_cast
attribute [simp_coe] complex.of_real_rat_cast

attribute [simp_coe] enat.coe_get