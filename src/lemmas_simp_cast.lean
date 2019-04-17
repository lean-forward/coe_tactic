import data.complex.basic data.nat.enat
import norm_cast

attribute [simp_cast] nat.cast_zero
attribute [simp_cast] int.coe_nat_zero
attribute [simp_cast] int.cast_zero
attribute [simp_cast] rat.cast_zero
attribute [simp_cast] complex.of_real_zero

attribute [simp_cast] nat.cast_one
attribute [simp_cast] int.coe_nat_one
attribute [simp_cast] int.cast_one
attribute [simp_cast] rat.cast_one
attribute [simp_cast] complex.of_real_one

attribute [simp_cast] nat.cast_id
attribute [simp_cast] int.cast_id
attribute [simp_cast] rat.cast_id

attribute [simp_cast] int.cast_coe_nat
attribute [simp_cast] int.cast_coe_nat'
attribute [simp_cast] rat.cast_coe_nat
attribute [simp_cast] rat.cast_coe_int
attribute [simp_cast] complex.of_real_int_cast
attribute [simp_cast] complex.of_real_nat_cast
attribute [simp_cast] complex.of_real_rat_cast

attribute [simp_cast] enat.coe_zero
attribute [simp_cast] enat.coe_one
attribute [simp_cast] enat.coe_get
