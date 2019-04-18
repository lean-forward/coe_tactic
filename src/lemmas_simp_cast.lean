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

attribute [simp_cast] nat.cast_bit0
attribute [simp_cast] int.cast_bit0
attribute [simp_cast] rat.cast_bit0
attribute [simp_cast] complex.of_real_bit0

attribute [simp_cast] nat.cast_bit1
attribute [simp_cast] int.cast_bit1
attribute [simp_cast] rat.cast_bit1
attribute [simp_cast] complex.of_real_bit1

@[simp_cast]
lemma int.coe_nat_bit0 (n : ℕ) : (↑(bit0 n) : ℤ) = bit0 ↑n :=
by {unfold bit0, simp}
@[simp_cast]
lemma int.coe_nat_bit1 (n : ℕ) : (↑(bit1 n) : ℤ) = bit1 ↑n :=
by {unfold bit1, unfold bit0, simp}