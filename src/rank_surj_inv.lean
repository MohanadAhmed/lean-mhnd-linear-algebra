import data.complex.basic
import linear_algebra.matrix.nonsingular_inverse
import data.matrix.rank

variables {m n R: Type*}
variables [fintype m][fintype n][decidable_eq m][decidable_eq n]
variables [field R][decidable_eq R]

open matrix
open_locale matrix

lemma rank_mul_unit (A: matrix n n R)(B: matrix m n R) (hA: is_unit A.det):
  (B⬝A).rank = B.rank := begin
  rw [matrix.rank, mul_vec_lin_mul, linear_map.range_comp_of_range_eq_top, ← matrix.rank],
  rw linear_map.range_eq_top,
  intro x,
  use ((A⁻¹).mul_vec_lin ) x,
  rwa [mul_vec_lin_apply, mul_vec_lin_apply, mul_vec_mul_vec, mul_nonsing_inv, one_mul_vec],
end

lemma rank_mul_unit' (A: matrix m m R)(B: matrix m n R) (hA: is_unit A.det):
  (A⬝B).rank = B.rank := begin
  have h: linear_map.ker ((A⬝B).mul_vec_lin) = linear_map.ker (B.mul_vec_lin) ,
  { rw [mul_vec_lin_mul, linear_map.ker_comp_of_ker_eq_bot],
    rw linear_map.ker_eq_bot,
    simp_rw [function.injective, mul_vec_lin_apply],
    intros x y h,
    replace h := congr_arg (λ x, matrix.mul_vec (A⁻¹) x)  h, 
    simp_rw [mul_vec_mul_vec, nonsing_inv_mul A hA, one_mul_vec] at h, 
    exact h, },  
  have hB := linear_map.finrank_range_add_finrank_ker ((B).mul_vec_lin),
  rw [← linear_map.finrank_range_add_finrank_ker ((A⬝B).mul_vec_lin), h, add_left_inj] at hB,
  rw [matrix.rank, matrix.rank, hB],
end