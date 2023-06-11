import data.complex.basic
import linear_algebra.std_basis
import data.matrix.basic
import data.matrix.rank
import data.fin.tuple.sort
import algebra.module.linear_map

open matrix
open complex
open_locale matrix big_operators

lemma range_zero_mat_zero {m n R: Type*}
  [fintype n][fintype m][decidable_eq m][decidable_eq n]
  [comm_ring R] [nontrivial R] {A: matrix m n R} :
  (∀ x, A.mul_vec x = 0) → A = 0 :=
begin
  intro h,
  funext x y, rw [pi.zero_apply,pi.zero_apply],
  let z := λ i, ite (i = y) (1:R) 0,
  
  specialize h z,
  rw function.funext_iff at h,
  specialize h x,
  simp_rw [mul_vec, dot_product, z, mul_boole, finset.sum_ite_eq',
    finset.mem_univ, if_true, pi.zero_apply] at h,
  exact h,
end

theorem matrix.rank_zero_iff_eq_zero {m n: Type*}  {R : Type*}
  [fintype n][fintype m][decidable_eq m][decidable_eq n]
  [field R] [nontrivial R] {A: matrix m n R} :
    A = 0 ↔ A.rank = 0 :=
begin
  split,
  intro h, rw [h, matrix.rank_zero],
  intro h,  
  rw [matrix.rank, finrank_eq_zero, linear_map.range_eq_bot, linear_map.ext_iff] at h,
  simp_rw [mul_vec_lin_apply] at h,
  exact range_zero_mat_zero h,
end

