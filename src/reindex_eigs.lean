import data.complex.basic
import linear_algebra.matrix.hermitian
import linear_algebra.matrix.pos_def
import linear_algebra.matrix.determinant
import linear_algebra.matrix.spectrum
import linear_algebra.matrix.nonsingular_inverse
import data.matrix.basic
import data.matrix.rank
import data.matrix.notation
import data.int.basic
import data.fin.tuple.sort
import tactic.norm_fin

open matrix complex
open_locale matrix big_operators complex_conjugate

/-
  Lets prove that for a matrix A, with rank r, the eigenvalues
  of AᴴA sorted in descending order are zero from the (r+1) term.
-/
variables {m n R: Type*}
variables [fintype m][fintype n][decidable_eq m][decidable_eq n]
variables [field R][is_R_or_C R][decidable_eq R]

instance a := complex.star_ordered_ring

lemma dot_product_star_self_eq_zero' (v: n → ℂ) :
  star v ⬝ᵥ v = 0 ↔ v = 0 := 
begin
  simp_rw [dot_product_comm, dot_product, pi.star_apply, ← star_ring_end_apply,
    complex.mul_conj, ← complex.sq_abs, complex.ext_iff, im_sum, of_real_im, 
    re_sum, of_real_re, zero_re, zero_im, finset.sum_const_zero, eq_self_iff_true, and_true],
  rw finset.sum_eq_zero_iff_of_nonneg,
  simp_rw [finset.mem_univ, forall_true_left, pow_eq_zero_iff zero_lt_two, 
    absolute_value.eq_zero, function.funext_iff, pi.zero_apply],
  simp only [pow_nonneg, map_nonneg, implies_true_iff],
end

lemma ker_mul_vec_lin_conj_transpose_mul_self' (A : matrix m n ℂ) :
  linear_map.ker (Aᴴ ⬝ A).mul_vec_lin = linear_map.ker (mul_vec_lin A):=
begin
  ext x,
  simp only [linear_map.mem_ker, mul_vec_lin_apply, ←mul_vec_mul_vec],
  split,
  { intro h,
    replace h := congr_arg (dot_product (star x)) h,
    rwa [dot_product_mul_vec, dot_product_zero, vec_mul_conj_transpose, star_star,
      dot_product_star_self_eq_zero'] at h, },
  { intro h, rw [h, mul_vec_zero] },
end

lemma rank_conj_transpose_mul_self' (A : matrix m n ℂ) :
  (Aᴴ ⬝ A).rank = A.rank :=
begin
  dunfold rank,
  refine add_left_injective (finite_dimensional.finrank ℂ (A.mul_vec_lin).ker) _,
  dsimp only,
  rw [linear_map.finrank_range_add_finrank_ker,
    ←((Aᴴ ⬝ A).mul_vec_lin).finrank_range_add_finrank_ker],
  congr' 1,
  rw ker_mul_vec_lin_conj_transpose_mul_self' A,
end

lemma modified_spectral_theorem {A: matrix n n R}(hA: A.is_hermitian) :
  A = (hA.eigenvector_matrix) ⬝ 
    (matrix.diagonal (coe ∘ hA.eigenvalues)).mul hA.eigenvector_matrix_inv := 
begin
  have h := hA.spectral_theorem,
  replace h := congr_arg (λ x, hA.eigenvector_matrix ⬝  x) h,
  simp only at h,
  rwa [← matrix.mul_assoc, hA.eigenvector_matrix_mul_inv, matrix.one_mul] at h,
end

lemma rank_mul_unit (A: matrix n n ℂ)(B: matrix m n ℂ) (hA: is_unit A.det):
  (B⬝A).rank = B.rank := begin
  rw [matrix.rank, mul_vec_lin_mul, linear_map.range_comp_of_range_eq_top, ← matrix.rank],
  rw linear_map.range_eq_top,
  intro x,
  use ((A⁻¹).mul_vec_lin ) x,
  rwa [mul_vec_lin_apply, mul_vec_lin_apply, mul_vec_mul_vec, mul_nonsing_inv, one_mul_vec],
end

lemma zero_eigs_before_rank
  {m n: ℕ}
  [ne_zero m][ne_zero n]
  {i: fin n}
  {A: matrix (fin m) (fin n) ℂ}
  :
  let 
    eigs := (is_hermitian_transpose_mul_self A).eigenvalues,
    ei := tuple.sort(eigs) i in
  (↑i < A.rank) →  eigs ei = 0 := 
begin
  -- haveI := complex.star_ordered_ring,
  intros eigs ei,
  -- intro h,
  rw ← rank_conj_transpose_mul_self A,

  have h1 := modified_spectral_theorem (is_hermitian_transpose_mul_self A),
  rw h1,
end
