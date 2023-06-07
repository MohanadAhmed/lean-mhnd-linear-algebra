import data.complex.basic
import linear_algebra.matrix.hermitian
import linear_algebra.matrix.pos_def
import linear_algebra.matrix.determinant
import linear_algebra.matrix.spectrum
import linear_algebra.matrix.nonsingular_inverse
import linear_algebra.matrix.diagonal
import data.matrix.basic
import data.matrix.rank
import data.matrix.notation
import data.int.basic
import data.fin.tuple.sort
import algebra.star.basic

open matrix complex
open_locale matrix big_operators complex_conjugate

/-
  Lets prove that for a matrix A, with rank r, the eigenvalues
  of AᴴA sorted in descending order are zero from the (r+1) term.
-/
variables {m n R: Type*}
variables [fintype m][fintype n][decidable_eq m][decidable_eq n]
variables [field R][decidable_eq R]

instance a := complex.star_ordered_ring


variables {f g : n → R} {s t : finset n}
lemma sum_eq_zero_iff_of_zero_eq1 : (∀ i ∈ s, f i = 0) → (∑ i in s, f i = 0 ↔ ∀ i ∈ s, f i = 0) :=
begin
  -- classical,
  -- apply finset.induction_on s,
  -- exact λ _, ⟨λ _ _, false.elim, λ _, rfl⟩,
  -- assume a s ha ih H,
  -- have : ∀ i ∈ s, 0 = f i, from λ _, H _ ∘ finset.mem_insert_of_mem,
  -- rw finset.sum_insert,
  -- -- rw [finset.sum_instert ha, mul_eq_one_iff' (H _ $ finset.mem_insert_self _ _) (finset.one_le_prod' this),
  -- --   forall_mem_insert, ih this]
  intro h,
  split, intro h1, exact h,
  intro hy,
  apply finset.induction_on s,
  simp only [finset.sum_empty],
  intros a q ha has, rw finset.sum_insert ha, rw has, specialize hy a,
  have : ∀ i ∈ q, 0 = f i, {

  },
end

lemma dot_product_star_self_eq_zero' (v: n → ℂ) :
  star v ⬝ᵥ v = 0 ↔ v = 0 := 
begin
  simp_rw [dot_product_comm, dot_product, pi.star_apply, ← star_ring_end_apply,
    complex.mul_conj, ← complex.sq_abs, complex.ext_iff, im_sum, of_real_im, 
    re_sum, of_real_re, zero_re, zero_im, finset.sum_const_zero, eq_self_iff_true, and_true],
    
  rw finset.sum_eq_zero_iff_of_nonneg,
  -- rw finset.sum_eq_zero at h, swap,   
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

lemma modified_spectral_theorem {A: matrix n n ℂ}(hA: A.is_hermitian) :
  A = (hA.eigenvector_matrix) ⬝ 
    (matrix.diagonal (coe ∘ hA.eigenvalues)).mul hA.eigenvector_matrix_inv := 
begin
  have h := hA.spectral_theorem,
  replace h := congr_arg (λ x, hA.eigenvector_matrix ⬝  x) h,
  simp only at h,
  rwa [← matrix.mul_assoc, hA.eigenvector_matrix_mul_inv, matrix.one_mul] at h,
end

lemma rank_mul_unit (A: matrix n n R){B: matrix m n R} (hA: is_unit A.det):
  (B⬝A).rank = B.rank := begin
  rw [matrix.rank, mul_vec_lin_mul, linear_map.range_comp_of_range_eq_top, ← matrix.rank],
  rw linear_map.range_eq_top,
  intro x,
  use ((A⁻¹).mul_vec_lin ) x,
  rwa [mul_vec_lin_apply, mul_vec_lin_apply, mul_vec_mul_vec, mul_nonsing_inv, one_mul_vec],
end

lemma rank_mul_unit' (A: matrix m m R){B: matrix m n R} (hA: is_unit A.det):
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

lemma rank_eq_rank_diagonal (A: matrix n n ℂ)(hA: A.is_hermitian) :
  A.rank = (matrix.diagonal (coe ∘ hA.eigenvalues: n → ℂ )).rank := 
begin
  have X :  
  A = (hA.eigenvector_matrix) ⬝ (matrix.diagonal (coe ∘ hA.eigenvalues)) ⬝ (hA.eigenvector_matrix_inv), 
  { rw matrix.mul_assoc, exact modified_spectral_theorem hA, },
  have: A.rank = ((hA.eigenvector_matrix) ⬝ (matrix.diagonal (coe ∘ hA.eigenvalues)) ⬝ (hA.eigenvector_matrix_inv)).rank, {
    rw X,
  },
  have hE := is_unit_det_of_invertible (hA.eigenvector_matrix),
  have hiE := is_unit_det_of_invertible (hA.eigenvector_matrix_inv),
  
  rw rank_mul_unit (hA.eigenvector_matrix_inv) hiE,
  rw rank_mul_unit' (hA.eigenvector_matrix) hE,
  assumption',
end

lemma rank_eq_count_non_zero_eigs (A: matrix n n ℂ)(hA: A.is_hermitian) :
  let D : matrix n n ℂ := matrix.diagonal (coe ∘ hA.eigenvalues) in 
  A.rank =  ↑(fintype.card {i // hA.eigenvalues i ≠ 0}) := 
begin
  have hx := rank_eq_rank_diagonal A hA,
  intros D,
end

/- lemma zero_eigs_before_rank
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
end -/
