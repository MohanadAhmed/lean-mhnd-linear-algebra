import data.complex.basic
import linear_algebra.matrix.hermitian
import linear_algebra.matrix.pos_def
import linear_algebra.matrix.determinant
import linear_algebra.matrix.spectrum
import linear_algebra.matrix.nonsingular_inverse
import linear_algebra.matrix.diagonal
import linear_algebra.std_basis
import data.matrix.basic
import data.matrix.rank
import rank_surj_inv
import algebra.star.basic

-- open matrix 
open complex
open_locale matrix big_operators 

variables {m n R: Type*}
variables [fintype m][fintype n][decidable_eq m][decidable_eq n]
variables [field R][is_R_or_C R][partial_order R][star_ordered_ring R][decidable_eq R]

lemma modified_spectral_theorem (A: matrix n n ℂ)(hA: A.is_hermitian) :
  A = (hA.eigenvector_matrix) ⬝ 
    (matrix.diagonal (coe ∘ hA.eigenvalues)) ⬝ hA.eigenvector_matrix_inv := 
begin
  have h := hA.spectral_theorem,
  replace h := congr_arg (λ x, hA.eigenvector_matrix ⬝  x) h,
  simp only at h,
  rw [← matrix.mul_assoc, hA.eigenvector_matrix_mul_inv, matrix.one_mul] at h,
  rwa matrix.mul_assoc,
end

lemma rank_eq_rank_diagonal (A: matrix n n ℂ)(hA: A.is_hermitian) :
  A.rank = (matrix.diagonal ((coe ∘ hA.eigenvalues): n → ℂ)).rank :=     
begin
  nth_rewrite_lhs 0 [modified_spectral_theorem A hA],  
  rw rank_mul_unit,  
  rw rank_mul_unit',
  apply matrix.is_unit_det_of_invertible,
  apply matrix.is_unit_det_of_invertible,
end

noncomputable theory

open linear_map matrix set submodule
open_locale matrix big_operators

lemma rank_diagonal' [decidable_eq m] [decidable_eq R] (w : m → ℂ) :
   linear_map.rank ((diagonal w).to_lin') = fintype.card { i // w i ≠ 0 } :=
begin
  have hu : univ ⊆ {i : m | w i = 0}ᶜ ∪ {i : m | w i = 0}, { rw set.compl_union_self },
  have hd : disjoint {i : m | w i ≠ 0} {i : m | w i = 0} := disjoint_compl_left,
  have B₁ := supr_range_std_basis_eq_infi_ker_proj ℂ (λi:m, ℂ) hd hu (set.to_finite _),
  have B₂ := @infi_ker_proj_equiv ℂ _ _ (λi:m, ℂ) _ _ _ _ (by simp; apply_instance) hd hu,
  rw linear_map.rank,
  rw range_diagonal,
  rw B₁,
  rw ←@rank_fun' ℂ,
  apply linear_equiv.rank_eq,
  apply B₂,
end

lemma rank_diagonal_matrix (w: n → ℂ) :
  ((matrix.diagonal w).rank) = ↑(fintype.card {i // (w i) ≠ 0}) :=
begin
  have hu : univ ⊆ {i : n | w i = 0}ᶜ ∪ {i : n | w i = 0}, { rw set.compl_union_self },
  have hd : disjoint {i : n | w i ≠ 0} {i : n | w i = 0} := disjoint_compl_left,
  have B₁ := supr_range_std_basis_eq_infi_ker_proj ℂ (λi:n, ℂ) hd hu (set.to_finite _),
  have B₂ := @infi_ker_proj_equiv ℂ _ _ (λi:n, ℂ) _ _ _ _ (by simp; apply_instance) hd hu,
  rw matrix.rank, 
  rw ← to_lin'_apply',
  rw range_diagonal,
  rw B₁,
  rw ← finite_dimensional.finrank_fintype_fun_eq_card ℂ,
  apply linear_equiv.finrank_eq,
  apply B₂,
end


lemma rank_eq_count_nonzero_eigs (A: matrix n n ℂ)(hA: A.is_hermitian) :
  A.rank =  ↑(fintype.card {i // (coe∘hA.eigenvalues: n → ℂ) i ≠ 0}) :=
begin   
  rw rank_eq_rank_diagonal A hA,
  rw rank_diagonal_matrix,
end

lemma rank_eq_count_nonzero_eigs' (A: matrix n n ℂ)(hA: A.is_hermitian) :
  A.rank =  (fintype.card {i // (hA.eigenvalues) i ≠ 0}) :=
begin   
  rw rank_eq_rank_diagonal A hA,
  rw rank_diagonal_matrix,
  simp only [of_real_eq_zero, fintype.card_subtype_compl, nat.cast_id],
end

