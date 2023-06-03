import data.complex.basic
import linear_algebra.matrix.hermitian
import linear_algebra.matrix.pos_def
import linear_algebra.matrix.determinant
import linear_algebra.matrix.spectrum
import linear_algebra.matrix.nonsingular_inverse
import linear_algebra.matrix.diagonal
import data.matrix.basic
import data.matrix.rank
import rank_surj_inv
import algebra.star.basic

open matrix complex
open_locale matrix big_operators 

variables {m n R: Type*}
variables [fintype m][fintype n][decidable_eq m][decidable_eq n]
variables [field R][is_R_or_C R][partial_order R][star_ordered_ring R]

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
  apply is_unit_det_of_invertible,
  apply is_unit_det_of_invertible,
end

lemma rank_eq_count_nonzero_eigs (A: matrix n n ℂ)(hA: A.is_hermitian) :
  A.rank =  ↑(fintype.card {i // hA.eigenvalues i ≠ 0}) :=
begin
  sorry,
end