import data.matrix.basic
import data.matrix.rank
import data.matrix.notation
import data.fin.vec_notation
import data.complex.basic
import data.real.basic
import linear_algebra.matrix.pos_def
import linear_algebra.matrix.nonsingular_inverse
import tactic

open matrix
open_locale matrix big_operators complex_conjugate

def RηC := algebra_map ℝ ℂ
example {m n : ℕ}
  (A : matrix (fin m) (fin n) ℂ) :
  let hAHA : (Aᴴ ⬝ A).is_hermitian := (is_hermitian_transpose_mul_self A),
      V : matrix (fin n) (fin n) ℂ := hAHA.eigenvector_matrix,
      S : matrix (fin n) (fin n) ℝ := diagonal hAHA.eigenvalues,
      pn : fin n → Prop := λ (i : fin n), hAHA.eigenvalues i ≠ 0,
      e : {a // pn a} ⊕ {a // ¬pn a} ≃ fin n := equiv.sum_compl pn,
      eb : fin n ⊕ fin 0 ≃ fin n := equiv.sum_empty (fin n) (fin 0),
      V₁ : matrix (fin n) {a // pn a} ℂ :=
        ((reindex eb.symm e.symm) V).to_blocks₁₁,
      V₂ : matrix (fin n) {a // ¬pn a} ℂ :=
        ((reindex eb.symm e.symm) V).to_blocks₁₂
  in 
     Vᴴ ⬝ V = 1 →
     V₁ᴴ ⬝ V₁ = 1 ∧
       V₁ᴴ ⬝ V₂ = 0 ∧
         V₂ᴴ ⬝ V₁ = 0 ∧ V₂ᴴ ⬝ V₂ = 1 →
     V₁ᴴ ⬝ V₁ = 1 →
     A ⬝ V₂ = 0 →
    ((reindex eb (equiv.refl _)) (from_blocks V₁ V₂ vec_empty vec_empty)) ⬝
    ((reindex eb (equiv.refl _)) (from_blocks V₁ V₂ vec_empty vec_empty))ᴴ = 1 :=
begin
  intros hAHA V S pn e eb V₁ V₂ Vinv Vbh V₁inv AV₂,
  set Z := ((reindex eb (equiv.refl _)) (from_blocks V₁ V₂ vec_empty vec_empty))ᴴ,
  set Y := ((reindex eb (equiv.refl _)) (from_blocks V₁ V₂ vec_empty vec_empty)),
  change Z with ((reindex eb (equiv.refl _)) (from_blocks V₁ V₂ vec_empty vec_empty))ᴴ,
  change Y with ((reindex eb (equiv.refl _)) (from_blocks V₁ V₂ vec_empty vec_empty)),
  rw [conj_transpose_reindex, reindex_apply, reindex_apply, ← submatrix_mul,
    from_blocks_conj_transpose, from_blocks_multiply],
  simp only [mul_empty, of_add_of, pi.const_add, empty_add_empty],
  change V₁ with ((reindex eb.symm e.symm) V).to_blocks₁₁,
  change V₂ with ((reindex eb.symm e.symm) V).to_blocks₁₂,
  simp_rw [to_blocks₁₁, to_blocks₁₂],
  simp only [reindex_apply, equiv.symm_symm, submatrix_apply, equiv.sum_empty_apply_inl, 
    equiv.sum_compl_apply_inl, equiv.sum_compl_apply_inr],
  rw [← submatrix_one_equiv eb.symm, ← from_blocks_one],
  congr,
  rw mul_eq_one_comm at Vinv,

  funext x y,
  simp_rw [dmatrix.add_apply, mul_apply, of_apply, conj_transpose_apply, of_apply,
     ← conj_transpose_apply],
  simp_rw fintype.sum_subtype_add_sum_subtype pn (λ g, V x g * Vᴴ g y),
  
  rw [← mul_apply, Vinv], 
  simp only [equiv.refl_symm, equiv.coe_refl, function.bijective_id],
end