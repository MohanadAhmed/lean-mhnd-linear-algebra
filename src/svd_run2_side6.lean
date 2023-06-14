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
    V₁⬝V₁ᴴ + V₂⬝V₂ᴴ = 1 := 
begin
  intros hAHA V S pn e eb V₁ V₂ Vinv Vbh V₁inv AV₂,
  
  change V₁ with ((reindex eb.symm e.symm) V).to_blocks₁₁,
  change V₂ with ((reindex eb.symm e.symm) V).to_blocks₁₂,
  simp_rw [to_blocks₁₁, to_blocks₁₂],
  simp only [reindex_apply, equiv.symm_symm, submatrix_apply, equiv.sum_empty_apply_inl, 
    equiv.sum_compl_apply_inl, equiv.sum_compl_apply_inr],
  rw mul_eq_one_comm at Vinv,

  funext x y,
  simp_rw [dmatrix.add_apply, mul_apply, of_apply, conj_transpose_apply, of_apply,
     ← conj_transpose_apply],
  simp_rw fintype.sum_subtype_add_sum_subtype pn (λ g, V x g * Vᴴ g y),
  
  rw [← mul_apply, Vinv], 
end


example {m n : ℕ}
  (A : matrix (fin m) (fin n) ℂ) :
  let hAHA : (Aᴴ ⬝ A).is_hermitian := (is_hermitian_transpose_mul_self A),
      V : matrix (fin n) (fin n) ℂ := hAHA.eigenvector_matrix,
      S : matrix (fin n) (fin n) ℝ := diagonal hAHA.eigenvalues,
      pn : fin n → Prop := λ (i : fin n), hAHA.eigenvalues i ≠ 0,
      e : {a // pn a} ⊕ {a // ¬pn a} ≃ fin n := equiv.sum_compl pn,
      Se : matrix ({a // pn a} ⊕ {a // ¬pn a})
        ({a // pn a} ⊕ {a // ¬pn a})
        ℝ :=
        (reindex e.symm e.symm) S,
      S₁₁ : matrix {a // pn a} {a // pn a} ℝ := Se.to_blocks₁₁,
      S₁₂ : matrix {a // pn a} {a // ¬pn a} ℝ := Se.to_blocks₁₂,
      S₂₁ : matrix {a // ¬pn a} {a // pn a} ℝ := Se.to_blocks₂₁,
      S₂₂ : matrix {a // ¬pn a} {a // ¬pn a} ℝ := Se.to_blocks₂₂,
      eb : fin n ⊕ fin 0 ≃ fin n := equiv.sum_empty (fin n) (fin 0),
      V₁ : matrix (fin n) {a // pn a} ℂ :=
        ((reindex eb.symm e.symm) V).to_blocks₁₁,
      V₂ : matrix (fin n) {a // ¬pn a} ℂ :=
        ((reindex eb.symm e.symm) V).to_blocks₁₂,
      Sσ : matrix {a // pn a} {a // pn a} ℝ :=
        diagonal (λ (i : {a // pn a}), real.sqrt (S₁₁ i i)),
      U₁ : matrix (fin m) {a // pn a} ℂ :=
        A ⬝ V₁ ⬝ Sσ⁻¹.map RηC,
      hAAH : (A ⬝ Aᴴ).is_hermitian := (is_hermitian_mul_conj_transpose_self A),
      U : matrix (fin m) (fin m) ℂ := hAAH.eigenvector_matrix,
      pm : fin m → Prop := λ (i : fin m), hAAH.eigenvalues i ≠ 0,
      em : {a // pm a} ⊕ {a // ¬pm a} ≃ fin m := equiv.sum_compl pm,
      ebm : fin m ⊕ fin 0 ≃ fin m := equiv.sum_empty (fin m) (fin 0),
      U₂ : matrix (fin m) {a // ¬pm a} ℂ :=
        ((reindex ebm.symm em.symm) U).to_blocks₁₂
  in S.map RηC = diagonal (coe ∘ hAHA.eigenvalues) →
     Aᴴ ⬝ A = V ⬝ S.map RηC ⬝ Vᴴ →
     S = (reindex e e) (from_blocks S₁₁ S₁₂ S₂₁ S₂₂) →
     S₁₂ = 0 →
     S₂₁ = 0 →
     S₂₂ = 0 →
     V = (reindex eb e) (from_blocks V₁ V₂ vec_empty vec_empty) →
     Aᴴ ⬝ A = V₁ ⬝ S₁₁.map RηC ⬝ V₁ᴴ →
     Sσ⁻¹ = diagonal (λ (i : {a // pn a}), 1 / real.sqrt (S₁₁ i i)) →
     is_unit Sσ.det →
     S₁₁ = diagonal (λ (i : {a // pn a}), hAHA.eigenvalues ↑i) →
     Sσᴴ⁻¹ ⬝ (S₁₁ ⬝ Sσ⁻¹) = 1 →
     Vᴴ ⬝ V = 1 →
     V₁ᴴ ⬝ V₁ = 1 ∧
       V₁ᴴ ⬝ V₂ = 0 ∧
         V₂ᴴ ⬝ V₁ = 0 ∧ V₂ᴴ ⬝ V₂ = 1 →
     S₁₁ = diagonal (λ (i : {a // pn a}), hAHA.eigenvalues ↑i) →
     V₁ᴴ ⬝ V₁ = 1 →
     U₁ᴴ ⬝ U₁ = 1 →
     U₁ ⬝ Sσ.map RηC = A ⬝ V₁ →
     A ⬝ V₂ = 0 →
     A ⬝ Aᴴ ⬝ U₂ = 0 →
     Aᴴ ⬝ U₂ = 0 →
     U₁ᴴ ⬝ U₂ = 0 →
     U₂ᴴ ⬝ U₂ = 1 →
     U₂ᴴ ⬝ U₁ = 0 →
     (from_blocks U₁ U₂ vec_empty vec_empty)ᴴ ⬝
         from_blocks U₁ U₂ vec_empty vec_empty =
       1 →
     (reindex eb (equiv.refl ({a // pn a} ⊕ {a // ¬pn a})))
           (from_blocks V₁ V₂ vec_empty vec_empty) ⬝
         ((reindex eb (equiv.refl ({a // pn a} ⊕ {a // ¬pn a})))
              (from_blocks V₁ V₂ vec_empty vec_empty))ᴴ =
       1 → U₁⬝U₁ᴴ + U₂⬝U₂ᴴ = 1 :=
begin
  intros hAHA V S pn e Se S₁₁ S₁₂ S₂₁ S₂₂ eb V₁ V₂ Sσ U₁ hAAH U pm em ebm U₂ SRηC 
  spectralAHA Sblock hS₁₂ hS₂₁ hS₂₂ Vblock reducedSpectral Sσ_inv Sσ_is_unit_det S₁₁diag threeSs Vinv 
  Vbh S₁₁diag_1 V₁inv U₁inv U₁Sσ AV₂ AAHU₂ AHU₂ U₁HU₂ U₂HU₂ U₂HU₁ this fFinal,
    
end


