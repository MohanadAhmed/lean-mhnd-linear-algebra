import data.matrix.basic
import data.matrix.rank
import data.matrix.notation
import data.fin.vec_notation
import data.complex.basic
import data.real.basic
import linear_algebra.matrix.pos_def
import tactic

open matrix
open_locale matrix big_operators complex_conjugate
def RηC := algebra_map ℝ ℂ

variables {m n p: Type*}
variables [fintype m][fintype n][fintype p]
variables [decidable_eq m][decidable_eq n][decidable_eq p]
variables {R: Type*} [comm_ring R]

lemma semiconj_RηC : function.semiconj RηC star star :=
begin
  intro x,
  simp_rw [RηC, is_R_or_C.star_def, is_R_or_C.conj_to_real, complex.coe_algebra_map, is_R_or_C.conj_of_real],
end

lemma conj_transpose_real (A: matrix m n ℝ):
  Aᴴ = Aᵀ := 
begin
  funext x y, simp only [conj_transpose_apply, is_R_or_C.star_def, is_R_or_C.conj_to_real, transpose_apply],
end

-- example {m n : ℕ}
--   (A : matrix (fin m) (fin n) ℂ) :
--   let hAHA : (Aᴴ ⬝ A).is_hermitian := (is_hermitian_transpose_mul_self A),
--       V : matrix (fin n) (fin n) ℂ := hAHA.eigenvector_matrix,
--       S : matrix (fin n) (fin n) ℝ := diagonal hAHA.eigenvalues,
--       pn : fin n → Prop := λ (i : fin n), hAHA.eigenvalues i ≠ 0,
--       e : {a // pn a} ⊕ {a // ¬pn a} ≃ fin n := equiv.sum_compl pn,
--       Se : matrix ({a // pn a} ⊕ {a // ¬pn a})
--         ({a // pn a} ⊕ {a // ¬pn a})
--         ℝ :=
--         (reindex e.symm e.symm) S,
--       S₁₁ : matrix {a // pn a} {a // pn a} ℝ := Se.to_blocks₁₁,
--       Sσ : matrix {a // pn a} {a // pn a} ℝ :=
--         diagonal (λ (i : {a // pn a}), real.sqrt (S₁₁ i i))
--   in S₁₁ = diagonal (λ i:{a // pn a}, hAHA.eigenvalues i) :=
-- begin
--   intros hAHA V S pn e Se S₁₁ Sσ,
--   change S₁₁ with Se.to_blocks₁₁,
--   change Se with ((reindex e.symm e.symm) S),
--   rw to_blocks₁₁,
--   simp only [reindex_apply, equiv.symm_symm, submatrix_diagonal_equiv],
--   funext j k, 
--   rw of_apply,
--   by_cases hjk: j = k, rw hjk, 
--   rw [diagonal_apply_eq, diagonal_apply_eq, function.comp_app, equiv.sum_compl_apply_inl],
--   rw [diagonal_apply_ne, diagonal_apply_ne], 
--   exact hjk,
--   simp only [ne.def], exact hjk,
-- end

-- example {m n : ℕ}
--   (A : matrix (fin m) (fin n) ℂ) :
--   let hAHA : (Aᴴ ⬝ A).is_hermitian := (is_hermitian_transpose_mul_self A),
--       V : matrix (fin n) (fin n) ℂ := hAHA.eigenvector_matrix,
--       S : matrix (fin n) (fin n) ℝ := diagonal hAHA.eigenvalues,
--       pn : fin n → Prop := λ (i : fin n), hAHA.eigenvalues i ≠ 0,
--       e : {a // pn a} ⊕ {a // ¬pn a} ≃ fin n := equiv.sum_compl pn,
--       Se : matrix ({a // pn a} ⊕ {a // ¬pn a})
--         ({a // pn a} ⊕ {a // ¬pn a})
--         ℝ :=
--         (reindex e.symm e.symm) S,
--       S₁₁ : matrix {a // pn a} {a // pn a} ℝ := Se.to_blocks₁₁,
--       Sσ : matrix {a // pn a} {a // pn a} ℝ :=
--         diagonal (λ (i : {a // pn a}), real.sqrt (S₁₁ i i))
--   in Sσᴴ⁻¹ ⬝ (S₁₁ ⬝ Sσ⁻¹) = 1 :=
-- begin
--   intros hAHA V S pn e Se S₁₁ Sσ,
--   have Sσ_inv : Sσ⁻¹ = (matrix.diagonal (λ i, (1 / real.sqrt (S₁₁ i i)))), sorry,
--   have S₁₁diag : S₁₁ = diagonal (λ i:{a // pn a}, hAHA.eigenvalues i), sorry,
--   rw [← matrix.conj_transpose_nonsing_inv, Sσ_inv, S₁₁diag, diagonal_conj_transpose,
--     has_trivial_star.star_trivial, diagonal_mul_diagonal, diagonal_mul_diagonal, ← diagonal_one, 
--     diagonal_eq_diagonal_iff],
--   intro i,
--   rw [diagonal_apply_eq, mul_comm, mul_assoc, div_mul_div_comm, one_mul, ← real.sqrt_mul,
--     real.sqrt_mul_self, mul_div_cancel'],
 
-- end

/-
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
        A ⬝ V₁ ⬝ Sσ⁻¹.map RηC
  in S.map RηC = diagonal (coe ∘ hAHA.eigenvalues) →
     Aᴴ ⬝ A = V ⬝ S.map RηC ⬝ Vᴴ →
     S = (reindex e e) (from_blocks S₁₁ S₁₂ S₂₁ S₂₂) →
     S₁₂ = 0 →
     S₂₁ = 0 →
     S₂₂ = 0 →
     V = (reindex eb e) (from_blocks V₁ V₂ vec_empty vec_empty) →
     Aᴴ ⬝ A = V₁ ⬝ S₁₁.map RηC ⬝ V₁ᴴ →
     Vᴴ ⬝ V = 1 →
     V₁ᴴ ⬝ V₁ = 1 ∧
       V₁ᴴ ⬝ V₂ = 0 ∧
         V₂ᴴ ⬝ V₁ = 0 ∧ V₂ᴴ ⬝ V₂ = 1 →
     V₁ᴴ ⬝ V₁ = 1 → U₁ᴴ ⬝ U₁ = 1 :=
begin
  intros hAHA V S pn e Se S₁₁ S₁₂ S₂₁ S₂₂ eb V₁ V₂ Sσ U₁ SRηC 
    spectralAHA Sblock hS₁₂ hS₂₁ hS₂₂ Vblock reducedSpectral Vinv Vbh V₁inv,  
  change U₁ with A ⬝ V₁ ⬝ Sσ⁻¹.map RηC,
  have threeSs :  Sσᴴ⁻¹ ⬝ (S₁₁ ⬝ Sσ⁻¹) = 1, sorry,
  rw [conj_transpose_mul, conj_transpose_mul, matrix.mul_assoc, matrix.mul_assoc, 
    matrix.mul_assoc A, ← matrix.mul_assoc Aᴴ],
  conv_lhs {congr, skip, congr, skip, congr, rw reducedSpectral,},
  rw [matrix.mul_assoc, ← matrix.mul_assoc _ V₁, V₁inv, matrix.one_mul, matrix.mul_assoc V₁,
    ← matrix.mul_assoc _ V₁, V₁inv, matrix.one_mul, ← conj_transpose_map, 
    conj_transpose_nonsing_inv, ← matrix.map_mul, ← matrix.map_mul, threeSs,
    matrix.map_one RηC (map_zero RηC) (map_one RηC)],
  exact  semiconj_RηC,
end
-/

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
      hAAH : (A ⬝ Aᴴ).is_hermitian := _,
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
    --  fintype.card {a // pm a} = fintype.card {a // pn a} →
    --  {a // pm a} ≃ {a // pn a} →
    Aᴴ⬝U₂ = 0 :=
begin
  intros hAHA V S pn e Se S₁₁ S₁₂ S₂₁ S₂₂ eb V₁ V₂ Sσ U₁ hAAH U pm em ebm U₂ SRηC 
    spectralAHA Sblock hS₁₂ hS₂₁ hS₂₂ Vblock reducedSpectral Sσ_inv S₁₁diag threeSs 
    Vinv Vbh S₁₁diag_1 V₁inv U₁inv U₁Sσ AV₂,
  
end


