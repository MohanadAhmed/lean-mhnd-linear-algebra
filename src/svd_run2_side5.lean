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

lemma matrix.left_mul_inj_of_invertible 
  {m n R: Type*}[fintype m][decidable_eq m][fintype n][decidable_eq n]
  [comm_ring R]
  (P : matrix m m R) [invertible P] :
  function.injective (λ (x : matrix m n R), P ⬝ x) := 
begin
  let hdetP_unit := matrix.is_unit_det_of_invertible P,
  rintros x a hax, 
  replace hax := congr_arg (λ (x : matrix m n R), P⁻¹ ⬝ x) hax,
  simp only [inv_mul_cancel_left_of_invertible] at hax,
  exact hax,
end

lemma eigenvector_matrix_inv_mul_self {m: Type*}[fintype m][decidable_eq m]
  {A: matrix m m ℂ} (hA: is_hermitian A):
  (hA.eigenvector_matrix_inv)⬝(hA.eigenvector_matrix) = 1 := 
begin
  apply_fun hA.eigenvector_matrix.mul,
  rw ← matrix.mul_assoc,
  rw [is_hermitian.eigenvector_matrix_mul_inv, matrix.mul_one, matrix.one_mul],
  exact matrix.left_mul_inj_of_invertible hA.eigenvector_matrix,
end

lemma eigenvector_matrix_conj_transpose_mul_self {m: Type*}[fintype m][decidable_eq m]
  {A: matrix m m ℂ} (hA: is_hermitian A):
  (hA.eigenvector_matrix)ᴴ⬝(hA.eigenvector_matrix) = 1 := 
begin
  rw is_hermitian.conj_transpose_eigenvector_matrix,
  exact eigenvector_matrix_inv_mul_self hA,
end

/-Not NEEDED mul_eq_one_comm is sufficent -/
-- lemma conj_transpose_mul_self_eq_one_iff {m R: Type*}[fintype m][decidable_eq m]
--   [comm_ring R][has_star R]
--   {A: matrix m m R}: Aᴴ⬝A = 1 ↔  A⬝Aᴴ = 1 := 
-- begin
--   -- split,
--   -- intro h,
--   -- have: A⁻¹ = Aᴴ,{rw inv_eq_left_inv, exact h,}, rw ← this, 
--   apply matrix.mul_eq_one_comm ,  
-- end
lemma eigenvalues_nonneg_of_pos_semidef {n: Type*}[fintype n][decidable_eq n] (A: matrix n n ℂ) 
  (hAp: matrix.pos_semidef A) (i: n): 
  0 ≤ hAp.1.eigenvalues i := begin
  sorry,
end
example {m n : ℕ}
  (A : matrix (fin m) (fin n) ℂ) :
  let 
    hAAH : (A ⬝ Aᴴ).is_hermitian := (is_hermitian_mul_conj_transpose_self A),
    U : matrix (fin m) (fin m) ℂ := hAAH.eigenvector_matrix,
    pm : fin m → Prop := λ (i : fin m), hAAH.eigenvalues i ≠ 0,
    em : {a // pm a} ⊕ {a // ¬pm a} ≃ fin m := equiv.sum_compl pm,
    ebm : fin m ⊕ fin 0 ≃ fin m := equiv.sum_empty (fin m) (fin 0),
    U₂ : matrix (fin m) {a // ¬pm a} ℂ := ((reindex ebm.symm em.symm) U).to_blocks₁₂
  in 
    U₂ᴴ ⬝ U₂ = 1 :=
begin
  intros hAAH U pm em ebm U₂,
  change U₂ with ((reindex ebm.symm em.symm) U).to_blocks₁₂,
  change U with hAAH.eigenvector_matrix,

  rw to_blocks₁₂,
  simp only [reindex_apply, equiv.symm_symm, submatrix_apply, equiv.sum_empty_apply_inl, equiv.sum_compl_apply_inr],
  funext x y,
  rw mul_apply,
  simp_rw [of_apply, conj_transpose_apply, of_apply, ← conj_transpose_apply, ←mul_apply,
    eigenvector_matrix_conj_transpose_mul_self], 
  by_cases hxy: x = y, { simp_rw [hxy, one_apply_eq],},
  have : (x: fin m) ≠ y, { by_contra, rw subtype.coe_inj at h, exact hxy h, }, 
  rw [one_apply_ne this, one_apply_ne (hxy)], 
end

example {m n : ℕ}
  (A : matrix (fin m) (fin n) ℂ) 
  (f: (fin m) → (fin m) → ℂ)
  :
  let
    hAHA : (Aᴴ ⬝ A).is_hermitian := (is_hermitian_transpose_mul_self A),
    hAAH : (A ⬝ Aᴴ).is_hermitian := (is_hermitian_mul_conj_transpose_self A),
    U : matrix (fin m) (fin m) ℂ := hAAH.eigenvector_matrix,
    pn : fin n → Prop := λ (i : fin n), hAHA.eigenvalues i ≠ 0,
    pm : fin m → Prop := λ (i : fin m), hAAH.eigenvalues i ≠ 0,
    en : {a // pn a} ⊕ {a // ¬pn a} ≃ fin n := equiv.sum_compl pn,
    em : {a // pm a} ⊕ {a // ¬pm a} ≃ fin m := equiv.sum_compl pm,
    ebn : fin n ⊕ fin 0 ≃ fin n := equiv.sum_empty (fin n) (fin 0),
    ebm : fin m ⊕ fin 0 ≃ fin m := equiv.sum_empty (fin m) (fin 0),
    U₂ : matrix (fin m) {a // ¬pm a} ℂ := ((reindex ebm.symm em.symm) U).to_blocks₁₂,
    U₁ : matrix (fin m) {a // pm a} ℂ := λ i j, f i j
  in 
    U₁ᴴ⬝U₁ = 1 → U₁ᴴ⬝U₂ = 0 → U₂ᴴ ⬝ U₂ = 1 → 
    (from_blocks U₁ U₂ vec_empty vec_empty)ᴴ ⬝ (from_blocks U₁ U₂ vec_empty vec_empty) = 1
    := 
begin
  intros hAHA hAAH U pn pm en em ebn ebm U₂ U₁,
  intros U₁HU₁ U₁HU₂ U₂HU₂,
  have U₂HU₁: U₂ᴴ⬝U₁ = 0,
  { rw [← conj_transpose_conj_transpose U₁, ← conj_transpose_mul, U₁HU₂, conj_transpose_zero], },

  rw from_blocks_conj_transpose,
  rw from_blocks_multiply,
  simp_rw [empty_mul_empty, add_zero, U₁HU₁, U₁HU₂, U₂HU₁, U₂HU₂, from_blocks_one],
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
     A ⬝
         ((reindex eb (equiv.refl ({a // pn a} ⊕ {a // ¬pn a})))
              (from_blocks V₁ V₂ vec_empty vec_empty)) =
       (reindex ebm (equiv.refl ({a // pn a} ⊕ {a // ¬pm a})))
             (from_blocks U₁ U₂ vec_empty vec_empty) ⬝
           from_blocks (Sσ.map RηC) 0 0 0  :=
begin
  intros hAHA V S pn e Se S₁₁ S₁₂ S₂₁ S₂₂ eb V₁ V₂ Sσ U₁ hAAH U pm em ebm U₂ SRηC spectralAHA 
    Sblock hS₁₂ hS₂₁ hS₂₂ Vblock reducedSpectral Sσ_inv S₁₁diag threeSs Vinv Vbh S₁₁diag_1 V₁inv 
      U₁inv U₁Sσ AV₂ AAHU₂ AHU₂ U₁HU₂ U₂HU₂ U₂HU₁ this,
  simp_rw [reindex_apply],
  simp only [equiv.refl_symm, equiv.coe_refl, conj_transpose_submatrix],
  
  
  rw [← submatrix_id_id (from_blocks (Sσ.map RηC) 0 0 0), ← submatrix_mul],

  simp only [from_blocks_multiply, empty_mul_empty, matrix.zero_mul, matrix.mul_zero, 
    add_zero, mul_empty, of_add_of, pi.const_add, empty_add_empty],
  change U₁ with  A ⬝ V₁ ⬝ Sσ⁻¹.map RηC,
  rw [matrix.mul_assoc, ← matrix.map_mul, nonsing_inv_mul, 
    matrix.map_one _ (map_zero RηC) (map_one RηC), matrix.mul_one],
  funext x y,
  rw mul_apply, simp_rw submatrix_apply,
  cases y,
  simp only [equiv.sum_empty_symm_apply, id.def, from_blocks_apply₁₁], rw ← mul_apply,

  simp only [equiv.sum_empty_symm_apply, id.def, from_blocks_apply₁₂, dmatrix.zero_apply],
  rw ← mul_apply, rw AV₂, rw [pi.zero_apply,pi.zero_apply],
  sorry,
  exact function.bijective_id,
  -- admit,
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
      Sσ : matrix {a // pn a} {a // pn a} ℝ :=
        diagonal (λ (i : {a // pn a}), real.sqrt (S₁₁ i i))
  in S.map RηC = diagonal (coe ∘ hAHA.eigenvalues) →
     is_unit Sσ.det :=
begin
  intros hAHA V S pn e Se S₁₁ Sσ SRηC,
  change Sσ with diagonal (λ (i : {a // pn a}), real.sqrt (S₁₁ i i)),
  change S₁₁ with Se.to_blocks₁₁,
  change Se with (reindex e.symm e.symm) S,
  rw [det_diagonal, to_blocks₁₁, is_unit_iff_ne_zero],
  simp only [reindex_apply, equiv.symm_symm, submatrix_diagonal_equiv, of_apply, 
    diagonal_apply_eq, function.comp_app, equiv.sum_compl_apply_inl,
      finset.prod_ne_zero_iff, finset.mem_univ,  forall_true_left, real.sqrt_ne_zero'],
  intro i,
  apply lt_of_le_of_ne,
  sorry,
  exact i.prop.symm,
end


