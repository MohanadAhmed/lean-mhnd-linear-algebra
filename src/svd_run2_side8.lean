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

def equiv_trans_across_sums
  {a b c d: Type*}
  [fintype a][fintype b][fintype c][fintype d]
  [decidable_eq a][decidable_eq b][decidable_eq c][decidable_eq d]
  (e1: a ≃ c)(e2: b ≃ d): (a ⊕ b) ≃ (c ⊕ d) :=
  { to_fun := sum.elim (λ x, sum.inl (e1 x)) (λ x, sum.inr (e2 x)),
    inv_fun := sum.elim (λ x, sum.inl (e1.symm x)) (λ x, sum.inr (e2.symm x)),
    left_inv := by {intro x, cases x, 
      simp only [sum.elim_inl, equiv.symm_apply_apply],
      simp only [sum.elim_inr, equiv.symm_apply_apply], },
    right_inv := by { intro x, cases x,
      simp only [sum.elim_inl, equiv.apply_symm_apply],
      simp only [sum.elim_inr, equiv.apply_symm_apply], }, }

-- lemma x1
--   {a b c d: Type*}
--   [fintype a][fintype b][fintype c][fintype d]
--   [decidable_eq a][decidable_eq b][decidable_eq c][decidable_eq d]
--   (e1: a ≃ c)(e2: b ≃ d)(z: a):
--     (equiv_trans_across_sums e1 e2) (sum.inl z)

/-
sum.elim 
  (λ (i : {a // pn a}), sum.elim (Sσ i) 0) 
  (λ (i : {a // ¬pm a}), sum.elim 0 0) 
    ((⇑(ezm.symm) ∘ sum.inl) i)
    ((⇑(ezn.symm) ∘ sum.inr) j) = 0
-/

--/--
example {m n r : ℕ}
  (A : matrix (fin m) (fin n) ℂ)
  (hrank : r = A.rank) :
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
     A ⬝
         (reindex eb (equiv.refl ({a // pn a} ⊕ {a // ¬pn a})))
           (from_blocks V₁ V₂ vec_empty vec_empty) =
       (reindex ebm (equiv.refl ({a // pn a} ⊕ {a // ¬pm a})))
           (from_blocks U₁ U₂ vec_empty vec_empty) ⬝
         (from_blocks Sσ 0 0 0).map RηC →
     (reindex eb (equiv.refl ({a // pn a} ⊕ {a // ¬pn a})))
           (from_blocks V₁ V₂ vec_empty vec_empty) ⬝
         ((reindex eb (equiv.refl ({a // pn a} ⊕ {a // ¬pn a})))
              (from_blocks V₁ V₂ vec_empty vec_empty))ᴴ =
       1 →
     fintype.card {a // pn a} = r →
     fintype.card {a // pm a} = r →
     fintype.card {a // ¬pm a} = m - r →
     fintype.card {a // ¬pn a} = n - r →
     {a // pn a} ≃ fin r →
     {a // ¬pm a} ≃ fin (m - r) →
     {a // ¬pn a} ≃ fin (n - r) →
     ∀ (ezm : {a // pn a} ⊕ {a // ¬pm a} ≃ fin r ⊕ fin (m - r))
     (ezn : {a // pn a} ⊕ {a // ¬pn a} ≃ fin r ⊕ fin (n - r)),
       A =
         (from_blocks U₁ U₂ vec_empty vec_empty).submatrix (ebm.symm)
               (ezm.symm) ⬝
             ((from_blocks Sσ 0 0 0).submatrix (ezm.symm) (ezn.symm)).map
               RηC ⬝
           ((from_blocks V₁ V₂ vec_empty vec_empty).submatrix (eb.symm)
                (ezn.symm))ᴴ →
       {a // pm a} ≃ {a // pn a} →
       ((from_blocks Sσ 0 0 0).submatrix (ezm.symm)
              (ezn.symm)).to_blocks₁₂ =
           0 ∧
         ((from_blocks Sσ 0 0 0).submatrix (ezm.symm)
                (ezn.symm)).to_blocks₂₁ =
             0 ∧
           ((from_blocks Sσ 0 0 0).submatrix (ezm.symm)
                (ezn.symm)).to_blocks₂₂ =
             0 :=
begin
  intros hAHA V S pn e Se S₁₁ S₁₂ S₂₁ S₂₂ eb V₁ V₂ Sσ U₁ hAAH U pm em ebm U₂ SRηC 
    spectralAHA Sblock hS₁₂ hS₂₁ hS₂₂ Vblock reducedSpectral Sσ_inv Sσ_is_unit_det 
    S₁₁diag threeSs Vinv Vbh S₁₁diag_1 V₁inv U₁inv U₁Sσ AV₂ AAHU₂ AHU₂ U₁HU₂ U₂HU₂ U₂HU₁ this 
    xFinal fFinal card_pn_r card_pm_r card_not_pm_m_sub_r card_not_pn_n_sub_r e_pn_r e_not_pm_r 
      e_not_pn_r ezm ezn Final e_pn_pm,
    clear Vblock reducedSpectral Sσ_inv Sσ_is_unit_det 
    S₁₁diag threeSs Vinv Vbh S₁₁diag_1 V₁inv U₁inv U₁Sσ AV₂ AAHU₂ AHU₂ U₁HU₂ U₂HU₂ U₂HU₁ this 
    xFinal fFinal spectralAHA,
    clear card_pm_r card_not_pm_m_sub_r card_not_pn_n_sub_r Sblock Final,

    simp_rw [to_blocks₁₂, to_blocks₂₁, to_blocks₂₂, ← matrix.ext_iff, submatrix_apply, 
      of_apply, dmatrix.zero_apply, from_blocks, of_apply, pi.zero_apply, 
      sum.elim_zero_zero],
    -- split,
    -- intros i j,
    have x1: ezm = equiv_trans_across_sums e_pn_r e_not_pm_r, sorry,
    have x2: ezn = equiv_trans_across_sums e_pn_r e_not_pn_r, sorry,
    simp_rw [x1, x2, equiv_trans_across_sums, equiv.coe_fn_symm_mk,
       sum.elim_inl, sum.elim_inr, pi.zero_apply, eq_self_iff_true, 
       forall_2_true_iff, and_true],
    -- simp_rw equiv.coe_fn_symm_mk,
    -- simp only [equiv.coe_fn_symm_mk, sum.elim_inl, sum.elim_inr, pi.zero_apply],
    -- simp only [equiv.coe_fn_symm_mk, sum.elim_inl, sum.elim_inr, pi.zero_apply, eq_self_iff_true],
    

      -- simp_rw ← equiv.eq_comp_symm ezn _ _,
      
      -- rw equiv.set.sum_compl_symm_apply,
end
---/
