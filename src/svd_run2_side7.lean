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

variables {a b c d: Type*}
variables [fintype a][fintype b][fintype c][fintype d]
variables [decidable_eq a][decidable_eq b][decidable_eq c][decidable_eq d]
variables (e1: a ≃ c)(e2: b ≃ d)

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

lemma submatrix_empty_blocks {m n R: Type*}[comm_ring R]
  [fintype m][fintype n]
  [decidable_eq m][decidable_eq n]
  (A: matrix m n R) :
  (from_blocks (A) (of (function.const (m) vec_empty)) (of vec_empty) (of (function.const (fin 0) vec_empty))
   ).submatrix (equiv.sum_empty m (fin 0)).symm (equiv.sum_empty n (fin 0)).symm = A
:= begin
  funext x y, 
  simp_rw [submatrix_apply, from_blocks, of_apply, equiv.sum_empty_symm_apply, sum.elim_inl],
end

lemma subblocks_eq_one {m R: Type*}
  [comm_ring R][has_star R]
  [fintype m][decidable_eq m]
  {p: m → Prop}[decidable_pred p]
  (V₁: matrix m {a // p a} R)(V₂: matrix m {a // ¬ p a} R) 
  (h₁₁: V₁ᴴ⬝V₁ = 1)(h₁₂: V₁ᴴ⬝V₂ = 0)(h₂₁: V₂ᴴ⬝V₁ = 0)(h₂₂: V₂ᴴ⬝V₂ = 1):
  V₁⬝V₁ᴴ + V₂⬝V₂ᴴ = 1 
:= begin
  let em := equiv.sum_compl p,
  let eb : m ⊕ fin 0 ≃ m := equiv.sum_empty m (fin 0),
  
  set V := ((reindex eb em)) (from_blocks V₁ V₂ vec_empty vec_empty),
  have hV₁ : V₁ = ((reindex eb.symm em.symm) V).to_blocks₁₁, 
  { change V with ((reindex eb em)) (from_blocks V₁ V₂ vec_empty vec_empty),
    rw to_blocks₁₁,
    simp only [reindex_apply, equiv.symm_symm, submatrix_submatrix, equiv.symm_comp_self,
     submatrix_id_id, from_blocks_apply₁₁],
    funext, 
    rw of_apply, },
  have hV₂ : V₂ = ((reindex eb.symm em.symm) V).to_blocks₁₂, 
  { change V with ((reindex eb em)) (from_blocks V₁ V₂ vec_empty vec_empty),
    rw to_blocks₁₂,
    simp only [reindex_apply, equiv.symm_symm, submatrix_submatrix, equiv.symm_comp_self,
     submatrix_id_id, from_blocks_apply₁₂],
    funext, 
    rw of_apply, },

  have VHVeq1 : Vᴴ⬝V = 1, 
  { change V with ((reindex eb em)) (from_blocks V₁ V₂ vec_empty vec_empty),
    simp_rw [reindex_apply, conj_transpose_submatrix, submatrix_mul_equiv],
    rw [from_blocks_conj_transpose, from_blocks_multiply, h₁₁, h₁₂, h₂₁, h₂₂],
    simp only [empty_mul_empty, add_zero, from_blocks_one, submatrix_one_equiv], },
  rw mul_eq_one_comm at VHVeq1,

  simp_rw [hV₁, hV₂, to_blocks₁₁, to_blocks₁₂],
  funext x y,
  simp only [reindex_apply, equiv.symm_symm, submatrix_apply, equiv.sum_empty_apply_inl, equiv.sum_compl_apply_inl,
  equiv.sum_compl_apply_inr, dmatrix.add_apply],
  simp_rw [mul_apply, of_apply, conj_transpose_apply, of_apply],
  simp_rw fintype.sum_subtype_add_sum_subtype p (λ x_1, V x x_1 * star (V y x_1)),
  simp_rw [←conj_transpose_apply, ← mul_apply, VHVeq1 ],
end

lemma subblocks_eq_one_with_equiv
  {m n R: Type*}
  [comm_ring R][has_star R]
  [fintype m][decidable_eq m][fintype n][decidable_eq n]
  {pm: m → Prop}[decidable_pred pm]
  {pn: n → Prop}[decidable_pred pn]
  (V₁: matrix m {a // pn a} R)(V₂: matrix m {a // ¬ pm a} R) 
  (e:  {a // pm a} ≃ {a // pn a})
  (h₁₁: V₁ᴴ⬝V₁ = 1)(h₁₂: V₁ᴴ⬝V₂ = 0)(h₂₁: V₂ᴴ⬝V₁ = 0)(h₂₂: V₂ᴴ⬝V₂ = 1):
  V₁⬝V₁ᴴ + V₂⬝V₂ᴴ = 1 :=
begin
  rw [← submatrix_id_id (V₁⬝V₁ᴴ), ← submatrix_mul_equiv V₁ V₁ᴴ _ e _, ← conj_transpose_submatrix],
  apply subblocks_eq_one _ _ _ _ _ h₂₂,
  rw [conj_transpose_submatrix, ← submatrix_mul, h₁₁, submatrix_one_equiv],
  exact function.bijective_id,
  rw [conj_transpose_submatrix, ← submatrix_id_id (V₂),← submatrix_mul, h₁₂, submatrix_zero, 
    dmatrix.zero_apply],
  exact function.bijective_id,
  rw [← submatrix_id_id (V₂ᴴ), ← submatrix_mul, h₂₁, submatrix_zero, dmatrix.zero_apply],
  exact function.bijective_id,
end

example {m n r: ℕ}
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
       1 →
     A =
       (reindex ebm (equiv.refl ({a // pn a} ⊕ {a // ¬pm a})))
             (from_blocks U₁ U₂ vec_empty vec_empty) ⬝
           (from_blocks Sσ 0 0 0).map RηC ⬝
         ((reindex eb (equiv.refl ({a // pn a} ⊕ {a // ¬pn a})))
              (from_blocks V₁ V₂ vec_empty vec_empty))ᴴ →
     (∃ (U : matrix (fin m) ((fin r) ⊕ (fin (m - r))) ℂ) 
        (Q : matrix ((fin r) ⊕ (fin (m - r))) ((fin r) ⊕ (fin (n - r))) ℝ)
        (V : matrix (fin n) ((fin r) ⊕ (fin (n - r))) ℂ),
        A = U ⬝ Q.map RηC ⬝ Vᴴ ∧
          V ⬝ Vᴴ = 1 ∧
            U ⬝ Uᴴ = 1 ∧
              Uᴴ ⬝ U = 1 ∧
                Vᴴ ⬝ V = 1) := 
                  -- ∀ (i : fin m) (j : fin n), (i:ℕ) ≠ (j:ℕ) → Q i j = 0) :=
begin
  intros hAHA V S pn e Se S₁₁ S₁₂ S₂₁ S₂₂ eb V₁ V₂ Sσ U₁ hAAH U pm em ebm U₂ SRηC 
  spectralAHA Sblock hS₁₂ hS₂₁ hS₂₂ Vblock reducedSpectral Sσ_inv Sσ_is_unit_det S₁₁diag threeSs Vinv Vbh 
  S₁₁diag_1 V₁inv U₁inv U₁Sσ AV₂ AAHU₂ AHU₂ U₁HU₂ U₂HU₂ U₂HU₁ Vbinv fFinal xFinal,
  have A_rank_r: A.rank = r, sorry,
  have card_pn_r: fintype.card {a // pn a} = r,sorry,
  have card_pm_r: fintype.card {a // pm a} = r,sorry,
  have card_not_pm_m_sub_r: fintype.card {a // ¬pm a} = (m - r), 
  { rw [fintype.card_subtype_compl, fintype.card_fin, card_pm_r], },
  have card_not_pn_n_sub_r: fintype.card {a // ¬pn a} = (n - r),
  { rw [fintype.card_subtype_compl, fintype.card_fin, card_pn_r], },
  -- have e_pn_r: {a // pn a} ≃ (fin r), {apply fintype.equiv_fin_of_card_eq card_pn_r,},
  -- have e_not_pm_r: {a // ¬pm a} ≃ (fin (m - r)), 
  -- { apply fintype.equiv_fin_of_card_eq card_not_pm_m_sub_r, },
  -- have e_not_pn_r: {a // ¬pn a} ≃ (fin (n - r)), 
  -- { apply fintype.equiv_fin_of_card_eq card_not_pn_n_sub_r, },
  have ezn : {a // pn a} ⊕ {a // ¬pn a} ≃ (fin r) ⊕ (fin (n - r)), sorry {
    apply equiv_trans_across_sums e_pn_r e_not_pn_r,
  },
  have ezm : {a // pn a} ⊕ {a // ¬pm a} ≃ (fin r) ⊕ (fin (m - r)), sorry {
    exact equiv_trans_across_sums e_pn_r e_not_pm_r,
  },
  have e_pn_pm : {a // pm a} ≃ {a // pn a}, 
  { apply fintype.equiv_of_card_eq,
    rw [card_pn_r, card_pm_r], },

  apply_fun (λ x, x.submatrix id id) at xFinal,
  -- simp only [submatrix_id_id, reindex_apply, equiv.refl_symm, equiv.coe_refl, conj_transpose_submatrix] at xFinal,
  rw submatrix_id_id at xFinal,
  simp only [reindex_apply, equiv.refl_symm, equiv.coe_refl, conj_transpose_submatrix] at xFinal,
  rw ← submatrix_mul_equiv _ _ _ ezn.symm _ at xFinal,
  rw ← submatrix_mul_equiv _ _ _ ezm.symm _ at xFinal,
  simp only [submatrix_submatrix, function.comp.right_id, function.comp.left_id] at xFinal,
  
  use (from_blocks U₁ U₂ vec_empty vec_empty).submatrix (ebm.symm) (ezm.symm),
  use ((from_blocks Sσ 0 0 0)).submatrix (ezm.symm) (ezn.symm),
  use (from_blocks V₁ V₂ vec_empty vec_empty).submatrix (eb.symm) (ezn.symm),
  rw ← submatrix_map (RηC), --rw from_blocks_map,
  -- simp_rw matrix.map_zero RηC (map_zero _),
  simp_rw conj_transpose_submatrix,
  split,
  exact xFinal,
  simp_rw [from_blocks_conj_transpose, submatrix_mul_equiv, from_blocks_multiply,
    empty_mul_empty, mul_empty, empty_mul, of_add_of, pi.const_add, empty_add_empty,
     add_zero, Vbh.1, Vbh.2.1, Vbh.2.2, submatrix_empty_blocks,
    U₁inv, U₁HU₂, U₂HU₁, U₂HU₂, from_blocks_one, submatrix_one_equiv],
  rw subblocks_eq_one V₁ V₂ Vbh.1 Vbh.2.1 Vbh.2.2.1 Vbh.2.2.2,
  rw subblocks_eq_one_with_equiv U₁ U₂ e_pn_pm U₁inv U₁HU₂ U₂HU₁ U₂HU₂,
  simp_rw [eq_self_iff_true, and_true],
  -- simp only [mul_empty, of_add_of, pi.const_add, empty_add_empty],
end

