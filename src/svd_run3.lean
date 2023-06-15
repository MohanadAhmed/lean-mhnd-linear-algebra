import data.matrix.basic
import data.matrix.rank
import data.matrix.notation
import data.fin.vec_notation
import data.complex.basic
import data.real.basic
import linear_algebra.matrix.pos_def
import linear_algebra.matrix.diagonal

open matrix
open_locale matrix big_operators

variables {m n r: ℕ}
variables (A: matrix (fin m) (fin n) ℂ)

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

lemma rank_eq_card_pos_eigs_conj_transpose_mul_self 
  {y: Type*}[fintype y][decidable_eq y] 
  {z: Type*}[fintype z][decidable_eq z] 
  (A: matrix y z ℂ):
  A.rank =  (fintype.card {i // (is_hermitian_transpose_mul_self A).eigenvalues i ≠ 0}) :=
begin
  sorry,
end

lemma rank_eq_card_pos_eigs_self_mul_conj_transpose
  {y: Type*}[fintype y][decidable_eq y] 
  {z: Type*}[fintype z][decidable_eq z] 
  (A: matrix y z ℂ):
  A.rank =  (fintype.card {i // (is_hermitian_mul_conj_transpose_self A).eigenvalues i ≠ 0}) :=
begin
  sorry,
end

noncomputable def ezn1 (hr: r = A.rank) :  
  {a // (is_hermitian_transpose_mul_self A).eigenvalues a ≠ 0} ⊕ 
  {a // ¬(is_hermitian_transpose_mul_self A).eigenvalues a ≠ 0} ≃ 
  (fin r) ⊕ (fin (n - r)) := begin
  have e_pn_r : {a // (is_hermitian_transpose_mul_self A).eigenvalues a ≠ 0} ≃ (fin r), 
  { apply fintype.equiv_fin_of_card_eq,
    symmetry,
    rw [hr, rank_eq_card_pos_eigs_conj_transpose_mul_self], },
  have e_npn_r : {a // ¬((is_hermitian_transpose_mul_self A).eigenvalues a ≠ 0)} ≃ (fin (n - r)), 
  { apply fintype.equiv_of_card_eq,
    rw fintype.card_subtype_compl,
    rw [fintype.card_fin, fintype.card_fin, ← rank_eq_card_pos_eigs_conj_transpose_mul_self, hr], },
  exact equiv_trans_across_sums e_pn_r e_npn_r,
end

-- noncomputable def ezn (hr: r = A.rank) :  
--   {a // (pn A) a} ⊕ {a // ¬(pn A) a} ≃ 
--   (fin r) ⊕ (fin (n - r)) := begin
--   have e_pn_r : {a // (pn A) a} ≃ (fin r), sorry,
--   have e_npn_r : {a // ¬(pn A) a} ≃ (fin (n - r)), sorry,
--   apply equiv_trans_across_sums e_pn_r e_npn_r,
-- end

-- def svdV₁ (A: matrix (fin m) (fin n) ℂ): matrix (fin m) (fin r) ℂ := begin
--   let hAHA := is_hermitian_transpose_mul_self A,
--   let V := (hAHA).eigenvector_matrix,
--   let pn := λ i, hAHA.eigenvalues i ≠ 0, 
--   let en := equiv.sum_compl pn,
--   let ebn := equiv.sum_empty (fin n) (fin 0),
--   exact ((reindex ebn.symm en.symm V).to_blocks₁₁).submatrix id (ezn A),
-- end
-- def svdV₂: matrix (fin m) (fin r) ℂ := sorry
