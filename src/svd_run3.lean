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

namespace matrix

variables {m n r: ℕ}
variables {A: matrix (fin m) (fin n) ℂ}
variables {hr: r = A.rank}

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

noncomputable def ezn (hr: r = A.rank) :  
  {a // (is_hermitian_transpose_mul_self A).eigenvalues a ≠ 0} ⊕ 
  {a // ¬(is_hermitian_transpose_mul_self A).eigenvalues a ≠ 0} ≃ (fin r) ⊕ (fin (n - r)) 
:= begin
  have e_pn_r : {a // (is_hermitian_transpose_mul_self A).eigenvalues a ≠ 0} ≃ (fin r), 
  { apply fintype.equiv_fin_of_card_eq,
    symmetry,
    rw [hr, rank_eq_card_pos_eigs_conj_transpose_mul_self], },
  have e_npn_r : 
    {a // ¬((is_hermitian_transpose_mul_self A).eigenvalues a ≠ 0)} ≃ (fin (n - r)),
  { apply fintype.equiv_of_card_eq,
    rw fintype.card_subtype_compl,
    rw [fintype.card_fin, fintype.card_fin, ← rank_eq_card_pos_eigs_conj_transpose_mul_self, hr], },
  exact equiv_trans_across_sums e_pn_r e_npn_r,
end

noncomputable def ezm (hr: r = A.rank) :  
  {a // (is_hermitian_mul_conj_transpose_self A).eigenvalues a ≠ 0} ⊕ 
  {a // ¬(is_hermitian_mul_conj_transpose_self A).eigenvalues a ≠ 0} ≃ (fin r) ⊕ (fin (m - r)) 
:= begin
  have e_pm_r : {a // (is_hermitian_mul_conj_transpose_self A).eigenvalues a ≠ 0} ≃ (fin r), 
  { apply fintype.equiv_fin_of_card_eq,
    symmetry,
    rw [hr, rank_eq_card_pos_eigs_self_mul_conj_transpose], },
  have e_npm_r : 
    {a // ¬((is_hermitian_mul_conj_transpose_self A).eigenvalues a ≠ 0)} ≃ (fin (m - r)),
  { apply fintype.equiv_of_card_eq,
    rw fintype.card_subtype_compl,
    rw [fintype.card_fin, fintype.card_fin, ← rank_eq_card_pos_eigs_self_mul_conj_transpose, hr], },
  exact equiv_trans_across_sums e_pm_r e_npm_r,
end

noncomputable def svdV₁ (hr: r = A.rank): matrix (fin n) (fin r) ℂ := begin
  let hAHA := is_hermitian_transpose_mul_self A,
  let V := (hAHA).eigenvector_matrix,
  let epn := equiv.sum_compl (λ i, hAHA.eigenvalues i ≠ 0),
  let ebn := equiv.sum_empty (fin n) (fin 0),
  let enx : {a // hAHA.eigenvalues a ≠ 0} ≃ (fin r), 
  { apply fintype.equiv_fin_of_card_eq,
    rw [hr, rank_eq_card_pos_eigs_conj_transpose_mul_self], },
  exact ((reindex (equiv.refl _) enx) ((reindex ebn.symm epn.symm V).to_blocks₁₁)),
end

noncomputable def svdV₂ (hr: r = A.rank): matrix (fin n) (fin (n-r)) ℂ := begin
  let hAHA := is_hermitian_transpose_mul_self A,
  let V := (hAHA).eigenvector_matrix,
  let epn := equiv.sum_compl (λ i, hAHA.eigenvalues i ≠ 0),
  let ebn := equiv.sum_empty (fin n) (fin 0),
  let enx : {a // ¬hAHA.eigenvalues a ≠ 0} ≃ (fin (n - r)), 
  { refine fintype.equiv_fin_of_card_eq _,
    rw [fintype.card_subtype_compl, fintype.card_fin, hr, 
    rank_eq_card_pos_eigs_conj_transpose_mul_self], },
  exact ((reindex (equiv.refl _) enx) ((reindex ebn.symm epn.symm V).to_blocks₁₂)),
end

lemma matrix.left_mul_inj_of_invertible 
  {m n: Type*}[fintype m][decidable_eq m][fintype n][decidable_eq n]
  {R: Type*}[comm_ring R]
  (P : matrix m m R) [invertible P] :
  function.injective (λ (x : matrix m n R), P ⬝ x) := 
begin
  let hdetP_unit := matrix.is_unit_det_of_invertible P,
  rintros x a hax, 
  replace hax := congr_arg (λ (x : matrix m n R), P⁻¹ ⬝ x) hax,
  simp only [inv_mul_cancel_left_of_invertible] at hax,
  exact hax,
end

lemma eigenvector_matrix_inv_mul_self {m F: Type*}
  [fintype m][decidable_eq m][is_R_or_C F][decidable_eq F]
  {A: matrix m m F} (hA: is_hermitian A):
  (hA.eigenvector_matrix_inv)⬝(hA.eigenvector_matrix) = 1 := 
begin
  apply_fun hA.eigenvector_matrix.mul,
  rw ← matrix.mul_assoc,
  rw [is_hermitian.eigenvector_matrix_mul_inv, matrix.mul_one, matrix.one_mul],
  exact matrix.left_mul_inj_of_invertible hA.eigenvector_matrix,
end

lemma one_subtype
  {m R: Type*}
  [fintype m][decidable_eq m][comm_ring R]
  {p: m → Prop}[decidable_pred p]: 
  (λ i j: subtype p, (1: matrix m m R) i j) = (1: matrix (subtype p) (subtype p) R) :=
begin
funext x y,
-- rw of_apply,
by_cases hxy: x = y,
rw hxy, rw [one_apply_eq, one_apply_eq],
rw [one_apply_ne hxy, one_apply_ne],
by_contra h,
rw subtype.coe_eq_iff at h,
simp only [ne.def, subtype.coe_eta, embedding_like.apply_eq_iff_eq, exists_prop] at h,
exact hxy h.2,
end

lemma submatrix_equiv_one_subtype
  {m n R: Type*}
  [fintype m][decidable_eq m][fintype n][decidable_eq n][comm_ring R]
  {p: m → Prop}[decidable_pred p] {e: (subtype p) ≃ n}: 
  reindex e e ((λ i j: subtype p, (1: matrix m m R) i j)) = 1 :=
begin
  simp_rw one_subtype,
  simp only [reindex_apply, submatrix_one_equiv],
end

lemma V₁_conj_transpose_mul_V₁: (svdV₁ hr)ᴴ⬝ (svdV₁ hr) = 1 := begin
  simp_rw [svdV₁, to_blocks₁₁, reindex_apply, equiv.symm_symm,
    submatrix_apply, equiv.sum_empty_apply_inl, equiv.sum_compl_apply_inl,
    equiv.refl_symm, equiv.coe_refl, conj_transpose_submatrix],
  rw ← submatrix_mul,
  simp_rw [matrix.mul, dot_product, conj_transpose_apply, of_apply, 
    ←conj_transpose_apply, is_hermitian.conj_transpose_eigenvector_matrix, ← matrix.mul_apply,
    eigenvector_matrix_inv_mul_self, ← reindex_apply, submatrix_equiv_one_subtype],
  exact function.bijective_id,
end

lemma V₂_conj_transpose_mul_V₂: (svdV₂ hr)ᴴ⬝ (svdV₂ hr) = 1 := begin
  simp_rw [svdV₂, to_blocks₁₂, reindex_apply, equiv.symm_symm,
    submatrix_apply, equiv.sum_empty_apply_inl, equiv.sum_compl_apply_inr,
    equiv.refl_symm, equiv.coe_refl, conj_transpose_submatrix],
  rw ← submatrix_mul,
  simp_rw [matrix.mul, dot_product, conj_transpose_apply, of_apply, 
    ←conj_transpose_apply, is_hermitian.conj_transpose_eigenvector_matrix, ← matrix.mul_apply,
    eigenvector_matrix_inv_mul_self, ← reindex_apply, submatrix_equiv_one_subtype],
  exact function.bijective_id,
end

end matrix
