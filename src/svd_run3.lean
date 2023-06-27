import data.matrix.basic
import data.matrix.rank
import data.matrix.notation
import data.fin.vec_notation
import data.complex.basic
import data.real.basic
import linear_algebra.matrix.pos_def
import linear_algebra.matrix.diagonal


open_locale matrix big_operators

namespace matrix

variables {m n r: ℕ}
variables {A: matrix (fin m) (fin n) ℂ}
variables {hr: r = A.rank}

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

-- noncomputable def ezn (hr: r = A.rank) :  
--   {a // (is_hermitian_transpose_mul_self A).eigenvalues a ≠ 0} ⊕ 
--   {a // ¬(is_hermitian_transpose_mul_self A).eigenvalues a ≠ 0} ≃ (fin r) ⊕ (fin (n - r)) 
-- := begin
--   have e_pn_r : {a // (is_hermitian_transpose_mul_self A).eigenvalues a ≠ 0} ≃ (fin r), 
--   { apply fintype.equiv_fin_of_card_eq,
--     symmetry,
--     rw [hr, rank_eq_card_pos_eigs_conj_transpose_mul_self], },
--   have e_npn_r : 
--     {a // ¬((is_hermitian_transpose_mul_self A).eigenvalues a ≠ 0)} ≃ (fin (n - r)),
--   { apply fintype.equiv_of_card_eq,
--     rw fintype.card_subtype_compl,
--     rw [fintype.card_fin, fintype.card_fin, ← rank_eq_card_pos_eigs_conj_transpose_mul_self, hr], },
--   exact equiv_trans_across_sums e_pn_r e_npn_r,
-- end

-- noncomputable def ezm (hr: r = A.rank) :  
--   {a // (is_hermitian_mul_conj_transpose_self A).eigenvalues a ≠ 0} ⊕ 
--   {a // ¬(is_hermitian_mul_conj_transpose_self A).eigenvalues a ≠ 0} ≃ (fin r) ⊕ (fin (m - r)) 
-- := begin
--   have e_pm_r : {a // (is_hermitian_mul_conj_transpose_self A).eigenvalues a ≠ 0} ≃ (fin r), 
--   { apply fintype.equiv_fin_of_card_eq,
--     symmetry,
--     rw [hr, rank_eq_card_pos_eigs_self_mul_conj_transpose], },
--   have e_npm_r : 
--     {a // ¬((is_hermitian_mul_conj_transpose_self A).eigenvalues a ≠ 0)} ≃ (fin (m - r)),
--   { apply fintype.equiv_of_card_eq,
--     rw fintype.card_subtype_compl,
--     rw [fintype.card_fin, fintype.card_fin, ← rank_eq_card_pos_eigs_self_mul_conj_transpose, hr], },
--   exact equiv_trans_across_sums e_pm_r e_npm_r,
-- end

-- noncomputable def svdV₁ (hr: r = A.rank): matrix (fin n) (fin r) ℂ := begin
--   let hAHA := is_hermitian_transpose_mul_self A,
--   let V := (hAHA).eigenvector_matrix,
--   let epn := equiv.sum_compl (λ i, hAHA.eigenvalues i ≠ 0),
--   let ebn := equiv.sum_empty (fin n) (fin 0),
--   let enx : {a // hAHA.eigenvalues a ≠ 0} ≃ (fin r), 
--   { apply fintype.equiv_fin_of_card_eq,
--     rw [hr, rank_eq_card_pos_eigs_conj_transpose_mul_self], },
--   exact ((reindex (equiv.refl _) enx) ((reindex ebn.symm epn.symm V).to_blocks₁₁)),
-- end

noncomputable def svdV₁ (A: matrix (fin m) (fin n) ℂ): matrix (fin n) (fin A.rank) ℂ := begin
  let hAHA := is_hermitian_transpose_mul_self A,
  let V := (hAHA).eigenvector_matrix,
  let epn := equiv.sum_compl (λ i, hAHA.eigenvalues i ≠ 0),
  let ebn := equiv.sum_empty (fin n) (fin 0),
  let enx : {a // hAHA.eigenvalues a ≠ 0} ≃ (fin A.rank), 
  { apply fintype.equiv_fin_of_card_eq,
    rw [rank_eq_card_pos_eigs_conj_transpose_mul_self], },
  exact ((reindex (equiv.refl _) enx) ((reindex ebn.symm epn.symm V).to_blocks₁₁)),
end

noncomputable def svdV₂ (A: matrix (fin m) (fin n) ℂ): matrix (fin n) (fin (n- A.rank)) ℂ := begin
  let hAHA := is_hermitian_transpose_mul_self A,
  let V := (hAHA).eigenvector_matrix,
  let epn := equiv.sum_compl (λ i, hAHA.eigenvalues i ≠ 0),
  let ebn := equiv.sum_empty (fin n) (fin 0),
  let enx : {a // ¬hAHA.eigenvalues a ≠ 0} ≃ (fin (n - A.rank)), 
  { refine fintype.equiv_fin_of_card_eq _,
    rw [fintype.card_subtype_compl, fintype.card_fin,
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

lemma V₁_conj_transpose_mul_V₁ (A: matrix (fin m) (fin n) ℂ): (A.svdV₁)ᴴ⬝ (A.svdV₁) = 1 := begin
  simp_rw [svdV₁, to_blocks₁₁, reindex_apply, equiv.symm_symm,
    submatrix_apply, equiv.sum_empty_apply_inl, equiv.sum_compl_apply_inl,
    equiv.refl_symm, equiv.coe_refl, conj_transpose_submatrix],
  rw ← submatrix_mul,
  simp_rw [matrix.mul, dot_product, conj_transpose_apply, of_apply, 
    ←conj_transpose_apply, is_hermitian.conj_transpose_eigenvector_matrix, ← matrix.mul_apply,
    eigenvector_matrix_inv_mul_self, ← reindex_apply, submatrix_equiv_one_subtype],
  exact function.bijective_id,
end

lemma V₂_conj_transpose_mul_V₂ (A: matrix (fin m) (fin n) ℂ): (A.svdV₂)ᴴ⬝ (A.svdV₂) = 1 := begin
  simp_rw [svdV₂, to_blocks₁₂, reindex_apply, equiv.symm_symm,
    submatrix_apply, equiv.sum_empty_apply_inl, equiv.sum_compl_apply_inr,
    equiv.refl_symm, equiv.coe_refl, conj_transpose_submatrix],
  rw ← submatrix_mul,
  simp_rw [matrix.mul, dot_product, conj_transpose_apply, of_apply, 
    ←conj_transpose_apply, is_hermitian.conj_transpose_eigenvector_matrix, ← matrix.mul_apply,
    eigenvector_matrix_inv_mul_self, ← reindex_apply, submatrix_equiv_one_subtype],
  exact function.bijective_id,
end

lemma compl_subtypes_ne {z: Type*}[fintype z]{pn: z → Prop} :
     ∀ (i : {a // pn a}) (j : {a // ¬pn a}), (i: z) ≠ (j: z):= 
begin
  intros i j,
  by_contra' h,
  rw subtype.coe_eq_iff at h,
  cases h with hj hx,
  exact j.prop hj,
end

lemma one_subtype_ne
  {m R: Type*}
  [fintype m][decidable_eq m][comm_ring R]
  {p: m → Prop}[decidable_pred p]: 
  (λ (i: subtype p)(j: {a // ¬ p a}), (1: matrix m m R) i j) = 0 :=
begin
  funext x y,
  rw [dmatrix.zero_apply, one_apply_ne],
  apply compl_subtypes_ne,
end

lemma V₁_conj_transpose_mul_V₂: (A.svdV₁)ᴴ⬝(A.svdV₂) = 0 := begin
  simp_rw [svdV₁, svdV₂, to_blocks₁₁, to_blocks₁₂, reindex_apply, equiv.symm_symm, submatrix_apply, 
    equiv.sum_empty_apply_inl, equiv.sum_compl_apply_inl, equiv.refl_symm, equiv.coe_refl, 
    conj_transpose_submatrix, equiv.sum_compl_apply_inr],
  rw ← submatrix_mul,
  simp_rw [matrix.mul, dot_product, conj_transpose_apply, of_apply, 
    ←conj_transpose_apply, is_hermitian.conj_transpose_eigenvector_matrix, ← matrix.mul_apply,
    eigenvector_matrix_inv_mul_self, one_subtype_ne, submatrix_zero, dmatrix.zero_apply],
  exact function.bijective_id,
end

lemma conj_transpose_inj
  {m n R: Type*}
  [fintype m][decidable_eq m][fintype n][decidable_eq n]
  [has_involutive_star R]
  (A B: matrix m n R):
  Aᴴ = Bᴴ → A = B := begin
  simp_rw [← matrix.ext_iff, conj_transpose_apply, star_inj],
  intros h i j, exact (h j i),
end

lemma V₂_conj_tranpose_mul_V₁ (A: matrix (fin m) (fin n) ℂ): (A.svdV₂)ᴴ⬝(A.svdV₁) = 0 := begin
  apply_fun conj_transpose,
  simp only [conj_transpose_mul, conj_transpose_conj_transpose, conj_transpose_zero],
  apply V₁_conj_transpose_mul_V₂,
  exact conj_transpose_inj,
end

noncomputable def svdμ (A: matrix (fin m) (fin n) ℂ): matrix (fin A.rank) (fin A.rank) ℝ := 
begin
  let hAHA := is_hermitian_transpose_mul_self A,
  let V := (hAHA).eigenvector_matrix,
  let epn := equiv.sum_compl (λ i, hAHA.eigenvalues i ≠ 0),
  let enx : {a // hAHA.eigenvalues a ≠ 0} ≃ (fin (A.rank)),
  { apply fintype.equiv_fin_of_card_eq, 
    rw [rank_eq_card_pos_eigs_conj_transpose_mul_self], },
  exact reindex enx enx (diagonal (λ i: {a // hAHA.eigenvalues a ≠ 0}, hAHA.eigenvalues i)),
end

noncomputable def svdσ (A: matrix (fin m) (fin n) ℂ): 
  matrix (fin A.rank) (fin A.rank) ℝ := 
begin
  let hAHA := is_hermitian_transpose_mul_self A,
  let V := (hAHA).eigenvector_matrix,
  let epn := equiv.sum_compl (λ i, hAHA.eigenvalues i ≠ 0),
  let enx : {a // hAHA.eigenvalues a ≠ 0} ≃ (fin (A.rank)),
  { apply fintype.equiv_fin_of_card_eq, 
    rw [rank_eq_card_pos_eigs_conj_transpose_mul_self], },
  exact reindex enx enx (diagonal (λ i: {a // hAHA.eigenvalues a ≠ 0},
    real.sqrt(hAHA.eigenvalues i) )),
end

noncomputable def svdσ_inv (A: matrix (fin m) (fin n) ℂ): 
  matrix (fin A.rank) (fin A.rank) ℝ := 
begin
  let hAHA := is_hermitian_transpose_mul_self A,
  let V := (hAHA).eigenvector_matrix,
  let epn := equiv.sum_compl (λ i, hAHA.eigenvalues i ≠ 0),
  let enx : {a // hAHA.eigenvalues a ≠ 0} ≃ (fin (A.rank)),
  { apply fintype.equiv_fin_of_card_eq, 
    rw [rank_eq_card_pos_eigs_conj_transpose_mul_self], },
  exact reindex enx enx (diagonal (λ i: {a // hAHA.eigenvalues a ≠ 0}, 
    1 / real.sqrt(hAHA.eigenvalues i) )),
end

lemma modified_spectral_theorem 
  {n: Type*}[fintype n][decidable_eq n]
  {A: matrix n n ℂ}(hA: A.is_hermitian) :
  A = (hA.eigenvector_matrix) ⬝ 
    (matrix.diagonal (coe ∘ hA.eigenvalues)).mul hA.eigenvector_matrix_inv := 
begin
  have h := hA.spectral_theorem,
  replace h := congr_arg (λ x, hA.eigenvector_matrix ⬝  x) h,
  simp only at h,
  rwa [← matrix.mul_assoc, hA.eigenvector_matrix_mul_inv, matrix.one_mul] at h,
end

lemma reindex_inj {m n p q R: Type*}
  [fintype m][decidable_eq m][fintype n][decidable_eq n]
  [fintype p][decidable_eq p][fintype q][decidable_eq q]
  [comm_ring R]
  (A B: matrix m n R)(e₁: m ≃ p)(e₂: n ≃ q):
  reindex e₁ e₂ A = reindex e₁ e₂ B → A = B := 
begin
  -- intros h,
  simp_rw [reindex_apply, ← matrix.ext_iff, submatrix_apply],
  intros h i j,
  specialize h (e₁ i) (e₂ j),
  simp [equiv.symm_apply_apply] at h,
  exact h,
end

lemma svdVblock' (A: matrix (fin m) (fin n) ℂ):
  let 
    hAHA := is_hermitian_transpose_mul_self A,
    V := (hAHA).eigenvector_matrix,
    ebn := equiv.sum_empty (fin n) (fin 0),
    epn := equiv.sum_compl (λ i, hAHA.eigenvalues i ≠ 0),
    enx : {a // hAHA.eigenvalues a ≠ 0} ≃ (fin A.rank) := by 
    { apply fintype.equiv_fin_of_card_eq,
      rw rank_eq_card_pos_eigs_conj_transpose_mul_self, },
    eny : {a // ¬hAHA.eigenvalues a ≠ 0} ≃ (fin (n - A.rank)):= by
    { refine fintype.equiv_fin_of_card_eq _,
      rw [fintype.card_subtype_compl, fintype.card_fin, rank_eq_card_pos_eigs_conj_transpose_mul_self], }
  in
  (reindex (equiv.refl _) epn.symm V = 
  
  (reindex ebn (equiv_trans_across_sums enx eny).symm
  (from_blocks A.svdV₁ A.svdV₂ ![] ![]))) := 
begin
  simp_rw [reindex_apply, equiv.refl_symm, equiv.coe_refl, equiv.symm_symm],
  funext i j,
  simp_rw [svdV₁, svdV₂, from_blocks, equiv_trans_across_sums, to_blocks₁₁, to_blocks₁₂,
    submatrix_apply, equiv.coe_fn_mk, equiv.sum_empty_symm_apply],
  cases j,
  simp_rw [sum.elim_inl, of_apply, sum.elim_inl, reindex_apply, equiv.refl_symm, equiv.coe_refl,
    submatrix_apply, of_apply, id.def, equiv.symm_symm, equiv.sum_empty_apply_inl, 
    equiv.sum_compl_apply_inl, equiv.symm_apply_apply],
  simp_rw [sum.elim_inr, of_apply, sum.elim_inl, reindex_apply, equiv.refl_symm, equiv.coe_refl,
    submatrix_apply, sum.elim_inr, submatrix_apply, of_apply, id.def, equiv.symm_symm, 
    equiv.sum_empty_apply_inl, equiv.symm_apply_apply],
end

lemma reindex_symm_reindex {m n p q R: Type*}
  [fintype m][decidable_eq m][fintype n][decidable_eq n]
  [fintype p][decidable_eq p][fintype q][decidable_eq q]
  [comm_ring R]
  (A: matrix m n R)(e₁: m ≃ p)(e₂: n ≃ q):
  (reindex e₁ e₂).symm (reindex e₁ e₂ A) = A := 
begin
simp only [reindex_symm, reindex_apply, equiv.symm_symm, submatrix_submatrix, 
  equiv.symm_comp_self, submatrix_id_id],
end

lemma svdVblock (A: matrix (fin m) (fin n) ℂ):
  let 
    hAHA := is_hermitian_transpose_mul_self A,
    V := (hAHA).eigenvector_matrix,
    ebn := equiv.sum_empty (fin n) (fin 0),
    epn := equiv.sum_compl (λ i, hAHA.eigenvalues i ≠ 0),
    enx : {a // hAHA.eigenvalues a ≠ 0} ≃ (fin A.rank) := by 
    { apply fintype.equiv_fin_of_card_eq,
      rw rank_eq_card_pos_eigs_conj_transpose_mul_self, },
    eny : {a // ¬hAHA.eigenvalues a ≠ 0} ≃ (fin (n - A.rank)):= by
    { refine fintype.equiv_fin_of_card_eq _,
      rw [fintype.card_subtype_compl, fintype.card_fin, rank_eq_card_pos_eigs_conj_transpose_mul_self], }
  in
  V = 
  (reindex (equiv.refl _) epn
  (reindex ebn (equiv_trans_across_sums enx eny).symm
  (from_blocks A.svdV₁ A.svdV₂ ![] ![]))) := 
begin
  intros _ _ _ _ _ _ ,
  apply_fun (λ M, (reindex (equiv.refl _) epn).symm M),
  simp_rw [reindex_symm_reindex],
  apply svdVblock' A,
end

noncomputable def equiv_compl_zero_eigs (A: matrix (fin m) (fin n) ℂ):
  {a // ¬(is_hermitian_transpose_mul_self A).eigenvalues a ≠ 0} ≃ (fin (n - A.rank)) :=
begin
  refine fintype.equiv_fin_of_card_eq _,
  rw [fintype.card_subtype_compl, fintype.card_fin, 
    rank_eq_card_pos_eigs_conj_transpose_mul_self],
end

noncomputable def equiv_non_zero_eigs (A: matrix (fin m) (fin n) ℂ):
  {a // (is_hermitian_transpose_mul_self A).eigenvalues a ≠ 0} ≃ (fin (A.rank)) :=
fintype.equiv_fin_of_card_eq (rank_eq_card_pos_eigs_conj_transpose_mul_self A).symm



lemma svdVblock'' (A: matrix (fin m) (fin n) ℂ):
  (is_hermitian_transpose_mul_self A).eigenvector_matrix = 
  (reindex (equiv.refl _) (equiv.sum_compl (λ i, (is_hermitian_transpose_mul_self A).eigenvalues i ≠ 0))
  (reindex (equiv.sum_empty (fin n) (fin 0)) 
    (equiv_trans_across_sums 
      (fintype.equiv_fin_of_card_eq (rank_eq_card_pos_eigs_conj_transpose_mul_self A).symm)
      (equiv_compl_zero_eigs A)
    ).symm
  (from_blocks A.svdV₁ A.svdV₂ ![] ![]))) := 
begin
  apply svdVblock,
end

lemma reducedSpectral_theorem' (A: matrix (fin m) (fin n) ℂ):
  Aᴴ⬝A = A.svdV₁ ⬝ (A.svdμ.map RηC) ⬝ A.svdV₁ᴴ := 
begin
  
  let hAHA := is_hermitian_transpose_mul_self A,
  let epn := equiv.sum_compl (λ i, hAHA.eigenvalues i ≠ 0),

  simp_rw [svdV₁, svdμ, reindex_apply, equiv.refl_symm, equiv.symm_symm, equiv.coe_refl,
    conj_transpose_submatrix],
  rw ← submatrix_map,
  rw ← submatrix_mul,
  rw ← submatrix_mul,
  rw submatrix_id_id,

  nth_rewrite_lhs 0 ← submatrix_id_id (Aᴴ⬝A),
  nth_rewrite_lhs 0  modified_spectral_theorem (is_hermitian_transpose_mul_self A),
  rw ← is_hermitian.conj_transpose_eigenvector_matrix,
  rw submatrix_mul _ _ _ epn _,
  rw submatrix_mul _ _ _ epn _,
  rw to_blocks₁₁,
  funext i j,
  simp_rw [mul_apply, finset.mul_sum, finset.sum_mul, submatrix_apply, id.def,
   conj_transpose_apply, of_apply, equiv.sum_empty_apply_inl],
  simp_rw fintype.sum_sum_type,
  simp only [equiv.sum_compl_apply_inl, is_R_or_C.star_def, equiv.sum_compl_apply_inr, 
    diagonal_map, map_eq_zero, diagonal_apply, ite_mul, mul_ite, zero_mul, mul_zero],
  simp only [function.comp_app, finset.sum_ite_eq', finset.mem_univ, if_true],
  have hz: ∀ (z: {a // ¬hAHA.eigenvalues a ≠ 0 }), hAHA.eigenvalues ↑z = 0, {
    intro z, 
    exact (not_ne_iff.1 z.prop),
  },
  simp_rw [hz],
  simp only [complex.of_real_zero, zero_mul, mul_zero, if_t_t, finset.sum_const_zero, add_zero],
  simp_rw [if_neg (compl_subtypes_ne _ _), finset.sum_const_zero, add_zero],
  simp_rw [← subtype.ext_iff, finset.sum_ite_eq, finset.mem_univ, if_true],
  simp_rw [RηC, complex.coe_algebra_map],
  dsimp, congr, simp_rw mul_assoc,
  all_goals {apply equiv.bijective},
end

noncomputable def svdU₁ (A: matrix (fin m) (fin n) ℂ): 
  matrix (fin m) (fin (A.rank)) ℂ :=  A ⬝ (A.svdV₁) ⬝ ((A.svdσ⁻¹).map RηC)

lemma mul_star_self_nonneg {n: Type*}[fintype n] 
  (v: n → ℂ): 0 ≤ is_R_or_C.re((star v) ⬝ᵥ v) := 
begin
  simp_rw [is_R_or_C.re_to_complex, dot_product_comm, dot_product, 
    complex.re_sum, pi.star_apply, ← star_ring_end_apply, 
    complex.mul_conj, ← complex.sq_abs, complex.of_real_re],
  apply finset.sum_nonneg,
  intros i hi, simp only [pow_nonneg, map_nonneg],
end

lemma conj_transpose_mul_self_is_pos_semidef {m n: Type*}
  [fintype m][decidable_eq m][fintype n][decidable_eq n]
  (A: matrix m n ℂ): matrix.pos_semidef (Aᴴ⬝A) 
:= begin
  split,
  exact is_hermitian_transpose_mul_self A,
  intro v,
  rw [← mul_vec_mul_vec, dot_product_mul_vec, vec_mul_conj_transpose, 
    is_R_or_C.re_to_complex, star_star], 
  apply mul_star_self_nonneg,
end

lemma eigenvalues_nonneg_of_pos_semidef {n: Type*}[fintype n] [decidable_eq n]
  (A: matrix n n ℂ) (hAp: matrix.pos_semidef A) (i: n): 
  0 ≤ hAp.1.eigenvalues i := begin
  rw  matrix.is_hermitian.eigenvalues_eq,
  apply hAp.2,
end

lemma sing_vals_ne_zero_pos (A: matrix (fin m) (fin n) ℂ) 
  (z: {a // (is_hermitian_transpose_mul_self A).eigenvalues a ≠ 0 }): 
  -- ∀ (z: {a // (is_hermitian_transpose_mul_self A).eigenvalues a ≠ 0 }), 
    0 < real.sqrt((is_hermitian_transpose_mul_self A).eigenvalues ↑z) :=
begin
  -- refine ne_of_gt _,
  rw real.sqrt_pos,
  apply lt_of_le_of_ne,
  apply eigenvalues_nonneg_of_pos_semidef,
  exact (conj_transpose_mul_self_is_pos_semidef A),
  exact z.prop.symm,
end

lemma svdσ_inv_eq (A: matrix (fin m) (fin n) ℂ): (A.svdσ)⁻¹ = A.svdσ_inv := begin
  apply inv_eq_right_inv,
  simp_rw [svdσ, svdσ_inv, reindex_apply, submatrix_mul_equiv, diagonal_mul_diagonal,
    submatrix_diagonal_equiv, mul_one_div_cancel (ne_of_gt (sing_vals_ne_zero_pos A _))],
  exact diagonal_one,
end

lemma threeSσ (A: matrix (fin m) (fin n) ℂ): (A.svdσ)⁻¹ᴴ ⬝ (A.svdμ ⬝ (A.svdσ)⁻¹) = 1 := begin
  have xsms: ∀ (x: ℝ), (0 < real.sqrt(x)) → 
    (1 / real.sqrt(x))*(x * (1 / real.sqrt(x))) = 1, 
  { intros x h, rw real.sqrt_pos at h,
    rw [mul_one_div, div_mul_div_comm, one_mul, real.mul_self_sqrt (le_of_lt h),
      div_self (ne_of_gt h)], },
  rw [svdμ, svdσ_inv_eq A, svdσ_inv],
  simp_rw [reindex_apply, conj_transpose_submatrix, diagonal_conj_transpose, 
    star_trivial, submatrix_mul_equiv, diagonal_mul_diagonal, submatrix_diagonal_equiv, 
    ← diagonal_one, xsms _ (sing_vals_ne_zero_pos A _)],
end

lemma semiconj_RηC : function.semiconj ⇑RηC star star :=
begin
  intro x,
  simp_rw [RηC, is_R_or_C.star_def, is_R_or_C.conj_to_real, complex.coe_algebra_map, is_R_or_C.conj_of_real],
end

lemma U₁_conj_transpose_U₁ (A: matrix (fin m) (fin n) ℂ): (A.svdU₁ᴴ ⬝ A.svdU₁) = 1 
:= begin
rw [svdU₁, conj_transpose_mul, conj_transpose_mul, matrix.mul_assoc, matrix.mul_assoc, 
  matrix.mul_assoc, ← matrix.mul_assoc Aᴴ, reducedSpectral_theorem', matrix.mul_assoc, 
  ← matrix.mul_assoc _ A.svdV₁, V₁_conj_transpose_mul_V₁, matrix.one_mul], 
rw [matrix.mul_assoc A.svdV₁, ← matrix.mul_assoc _ A.svdV₁, V₁_conj_transpose_mul_V₁, 
  matrix.one_mul, ← (conj_transpose_map RηC semiconj_RηC), ← matrix.map_mul, 
  ← matrix.map_mul, threeSσ, matrix.map_one RηC complex.of_real_zero complex.of_real_one],
end


lemma ker_mat_mul_conj_transpose_mul_self
  {m n p: Type*}
  [fintype m][decidable_eq m][fintype n][decidable_eq n]
  [fintype p][decidable_eq p]
  (A: matrix m n ℂ)(B: matrix n p ℂ) :
  (Aᴴ⬝A)⬝B = 0 ↔ A⬝B = 0 := begin
  split,
  intro h,
  funext x y, rw [dmatrix.zero_apply],
  replace h := congr_arg (matrix.mul (Bᴴ)) h,
  rw [matrix.mul_assoc, ← matrix.mul_assoc, ← conj_transpose_mul, matrix.mul_zero, 
    ← matrix.ext_iff] at h,
  replace h := h y y, simp_rw pi.zero_apply at h,
  rw mul_apply at h, simp_rw conj_transpose_apply at h,
  simp_rw [← star_ring_end_apply, mul_comm,
    complex.mul_conj, ← complex.sq_abs, complex.ext_iff, complex.im_sum, complex.of_real_im, 
    complex.re_sum, complex.of_real_re, complex.zero_re, complex.zero_im, 
    finset.sum_const_zero, eq_self_iff_true, and_true] at h,
  rw finset.sum_eq_zero_iff_of_nonneg at h,
  simp_rw [finset.mem_univ, forall_true_left, pow_eq_zero_iff zero_lt_two, 
    absolute_value.eq_zero] at h,
  exact h x,
  intro i, simp only [finset.mem_univ, pow_nonneg, map_nonneg, forall_true_left],
  intro h, 
  rw [matrix.mul_assoc, h, matrix.mul_zero],
end

lemma AV₂_eq_zero (A: matrix (fin m) (fin n) ℂ): A ⬝ A.svdV₂ = 0 := begin
  suffices h : Aᴴ⬝A⬝(A.svdV₂) = 0,
  apply (ker_mat_mul_conj_transpose_mul_self _ _).1 h,
  rw [reducedSpectral_theorem', matrix.mul_assoc, V₁_conj_transpose_mul_V₂,
    matrix.mul_zero],
end

noncomputable def svdU₂ (A: matrix (fin m) (fin n) ℂ): matrix (fin m) (fin (m - A.rank)) ℂ := begin
  let hAAH := is_hermitian_mul_conj_transpose_self A,
  let U := (hAAH).eigenvector_matrix,
  let epm := equiv.sum_compl (λ i, hAAH.eigenvalues i ≠ 0),
  let ebm := equiv.sum_empty (fin m) (fin 0),
  let emx : {a // ¬hAAH.eigenvalues a ≠ 0} ≃ (fin (m - A.rank)) := by 
  { refine fintype.equiv_fin_of_card_eq _,
    rw [fintype.card_subtype_compl, fintype.card_fin,
    rank_eq_card_pos_eigs_self_mul_conj_transpose], },
  exact ((reindex (equiv.refl _) emx) ((reindex ebm.symm epm.symm U).to_blocks₁₂)),
end

lemma ker_mat_mul_self_conj_transpose 
  {m n p: Type*}
  [fintype m][decidable_eq m][fintype n][decidable_eq n]
  [fintype p][decidable_eq p]  
(A: matrix n m ℂ)(B: matrix n p ℂ) :
  (A⬝Aᴴ)⬝B = 0 ↔ Aᴴ⬝B = 0 := begin
  split,
  swap,
  intro h, rw [matrix.mul_assoc, h, matrix.mul_zero],
  intro h,
  rw ← conj_transpose_conj_transpose A at h,
  nth_rewrite 1 conj_transpose_conj_transpose at h,
  exact (ker_mat_mul_conj_transpose_mul_self (Aᴴ) B).1 h,
end

lemma AHU₂_eq_zero (A: matrix (fin m) (fin n) ℂ): Aᴴ ⬝ A.svdU₂ = 0 := begin
  suffices h : A⬝Aᴴ⬝(A.svdU₂) = 0,
  apply (ker_mat_mul_self_conj_transpose  _ _).1 h,

  let hAAH := (is_hermitian_mul_conj_transpose_self A),
  let epm := equiv.sum_compl (λ i, hAAH.eigenvalues i ≠ 0),
  let emx : {a // ¬hAAH.eigenvalues a ≠ 0} ≃ (fin (m - A.rank)),
  { refine fintype.equiv_fin_of_card_eq _,
    rw [fintype.card_subtype_compl, fintype.card_fin,
    rank_eq_card_pos_eigs_self_mul_conj_transpose], },

  have spectralAAH := modified_spectral_theorem (is_hermitian_mul_conj_transpose_self A),
  rw spectralAAH,

  apply_fun matrix.mul hAAH.eigenvector_matrix_inv,
  rw [← matrix.mul_assoc, ← matrix.mul_assoc, eigenvector_matrix_inv_mul_self hAAH,
    matrix.one_mul, matrix.mul_zero, svdU₂],
  
  apply_fun (reindex (equiv.refl _) emx.symm),
  simp only [reindex_apply, equiv.symm_symm, equiv.refl_symm, 
    equiv.coe_refl, submatrix_zero, dmatrix.zero_apply],
  rw [← submatrix_mul_equiv _ _ _ (equiv.refl _) _, submatrix_submatrix,
    equiv.coe_refl, function.comp.right_id, equiv.symm_comp_self, submatrix_id_id,
    submatrix_id_id],
  
  simp only [to_blocks₁₂, submatrix_apply, equiv.sum_empty_apply_inl, 
    equiv.sum_compl_apply_inr],

  simp_rw [matrix.mul, dot_product, of_apply, finset.sum_mul, diagonal_apply, ite_mul,
    zero_mul, finset.sum_ite_eq, finset.mem_univ, if_true, 
    conj_transpose_apply, is_R_or_C.star_def, function.comp_app,
    mul_assoc, ← finset.mul_sum, ← mul_apply],

  funext i j,
  rw eigenvector_matrix_inv_mul_self,
  simp only [dmatrix.zero_apply, mul_eq_zero, complex.of_real_eq_zero],
  by_cases i = j, 
  left, rw h, 
  exact not_not.mp j.prop,
  right, rw one_apply_ne h,
  exact matrix.left_mul_inj_of_invertible _,
end

lemma U₁_conj_transpose_mul_U₂(A: matrix (fin m) (fin n) ℂ): (A.svdU₁ᴴ ⬝ A.svdU₂) = 0 
:= begin
  rw [svdU₁, conj_transpose_mul,  conj_transpose_mul, matrix.mul_assoc, matrix.mul_assoc, 
    AHU₂_eq_zero, matrix.mul_zero, matrix.mul_zero],
end

lemma U₂_conj_transpose_mul_U₂(A: matrix (fin m) (fin n) ℂ): (A.svdU₂ᴴ ⬝ A.svdU₂) = 1 
:= begin
  rw svdU₂,
  simp only [reindex_apply, equiv.symm_symm, equiv.refl_symm, equiv.coe_refl, 
    conj_transpose_submatrix],
  rw ← submatrix_mul, 
  rw to_blocks₁₂,
  simp only [submatrix_apply, equiv.sum_empty_apply_inl, equiv.sum_compl_apply_inr],
  -- funext x y,
  rw ← reindex_apply, 
  
  let hAAH := (is_hermitian_mul_conj_transpose_self A),
  let emx : {a // ¬hAAH.eigenvalues a ≠ 0} ≃ (fin (m - A.rank)),
  { refine fintype.equiv_fin_of_card_eq _,
    rw [fintype.card_subtype_compl, fintype.card_fin,
    rank_eq_card_pos_eigs_self_mul_conj_transpose], },

  apply_fun (reindex emx emx).symm,
  rw [reindex_symm_reindex, reindex_symm, reindex_apply, submatrix_one_equiv],
  simp_rw [matrix.mul, dot_product, conj_transpose_apply, of_apply, 
    ← conj_transpose_apply, ← mul_apply, is_hermitian.conj_transpose_eigenvector_matrix,
    eigenvector_matrix_inv_mul_self],
  funext i j,
  by_cases i = j, rw [h, one_apply_eq, one_apply_eq],
  rw [one_apply_ne, one_apply_ne h],
  rw [ne.def, subtype.coe_inj],
  exact h,
  exact function.bijective_id,
end

end matrix
