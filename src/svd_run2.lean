import data.matrix.basic
import data.matrix.rank
import data.matrix.notation
import data.fin.vec_notation
import data.complex.basic
import data.real.basic
import linear_algebra.matrix.pos_def
import tactic
import linear_algebra.matrix.diagonal
import linear_algebra.matrix.dual

open matrix
open_locale matrix big_operators

instance iC := complex.star_ordered_ring

variables {m n p: Type*}
variables [fintype m][decidable_eq m][fintype n][decidable_eq n][fintype p][decidable_eq p]

lemma compl_subtypes_ne {z: Type*}[fintype z]{pn: z → Prop} :
     ∀ (i : {a // pn a}) (j : {a // ¬pn a}), (i: z) ≠ (j: z):= 
begin
  intros i j,
  by_contra' h,
  rw subtype.coe_eq_iff at h,
  cases h with hj hx,
  exact j.prop hj,
end

def RηC := algebra_map ℝ ℂ
lemma semiconj_RηC : function.semiconj ⇑RηC star star :=
begin
  intro x,
  simp_rw [RηC, is_R_or_C.star_def, is_R_or_C.conj_to_real, complex.coe_algebra_map, is_R_or_C.conj_of_real],
end

lemma mul_star_self_nonneg (v: n → ℂ): 0 ≤ is_R_or_C.re((star v) ⬝ᵥ v) := 
begin
  simp_rw [is_R_or_C.re_to_complex, dot_product_comm, dot_product, 
    complex.re_sum, pi.star_apply, ← star_ring_end_apply, 
    complex.mul_conj, ← complex.sq_abs, complex.of_real_re],
  apply finset.sum_nonneg,
  intros i hi, simp only [pow_nonneg, map_nonneg],
end

lemma conj_transpose_mul_self_is_pos_semidef (A: matrix m n ℂ):
     matrix.pos_semidef (Aᴴ⬝A) 
:= begin
  split,
  exact is_hermitian_transpose_mul_self A,
  intro v,
  rw [← mul_vec_mul_vec, dot_product_mul_vec, vec_mul_conj_transpose, 
    is_R_or_C.re_to_complex, star_star], 
  apply mul_star_self_nonneg,
end

lemma eigenvalues_nonneg_of_pos_semidef (A: matrix n n ℂ) 
  (hAp: matrix.pos_semidef A) (i: n): 
  0 ≤ hAp.1.eigenvalues i := begin
  rw  matrix.is_hermitian.eigenvalues_eq,
  apply hAp.2,
end

lemma matrix.left_mul_inj_of_invertible {R: Type*}[comm_ring R](P : matrix m m R) [invertible P] :
  function.injective (λ (x : matrix m n R), P ⬝ x) := 
begin
  let hdetP_unit := matrix.is_unit_det_of_invertible P,
  rintros x a hax, 
  replace hax := congr_arg (λ (x : matrix m n R), P⁻¹ ⬝ x) hax,
  simp only [inv_mul_cancel_left_of_invertible] at hax,
  exact hax,
end

lemma ker_mat_mul_conj_transpose_mul_self (A: matrix m n ℂ)(B: matrix n p ℂ) :
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

lemma ker_mat_mul_self_conj_transpose (A: matrix n m ℂ)(B: matrix n p ℂ) :
  (A⬝Aᴴ)⬝B = 0 ↔ Aᴴ⬝B = 0 := begin
  split,
  swap,
  intro h, rw [matrix.mul_assoc, h, matrix.mul_zero],
  intro h,
  rw ← conj_transpose_conj_transpose A at h,
  nth_rewrite 1 conj_transpose_conj_transpose at h,
  exact (ker_mat_mul_conj_transpose_mul_self (Aᴴ) B).1 h,
end

lemma modified_spectral_theorem {A: matrix n n ℂ}(hA: A.is_hermitian) :
  A = (hA.eigenvector_matrix) ⬝ 
    (matrix.diagonal (coe ∘ hA.eigenvalues)).mul hA.eigenvector_matrix_inv := 
begin
  have h := hA.spectral_theorem,
  replace h := congr_arg (λ x, hA.eigenvector_matrix ⬝  x) h,
  simp only at h,
  rwa [← matrix.mul_assoc, hA.eigenvector_matrix_mul_inv, matrix.one_mul] at h,
end

lemma eigenvector_matrix_inv_mul_self {A: matrix m m ℂ} (hA: is_hermitian A):
  (hA.eigenvector_matrix_inv)⬝(hA.eigenvector_matrix) = 1 := 
begin
  apply_fun hA.eigenvector_matrix.mul,
  rw ← matrix.mul_assoc,
  rw [is_hermitian.eigenvector_matrix_mul_inv, matrix.mul_one, matrix.one_mul],
  exact matrix.left_mul_inj_of_invertible hA.eigenvector_matrix,
end

lemma eigenvector_matrix_conj_transpose_mul_self {A: matrix m m ℂ} (hA: is_hermitian A):
  (hA.eigenvector_matrix)ᴴ⬝(hA.eigenvector_matrix) = 1 := 
begin
  rw is_hermitian.conj_transpose_eigenvector_matrix,
  exact eigenvector_matrix_inv_mul_self hA,
end

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


lemma rank_mul_unit {R: Type*}[comm_ring R] (A: matrix n n R){B: matrix m n R} (hA: is_unit A.det):
  (B⬝A).rank = B.rank := begin
  rw [matrix.rank, mul_vec_lin_mul, linear_map.range_comp_of_range_eq_top, ← matrix.rank],
  rw linear_map.range_eq_top,
  intro x,
  use ((A⁻¹).mul_vec_lin ) x,
  rwa [mul_vec_lin_apply, mul_vec_lin_apply, mul_vec_mul_vec, mul_nonsing_inv, one_mul_vec],
end

lemma rank_mul_unit'{R: Type*}[field R] (A: matrix m m R){B: matrix m n R} (hA: is_unit A.det):
  (A⬝B).rank = B.rank := begin
  have h: linear_map.ker ((A⬝B).mul_vec_lin) = linear_map.ker (B.mul_vec_lin) ,
  { rw [mul_vec_lin_mul, linear_map.ker_comp_of_ker_eq_bot],
    rw linear_map.ker_eq_bot,
    simp_rw [function.injective, mul_vec_lin_apply],
    intros x y h,
    replace h := congr_arg (λ x, matrix.mul_vec (A⁻¹) x)  h, 
    simp_rw [mul_vec_mul_vec, nonsing_inv_mul A hA, one_mul_vec] at h, 
    exact h, },  
  have hB := linear_map.finrank_range_add_finrank_ker ((B).mul_vec_lin),
  rw [← linear_map.finrank_range_add_finrank_ker ((A⬝B).mul_vec_lin), h, add_left_inj] at hB,
  rw [matrix.rank, matrix.rank, hB],
end

lemma rank_eq_rank_diagonal (A: matrix n n ℂ)(hA: A.is_hermitian) :
  A.rank = (matrix.diagonal (coe ∘ hA.eigenvalues: n → ℂ )).rank := 
begin
  nth_rewrite_lhs 0 modified_spectral_theorem hA,

  have hE := is_unit_det_of_invertible (hA.eigenvector_matrix),
  have hiE := is_unit_det_of_invertible (hA.eigenvector_matrix_inv),
  
  rw rank_mul_unit' (hA.eigenvector_matrix) hE,
  rw rank_mul_unit (hA.eigenvector_matrix_inv) hiE,
  assumption',
end

lemma rank_diagonal_matrix{Z: Type*}[field Z][decidable_eq Z] (w: n → Z) :
  ((matrix.diagonal w).rank) = ↑(fintype.card {i // (w i) ≠ 0}) :=
begin
  have hu : set.univ ⊆ {i : n | w i = 0}ᶜ ∪ {i : n | w i = 0}, { rw set.compl_union_self },
  have hd : disjoint {i : n | w i ≠ 0} {i : n | w i = 0} := disjoint_compl_left,
  have B₁ := linear_map.supr_range_std_basis_eq_infi_ker_proj Z (λi:n, Z) hd hu (set.to_finite _),
  have B₂ := @linear_map.infi_ker_proj_equiv Z _ _ (λi:n, Z) _ _ _ _ (by simp; apply_instance) hd hu,
  rw matrix.rank,
  rw ← to_lin'_apply',
  rw range_diagonal,
  rw B₁,
  rw ← finite_dimensional.finrank_fintype_fun_eq_card Z,
  apply linear_equiv.finrank_eq,
  apply B₂,
end

lemma rank_eq_count_non_zero_eigs (A: matrix n n ℂ)(hA: A.is_hermitian) :
  A.rank =  ↑(fintype.card {i // hA.eigenvalues i ≠ 0}) := 
begin
  rw [rank_eq_rank_diagonal A hA, rank_diagonal_matrix],
  simp_rw [fintype.card_subtype_compl, complex.of_real_eq_zero],
end

lemma rank_eq_card_pos_eigs_conj_transpose_mul_self (A: matrix m n ℂ):
  A.rank =  (fintype.card {i // (is_hermitian_transpose_mul_self A).eigenvalues i ≠ 0}) :=
begin
  rw ← rank_conj_transpose_mul_self,
  apply rank_eq_count_non_zero_eigs,
end

lemma rank_eq_card_pos_eigs_self_mul_conj_transpose (A: matrix m n ℂ):
  A.rank =  (fintype.card {i // (is_hermitian_mul_conj_transpose_self A).eigenvalues i ≠ 0}) :=
begin
  rw ← rank_self_mul_conj_transpose,
  apply rank_eq_count_non_zero_eigs,
end

--/-!
lemma svd_decompose{m n r: ℕ} (A: matrix (fin m) (fin n) ℂ) (hrank: r = A.rank): 
∃ 
  (U: matrix (fin m) (fin r ⊕ fin (m - r)) ℂ)
  -- (σVals : fin r → ℝ)
  (Q: matrix (fin r ⊕ fin (m - r)) (fin r ⊕ fin (n - r)) ℝ)
  (V: matrix (fin n) (fin r ⊕ fin (n - r)) ℂ), 
  -- let Q: matrix (fin r ⊕ fin (m - r)) (fin r ⊕ fin (n - r)) ℝ 
    -- := from_blocks (diagonal σVals) 0 0 0 in
    A = U⬝(Q.map RηC)⬝Vᴴ ∧ 
    V⬝Vᴴ = 1 ∧
    U⬝Uᴴ = 1 ∧
    Uᴴ⬝U = 1 ∧ 
    Vᴴ⬝V = 1 ∧ Q.to_blocks₁₂ = 0 ∧ Q.to_blocks₂₁ = 0 ∧  Q.to_blocks₂₂ = 0 := 
begin
  let hAHA := is_hermitian_transpose_mul_self A,
  let V := hAHA.eigenvector_matrix,
  let S := diagonal hAHA.eigenvalues,
  have SRηC : S.map RηC = diagonal (coe ∘ hAHA.eigenvalues),
  sorry 
  { change S with diagonal hAHA.eigenvalues,
   rw [matrix.diagonal_map (map_zero _), RηC, complex.coe_algebra_map],},
  have spectralAHA : (Aᴴ⬝A) = V⬝ S.map RηC ⬝ Vᴴ, 
  sorry 
  { change V with hAHA.eigenvector_matrix,
    rw [SRηC, matrix.mul_assoc, matrix.is_hermitian.conj_transpose_eigenvector_matrix],
    apply modified_spectral_theorem hAHA, },

  let pn := λ i, hAHA.eigenvalues i ≠ 0,
  let e := equiv.sum_compl pn,

  let Se := reindex e.symm e.symm (S),
  let S₁₁ := Se.to_blocks₁₁,
  let S₁₂ := Se.to_blocks₁₂,
  let S₂₁ := Se.to_blocks₂₁,
  let S₂₂ := Se.to_blocks₂₂,
  
  have Sblock : S = reindex e e (from_blocks S₁₁ S₁₂ S₂₁ S₂₂), 
  sorry 
  { apply_fun reindex e.symm e.symm,
    simp only [reindex_apply, equiv.symm_symm, submatrix_submatrix, 
        equiv.symm_comp_self, submatrix_id_id],
    funext i j,
    cases i; { cases j; refl,},  },
  
  have hS₁₁: S₁₁ = diagonal (λ i: {a // pn a}, hAHA.eigenvalues i),
  sorry
  { change S₁₁ with Se.to_blocks₁₁,
    change Se with reindex e.symm e.symm (S),
    change e with equiv.sum_compl pn,
    change S with diagonal hAHA.eigenvalues,
    
    rw to_blocks₁₁,
    simp only [reindex_apply, equiv.symm_symm, submatrix_diagonal_equiv],
    funext x y,
    by_cases h: x =y,
    simp_rw [h, of_apply, diagonal_apply_eq, function.comp_apply, equiv.sum_compl_apply_inl],
    rwa [of_apply, diagonal_apply_ne, diagonal_apply_ne], 
    rwa [ne.def, sum.inl.inj_iff], },

  have hS₁₂ : S₁₂ = 0, 
  sorry 
  { change S₁₂ with (reindex e.symm e.symm (diagonal hAHA.eigenvalues)).to_blocks₁₂,
    funext i j,
    rw [dmatrix.zero_apply, to_blocks₁₂], 
    dsimp,
    rw diagonal_apply_ne,
    apply compl_subtypes_ne, },

  have hS₂₁ : S₂₁ = 0, 
  sorry 
  { change S₂₁ with (reindex e.symm e.symm (diagonal hAHA.eigenvalues)).to_blocks₂₁,
    funext i j,
    rw [dmatrix.zero_apply, to_blocks₂₁], 
    dsimp,
    rw diagonal_apply_ne',
    apply compl_subtypes_ne, },
  have hS₂₂ : S₂₂ = 0, 
  sorry 
  { change S₂₂ with (reindex e.symm e.symm (diagonal hAHA.eigenvalues)).to_blocks₂₂,
    funext i j,
    rw [dmatrix.zero_apply, to_blocks₂₂], 
    dsimp,
    by_cases ↑i = ↑j, rw h, rw diagonal_apply_eq,
    have ha := j.prop, 
    change pn with (λ i, hAHA.eigenvalues i ≠ 0) at ha,
    dsimp at ha,
    exact (not_not.1 ha),
    apply diagonal_apply_ne,
    exact h, },

  let eb : (fin n) ⊕ (fin 0) ≃ (fin n) , { exact equiv.sum_empty (fin n) (fin 0) },
  let V₁ := ((reindex eb.symm e.symm) V).to_blocks₁₁,
  let V₂ := ((reindex eb.symm e.symm) V).to_blocks₁₂,
  have Vblock : V = (reindex eb e (from_blocks V₁ V₂ ![] ![])), 
  sorry 
  {  apply_fun (reindex eb.symm e.symm),
     simp only [reindex_apply, equiv.symm_symm, submatrix_submatrix, 
          equiv.symm_comp_self, submatrix_id_id],
     funext i j,
     cases i, cases j, refl, refl,
     rw submatrix_apply, 
     cases j;
     fin_cases i, },
  have reducedSpectral : Aᴴ⬝A = V₁⬝(S₁₁.map RηC)⬝(V₁ᴴ), 
  sorry 
  {  simp_rw [(spectralAHA), Vblock, Sblock, reindex_apply, ← submatrix_map],
     rw [conj_transpose_submatrix,  from_blocks_conj_transpose],
     rw [hS₁₂, hS₂₁, hS₂₂],
     rw from_blocks_map,
     simp_rw (matrix.map_zero _ (map_zero RηC)),
     rw ← submatrix_mul,
     rw ← submatrix_mul,
  
     simp_rw [from_blocks_multiply],
     simp only [matrix.mul_zero, matrix.zero_mul, zero_add, add_zero],
     simp_rw [matrix.mul_empty, matrix.empty_mul],
     rw ← reindex_apply,
     apply_fun reindex eb.symm eb.symm,
     simp only [reindex_apply, equiv.symm_symm, submatrix_submatrix, 
          equiv.symm_comp_self, submatrix_id_id],
     funext i j,
     cases i, cases j, 
     rw from_blocks_apply₁₁,
     rw submatrix_apply,
     rw equiv.sum_empty_apply_inl,
     rw equiv.sum_empty_apply_inl,
     fin_cases j, fin_cases i,
     exact equiv.bijective e.symm,
     exact equiv.bijective e.symm, },

  have diagnz : ∀(i: {a // pn a}), 0 < hAHA.eigenvalues i,
  sorry 
  { intro i,
    refine lt_of_le_of_ne _ (i.prop.symm),
    exact eigenvalues_nonneg_of_pos_semidef _ (conj_transpose_mul_self_is_pos_semidef A) _, },

  let Sσ := diagonal (λ i: {a // pn a}, real.sqrt (hAHA.eigenvalues i)),
  have Sσ_inv : Sσ⁻¹ = (matrix.diagonal (λ i, (1 / real.sqrt (hAHA.eigenvalues i)))), 
  sorry 
  { rw inv_eq_right_inv,
    rw [matrix.diagonal_mul_diagonal, ← diagonal_one, diagonal_eq_diagonal_iff],
    intro i,
    rw mul_one_div_cancel,
    apply real.sqrt_ne_zero'.2 (diagnz i), },
  
  have Sσ_is_unit_det: is_unit Sσ.det, 
  sorry 
  { change Sσ with diagonal (λ i: {a // pn a}, real.sqrt (hAHA.eigenvalues i)),
    rw [det_diagonal, is_unit_iff_ne_zero],
    simp only [finset.prod_ne_zero_iff, finset.mem_univ,  forall_true_left, real.sqrt_ne_zero'],
    exact diagnz, },
  -- have S₁₁diag : S₁₁ = diagonal (λ i:{a // pn a}, hAHA.eigenvalues i),
  -- -- sorry 
  -- { change S₁₁ with Se.to_blocks₁₁,
  --   change Se with ((reindex e.symm e.symm) S),
  --   rw to_blocks₁₁,
  --   simp only [reindex_apply, equiv.symm_symm, submatrix_diagonal_equiv],
  --   funext j k, 
  --   rw of_apply,
  --   by_cases hjk: j = k, rw hjk, 
  --   rw [diagonal_apply_eq, diagonal_apply_eq, function.comp_app, equiv.sum_compl_apply_inl],
  --   rw [diagonal_apply_ne, diagonal_apply_ne], 
  --   exact hjk,
  --   simp only [ne.def], exact hjk, },

  have threeSs : Sσᴴ⁻¹ ⬝ (S₁₁ ⬝ Sσ⁻¹) = 1, 
  sorry 
  { rw [← matrix.conj_transpose_nonsing_inv, Sσ_inv, hS₁₁, diagonal_conj_transpose,
      has_trivial_star.star_trivial, diagonal_mul_diagonal, diagonal_mul_diagonal, ← diagonal_one,
      diagonal_eq_diagonal_iff],
    intro i,
    rw [mul_comm, mul_assoc, div_mul_div_comm, one_mul, ← real.sqrt_mul,
      real.sqrt_mul_self, mul_div_cancel'], exact i.prop, 
      all_goals 
      { apply eigenvalues_nonneg_of_pos_semidef, 
        apply conj_transpose_mul_self_is_pos_semidef,}, },

  have Vinv : Vᴴ⬝V = 1, 
  sorry 
  { apply_fun matrix.mul V,
    rw ← matrix.mul_assoc,
    rw matrix.is_hermitian.conj_transpose_eigenvector_matrix ,
    rw matrix.is_hermitian.eigenvector_matrix_mul_inv,
    rw [matrix.mul_one, matrix.one_mul],
    exact matrix.left_mul_inj_of_invertible _, },
  
  have Vbh : V₁ᴴ ⬝ V₁ = 1 ∧ V₁ᴴ ⬝ V₂ = 0 ∧ V₂ᴴ ⬝ V₁ = 0 ∧ V₂ᴴ ⬝ V₂ = 1, 
  sorry 
  { rw [Vblock, reindex_apply, conj_transpose_submatrix, submatrix_mul_equiv,
      from_blocks_conj_transpose, from_blocks_multiply] at Vinv,
    -- change xV₁ with vec_empty at Vinv,
    -- change xV₂ with vec_empty at Vinv,
    simp only [empty_mul_empty, add_zero] at Vinv,
    apply_fun reindex e.symm e.symm at Vinv,
    rw reindex_apply at Vinv,
    simp only [equiv.symm_symm, submatrix_submatrix, equiv.symm_comp_self, 
      submatrix_id_id, reindex_apply, submatrix_one_equiv] at Vinv,
    rw [← from_blocks_one, from_blocks_inj] at Vinv, 
    exact Vinv},

  -- have S₁₁diag : S₁₁ = diagonal (λ i:{a // pn a}, hAHA.eigenvalues i), 
  -- sorry 
  -- { change S₁₁ with Se.to_blocks₁₁,
  --   change Se with ((reindex e.symm e.symm) S),
  --   rw to_blocks₁₁,
  --   simp only [reindex_apply, equiv.symm_symm, submatrix_diagonal_equiv],
  --   funext j k, 
  --   rw of_apply,
  --   by_cases hjk: j = k, rw hjk, 
  --   rw [diagonal_apply_eq, diagonal_apply_eq, function.comp_app, equiv.sum_compl_apply_inl],
  --   rw [diagonal_apply_ne, diagonal_apply_ne], 
  --   exact hjk,
  --   simp only [ne.def], exact hjk, },
  
  let U₁ := A⬝V₁⬝((Sσ⁻¹).map RηC),
  have V₁inv : V₁ᴴ⬝V₁ = 1, exact Vbh.1,
  have U₁inv : U₁ᴴ⬝U₁ = 1, 
  sorry 
  { change U₁ with A ⬝ V₁ ⬝ Sσ⁻¹.map RηC,
    rw [conj_transpose_mul, conj_transpose_mul, matrix.mul_assoc, matrix.mul_assoc, 
      matrix.mul_assoc A, ← matrix.mul_assoc Aᴴ],
    conv_lhs {congr, skip, congr, skip, congr, rw reducedSpectral,},
    rw [matrix.mul_assoc, ← matrix.mul_assoc _ V₁, V₁inv, matrix.one_mul, matrix.mul_assoc V₁,
      ← matrix.mul_assoc _ V₁, V₁inv, matrix.one_mul, ← conj_transpose_map, 
      conj_transpose_nonsing_inv, ← matrix.map_mul, ← matrix.map_mul, threeSs,
      matrix.map_one RηC (map_zero RηC) (map_one RηC)],
    exact  semiconj_RηC, },
  
  have U₁Sσ : U₁⬝((Sσ).map RηC) = A ⬝ V₁, 
  sorry 
  { change U₁ with A⬝V₁⬝((Sσ⁻¹).map RηC),
    rw [matrix.mul_assoc, ← matrix.map_mul, nonsing_inv_mul, matrix.map_one, matrix.mul_one],
    exact map_zero RηC, 
    exact map_one RηC,
    exact Sσ_is_unit_det, },
  
  have AV₂ : A⬝V₂ = 0, 
  sorry 
  { suffices h : Aᴴ⬝A⬝V₂ = 0,
    apply (ker_mat_mul_conj_transpose_mul_self _ _).1 h,
    rw [reducedSpectral, matrix.mul_assoc, (Vbh.2.1), matrix.mul_zero], },

  let hAAH := is_hermitian_mul_conj_transpose_self A,
  let U := (hAAH).eigenvector_matrix,
  let pm := λ i, hAAH.eigenvalues i ≠ 0,
  let em := equiv.sum_compl pm,
  let ebm : (fin m) ⊕ (fin 0) ≃ (fin m) , { exact equiv.sum_empty (fin m) (fin 0) },
  let U₂ := ((reindex ebm.symm em.symm) U).to_blocks₁₂,

  -- have nzeigs_eqcard : fintype.card {a // pm a} = fintype.card {a // pn a}, 
  -- { sorry, },

  -- have ee : {a // pm a} ≃ {a // pn a}, 
  -- { exact (fintype.equiv_of_card_eq nzeigs_eqcard),},

  have AAHU₂ : A ⬝ Aᴴ ⬝ U₂ = 0, 
  sorry 
  { have spectralAAH := modified_spectral_theorem hAAH,
    rw spectralAAH,
    apply_fun matrix.mul hAAH.eigenvector_matrix_inv,
    rw [← matrix.mul_assoc, ← matrix.mul_assoc, eigenvector_matrix_inv_mul_self hAAH, -- matrix.is_hermitian.eigenvector_matrix_mul_inv' hAAH,
      matrix.one_mul, matrix.mul_zero],
    apply_fun (reindex (em.symm) (equiv.refl _)),
    rw [reindex_apply, reindex_apply, submatrix_zero],
    simp only [equiv.symm_symm, equiv.refl_symm, equiv.coe_refl, dmatrix.zero_apply],
    rw [← submatrix_mul_equiv _ _ _ (equiv.refl _) _, ← submatrix_mul_equiv _ _ _ em _],

    change U₂ with ((reindex ebm.symm em.symm) U).to_blocks₁₂,
    change U with hAAH.eigenvector_matrix,

    rw to_blocks₁₂,
    simp only [submatrix_diagonal_equiv, equiv.coe_refl, reindex_apply, equiv.symm_symm, submatrix_apply, 
      equiv.sum_empty_apply_inl, equiv.sum_compl_apply_inr, submatrix_id_id, of_apply],

    funext i j,
    cases i,
    -- The Range Case
    { rw matrix.mul_assoc,
    simp_rw [matrix.mul_apply, finset.mul_sum, diagonal_apply, ite_mul, zero_mul, function.comp_app],
    simp only [equiv.sum_compl_apply_inl, submatrix_apply, id.def, of_apply, finset.sum_ite_irrel, 
      finset.sum_const_zero, finset.sum_ite_eq, finset.mem_univ, if_true, dmatrix.zero_apply],
    rw [← finset.mul_sum, ← mul_apply, eigenvector_matrix_inv_mul_self hAAH,
      one_apply_ne, mul_zero], apply compl_subtypes_ne, },
    
    -- The Kernel Case
    { simp only [submatrix_diagonal_equiv, equiv.coe_refl, submatrix_id_id, dmatrix.zero_apply],
      simp_rw [matrix.mul_apply, finset.sum_mul, diagonal_apply, ite_mul, zero_mul, function.comp_app],
      simp only [equiv.sum_compl_apply_inr, submatrix_apply, id.def, finset.sum_ite_eq, finset.mem_univ, if_true],
      have : hAAH.eigenvalues i = 0, 
      { apply not_not.1, rw ← ne.def,
        apply i.prop, },
      simp_rw [this, complex.of_real_zero, zero_mul, finset.sum_const_zero], },

    apply matrix.left_mul_inj_of_invertible, },

  have AHU₂ : Aᴴ⬝U₂ = 0, 
  sorry 
  { rw ← ker_mat_mul_self_conj_transpose, rw AAHU₂,},
  have U₁HU₂ : U₁ᴴ⬝U₂ = 0, 
  sorry 
  { change U₁ with A⬝V₁⬝((Sσ⁻¹).map RηC),
    rw [matrix.mul_assoc, conj_transpose_mul, matrix.mul_assoc, AHU₂, matrix.mul_zero], },

  have U₂HU₂: U₂ᴴ⬝U₂ = 1, 
  sorry 
  { change U₂ with ((reindex ebm.symm em.symm) U).to_blocks₁₂,
    change U with hAAH.eigenvector_matrix,
    
    rw to_blocks₁₂,
    simp only [reindex_apply, equiv.symm_symm, submatrix_apply, equiv.sum_empty_apply_inl, 
      equiv.sum_compl_apply_inr],
    funext x y,
    rw mul_apply,
    simp_rw [of_apply, conj_transpose_apply, of_apply, ← conj_transpose_apply, ←mul_apply,
      eigenvector_matrix_conj_transpose_mul_self], 
    by_cases hxy: x = y, { simp_rw [hxy, one_apply_eq],},
    have : (x: fin m) ≠ y, { by_contra, rw subtype.coe_inj at h, exact hxy h, }, 
    rw [one_apply_ne this, one_apply_ne (hxy)], },
  have U₂HU₁: U₂ᴴ⬝U₁ = 0,
  sorry
  { rw [← conj_transpose_conj_transpose U₁, ← conj_transpose_mul, U₁HU₂, conj_transpose_zero], },
  have : (from_blocks U₁ U₂ vec_empty vec_empty)ᴴ ⬝ (from_blocks U₁ U₂ vec_empty vec_empty) = 1, 
  sorry
  { rw [from_blocks_conj_transpose, from_blocks_multiply],
    simp_rw [empty_mul_empty, add_zero, U₁inv, U₁HU₂, U₂HU₁, U₂HU₂, from_blocks_one], },

  have xFinal :  A ⬝
         ((reindex eb (equiv.refl ({a // pn a} ⊕ {a // ¬pn a})))
              (from_blocks V₁ V₂ vec_empty vec_empty)) =
       (reindex ebm (equiv.refl ({a // pn a} ⊕ {a // ¬pm a})))
             (from_blocks U₁ U₂ vec_empty vec_empty) ⬝
           (from_blocks Sσ 0 0 0).map RηC, 
  sorry 
  { simp_rw [reindex_apply],
    simp only [equiv.refl_symm, equiv.coe_refl, conj_transpose_submatrix],
    
    rw [← submatrix_id_id ((from_blocks (Sσ) 0 0 0).map RηC), ← submatrix_mul, 
      from_blocks_map],
    simp_rw matrix.map_zero RηC (map_zero _),
    simp only [from_blocks_multiply, empty_mul_empty, matrix.zero_mul, 
      matrix.mul_zero, add_zero, mul_empty, of_add_of, pi.const_add, empty_add_empty],
    change U₁ with  A ⬝ V₁ ⬝ Sσ⁻¹.map RηC,
    rw [matrix.mul_assoc, ← matrix.map_mul, nonsing_inv_mul, 
      matrix.map_one _ (map_zero RηC) (map_one RηC), matrix.mul_one],
    funext x y,
    rw mul_apply, simp_rw submatrix_apply,
    cases y,
    simp only [equiv.sum_empty_symm_apply, id.def, from_blocks_apply₁₁], rw ← mul_apply,

    simp only [equiv.sum_empty_symm_apply, id.def, from_blocks_apply₁₂, dmatrix.zero_apply],
    rw ← mul_apply, rw AV₂, rw [pi.zero_apply,pi.zero_apply],
    exact Sσ_is_unit_det,
    exact function.bijective_id,  },
  -- 
  
  have fFinal: 
    ((reindex eb (equiv.refl _)) (from_blocks V₁ V₂ vec_empty vec_empty)) ⬝
    ((reindex eb (equiv.refl _)) (from_blocks V₁ V₂ vec_empty vec_empty))ᴴ = 1, 
  sorry 
  { rw [conj_transpose_reindex, reindex_apply, reindex_apply, ← submatrix_mul,
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
    simp only [equiv.refl_symm, equiv.coe_refl, function.bijective_id], },
  
  ---!------------------------

  have card_pn_r: fintype.card {a // pn a} = r,
  {
    rw hrank,
    symmetry,
    exact rank_eq_card_pos_eigs_conj_transpose_mul_self A, },
  have card_pm_r: fintype.card {a // pm a} = r,
  { rw hrank,
    symmetry,
    exact rank_eq_card_pos_eigs_self_mul_conj_transpose A, },
  
  have card_not_pm_m_sub_r: fintype.card {a // ¬pm a} = (m - r), 
  { rw [fintype.card_subtype_compl, fintype.card_fin, card_pm_r], },
  have card_not_pn_n_sub_r: fintype.card {a // ¬pn a} = (n - r),
  { rw [fintype.card_subtype_compl, fintype.card_fin, card_pn_r], },
  have e_pn_r: {a // pn a} ≃ (fin r), {apply fintype.equiv_fin_of_card_eq card_pn_r,},
  have e_not_pm_r: {a // ¬pm a} ≃ (fin (m - r)), 
  { apply fintype.equiv_fin_of_card_eq card_not_pm_m_sub_r, },
  have e_not_pn_r: {a // ¬pn a} ≃ (fin (n - r)), 
  { apply fintype.equiv_fin_of_card_eq card_not_pn_n_sub_r, },

  let ezm : {a // pn a} ⊕ {a // ¬pm a} ≃ (fin r) ⊕ (fin (m - r)) 
    := equiv_trans_across_sums e_pn_r e_not_pm_r,
  -- sorry 
  -- { exact equiv_trans_across_sums e_pn_r e_not_pm_r,},
  let ezn : {a // pn a} ⊕ {a // ¬pn a} ≃ (fin r) ⊕ (fin (n - r)) 
  -- sorry 
    := equiv_trans_across_sums e_pn_r e_not_pn_r,

  have Final: A = 
    ((from_blocks U₁ U₂ vec_empty vec_empty).submatrix (ebm.symm) (ezm.symm)) ⬝
    ((((from_blocks Sσ 0 0 0)).submatrix (ezm.symm) (ezn.symm)).map RηC) ⬝
    ((from_blocks V₁ V₂ vec_empty vec_empty).submatrix (eb.symm) (ezn.symm))ᴴ,
  sorry 
  { apply_fun (λ x, x ⬝(((reindex eb (equiv.refl _)) (from_blocks V₁ V₂ vec_empty vec_empty))ᴴ)) at xFinal,
    rw matrix.mul_assoc at xFinal,
    rw fFinal at xFinal,
    rw matrix.mul_one at xFinal,
    apply_fun (λ x, x.submatrix id id) at xFinal,
    rw submatrix_id_id at xFinal,
    simp only [reindex_apply, equiv.refl_symm, equiv.coe_refl, conj_transpose_submatrix] at xFinal,
    rw ← submatrix_mul_equiv _ _ _ ezn.symm _ at xFinal,
    rw ← submatrix_mul_equiv _ _ _ ezm.symm _ at xFinal,
    simp only [submatrix_submatrix, function.comp.right_id, function.comp.left_id] at xFinal,
    exact xFinal, },
  
  -- have A_rank_r: A.rank = r, sorry,
  
  have e_pn_pm : {a // pm a} ≃ {a // pn a}, 
  sorry 
  { apply fintype.equiv_of_card_eq, rw [card_pn_r, card_pm_r], },
  
  sorry   
  { use (from_blocks U₁ U₂ vec_empty vec_empty).submatrix (ebm.symm) (ezm.symm),
    -- use (λ i, (real.sqrt (S₁₁ (e_pn_r.symm i) (e_pn_r.symm i)))),
    use ((from_blocks Sσ 0 0 0)).submatrix (ezm.symm) (ezn.symm),
    use (from_blocks V₁ V₂ vec_empty vec_empty).submatrix (eb.symm) (ezn.symm),
    -- intros Q,
    rw ← submatrix_map (RηC), 
    simp_rw conj_transpose_submatrix,
    split,
    exact Final,
    simp_rw [from_blocks_conj_transpose, submatrix_mul_equiv, from_blocks_multiply,
      empty_mul_empty, mul_empty, empty_mul, of_add_of, pi.const_add, empty_add_empty,
      add_zero, Vbh.1, Vbh.2.1, Vbh.2.2, submatrix_empty_blocks,
      U₁inv, U₁HU₂, U₂HU₁, U₂HU₂, from_blocks_one, submatrix_one_equiv],
    rw subblocks_eq_one V₁ V₂ Vbh.1 Vbh.2.1 Vbh.2.2.1 Vbh.2.2.2,
    rw subblocks_eq_one_with_equiv U₁ U₂ e_pn_pm U₁inv U₁HU₂ U₂HU₁ U₂HU₂,
    simp_rw [eq_self_iff_true, true_and],
    simp_rw [to_blocks₁₂, to_blocks₂₁, to_blocks₂₂, ← matrix.ext_iff, submatrix_apply, 
      of_apply, dmatrix.zero_apply, from_blocks, of_apply, pi.zero_apply, 
      sum.elim_zero_zero],
    change ezm with equiv_trans_across_sums e_pn_r e_not_pm_r,
    change ezn with equiv_trans_across_sums e_pn_r e_not_pn_r,
    simp_rw [equiv_trans_across_sums, equiv.coe_fn_symm_mk,
      sum.elim_inl, sum.elim_inr, pi.zero_apply, eq_self_iff_true, 
      forall_2_true_iff, and_true],
     },
  
end 

-- -/

