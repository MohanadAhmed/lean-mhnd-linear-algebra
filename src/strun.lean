import data.complex.basic
import linear_algebra.matrix.hermitian
import linear_algebra.matrix.pos_def
import linear_algebra.matrix.determinant
import linear_algebra.matrix.spectrum
import linear_algebra.matrix.nonsingular_inverse
import linear_algebra.matrix.diagonal
import linear_algebra.std_basis
import data.matrix.basic
import data.matrix.rank
import rank_surj_inv
import algebra.star.basic
import data.fin.tuple.sort

-- open matrix
open complex
open_locale matrix big_operators

variables {m n R: Type*}
variables [fintype m][fintype n][decidable_eq m][decidable_eq n]
variables [field R][is_R_or_C R][partial_order R][star_ordered_ring R][decidable_eq R]

instance Cq := complex.star_ordered_ring

lemma modified_spectral_theorem (A: matrix n n ℂ)(hA: A.is_hermitian) :
  A = (hA.eigenvector_matrix) ⬝
    (matrix.diagonal (coe ∘ hA.eigenvalues)) ⬝ hA.eigenvector_matrix_inv :=
begin
  have h := hA.spectral_theorem,
  replace h := congr_arg (λ x, hA.eigenvector_matrix ⬝  x) h,
  simp only at h,
  rw [← matrix.mul_assoc, hA.eigenvector_matrix_mul_inv, matrix.one_mul] at h,
  rwa matrix.mul_assoc,
end

lemma rank_eq_rank_diagonal (A: matrix n n ℂ)(hA: A.is_hermitian) :
  A.rank = (matrix.diagonal ((coe ∘ hA.eigenvalues): n → ℂ)).rank :=
begin
  nth_rewrite_lhs 0 [modified_spectral_theorem A hA],
  rw rank_mul_unit,
  rw rank_mul_unit',
  apply matrix.is_unit_det_of_invertible,
  apply matrix.is_unit_det_of_invertible,
end

--noncomputable theory

open linear_map matrix set submodule
open_locale matrix big_operators

lemma rank_diagonal' [decidable_eq m] [decidable_eq R] (w : m → ℂ) :
   linear_map.rank ((diagonal w).to_lin') = fintype.card { i // w i ≠ 0 } :=
begin
  have hu : univ ⊆ {i : m | w i = 0}ᶜ ∪ {i : m | w i = 0}, { rw set.compl_union_self },
  have hd : disjoint {i : m | w i ≠ 0} {i : m | w i = 0} := disjoint_compl_left,
  have B₁ := supr_range_std_basis_eq_infi_ker_proj ℂ (λi:m, ℂ) hd hu (set.to_finite _),
  have B₂ := @infi_ker_proj_equiv ℂ _ _ (λi:m, ℂ) _ _ _ _ (by simp; apply_instance) hd hu,
  rw linear_map.rank,
  rw range_diagonal,
  rw B₁,
  rw ←@rank_fun' ℂ,
  apply linear_equiv.rank_eq,
  apply B₂,
end

lemma rank_diagonal_matrix (w: n → ℂ) :
  ((matrix.diagonal w).rank) = ↑(fintype.card {i // (w i) ≠ 0}) :=
begin
  have hu : univ ⊆ {i : n | w i = 0}ᶜ ∪ {i : n | w i = 0}, { rw set.compl_union_self },
  have hd : disjoint {i : n | w i ≠ 0} {i : n | w i = 0} := disjoint_compl_left,
  have B₁ := supr_range_std_basis_eq_infi_ker_proj ℂ (λi:n, ℂ) hd hu (set.to_finite _),
  have B₂ := @infi_ker_proj_equiv ℂ _ _ (λi:n, ℂ) _ _ _ _ (by simp; apply_instance) hd hu,
  rw matrix.rank,
  rw ← to_lin'_apply',
  rw range_diagonal,
  rw B₁,
  rw ← finite_dimensional.finrank_fintype_fun_eq_card ℂ,
  apply linear_equiv.finrank_eq,
  apply B₂,
end


lemma rank_eq_count_nonzero_eigs (A: matrix n n ℂ)(hA: A.is_hermitian) :
  A.rank =  ↑(fintype.card {i // (coe∘hA.eigenvalues: n → ℂ) i ≠ 0}) :=
begin
  rw rank_eq_rank_diagonal A hA,
  rw rank_diagonal_matrix,
end

lemma rank_eq_count_nonzero_eigs' (A: matrix n n ℂ)(hA: A.is_hermitian) :
  A.rank =  (fintype.card {i // (hA.eigenvalues) i ≠ 0}) :=
begin
  rw rank_eq_rank_diagonal A hA,
  rw rank_diagonal_matrix,
  simp only [of_real_eq_zero, fintype.card_subtype_compl, nat.cast_id],
end

lemma card_sub_rank_eq_count_zero_eigs' (A: matrix n n ℂ)(hA: A.is_hermitian) :
  A.rank =  (fintype.card n) - (fintype.card {i // (hA.eigenvalues) i = 0}) :=
begin
  rw rank_eq_rank_diagonal A hA,
  rw rank_diagonal_matrix,
  simp only [of_real_eq_zero, fintype.card_subtype_compl, nat.cast_id],
end

lemma card_nonzero_eigs_AhA_AAh_eq (A: matrix m n ℂ):
    (fintype.card {i // ((is_hermitian_mul_conj_transpose_self A).eigenvalues) i ≠ 0}) =
    (fintype.card {i // ((is_hermitian_transpose_mul_self A).eigenvalues) i ≠ 0}) :=
begin
  -- intros eigsAhA eigsAAh,
  rw [← rank_eq_count_nonzero_eigs', ← rank_eq_count_nonzero_eigs', matrix.rank_self_mul_conj_transpose,
    matrix.rank_conj_transpose_mul_self],
end

noncomputable def equiv_non_zero_singular_vals (A: matrix m n ℂ)
  := fintype.equiv_of_card_eq (card_nonzero_eigs_AhA_AAh_eq A)

/-
  What do I need to go on?
  I now have an equivalence between the sets of non-zero eigenvalues
  in the AhA and AAh matrices. But this does not make them ordered!

  What I want is to sort them in increasing (or decreasing) order.
  And say that they are the same.
-/

-- def x: list ℤ := [1, 2, -1, 3, -5]
-- def fx := (λ i: fin 5, list.nth_le x i (@fin.is_lt 5 i) )
-- #eval fx (tuple.sort fx) (fin 5).elems
-- #check fintype.elems (fin 5)

lemma range_zero_mat_zero {m n R: Type*}
  [fintype n][fintype m][decidable_eq m][decidable_eq n]
  [comm_ring R] [nontrivial R] {A: matrix m n R} :
  (∀ x, A.mul_vec x = 0) → A = 0 :=
begin
  intro h,
  funext x y, rw [pi.zero_apply,pi.zero_apply],
  let z := λ i, ite (i = y) (1:R) 0,
  
  specialize h z,
  rw function.funext_iff at h,
  specialize h x,
  simp_rw [mul_vec, dot_product, z, mul_boole, finset.sum_ite_eq',
    finset.mem_univ, if_true, pi.zero_apply] at h,
  exact h,
end

theorem matrix.rank_zero_iff_eq_zero {m n: Type*}  {R : Type*}
  [fintype n][fintype m][decidable_eq m][decidable_eq n]
  [field R] [nontrivial R] {A: matrix m n R} :
    A = 0 ↔ A.rank = 0 :=
begin
  split,
  intro h, rw [h, matrix.rank_zero],
  intro h,  
  rw [matrix.rank, finrank_eq_zero, linear_map.range_eq_bot, linear_map.ext_iff] at h,
  simp_rw [mul_vec_lin_apply] at h,
  exact range_zero_mat_zero h,
end


lemma xeigs {m n r : ℕ}[ne_zero m][ne_zero n](A: matrix (fin m) (fin n) ℂ) (hr: A.rank = r)
  (hrm: r ≤ m)(hrn: r ≤ n):
  let
    eigAHA := (matrix.is_hermitian_transpose_mul_self A).eigenvalues,
    sAHA := tuple.sort eigAHA
  in
  ∀ i, i < (n - r) →
    eigAHA (sAHA (i)) = 0 :=
begin
  intros eigAHA sAHA,
  intros i hi,
  by_cases r = 0,
  rw h at hr, 
  rw ← matrix.rank_zero_iff_eq_zero at hr,
  change sAHA with tuple.sort eigAHA,
  change eigAHA with (matrix.is_hermitian_transpose_mul_self A).eigenvalues,
  rw hr,
  simp only [conj_transpose_zero, matrix.zero_mul],
  rw is_hermitian.eigenvalues_eq,
  
end