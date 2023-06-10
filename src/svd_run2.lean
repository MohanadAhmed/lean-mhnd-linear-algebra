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

variables {m n p: Type*}
variables [fintype m][fintype n][fintype p]
variables [decidable_eq m][decidable_eq n][decidable_eq p]
variables {R: Type*} [comm_ring R]

lemma compl_subtypes_ne {z: Type*}[fintype z]{pn: z → Prop} :
     ∀ (i : {a // pn a}) (j : {a // ¬pn a}), (i: z) ≠ (j: z):= 
begin
  intros i j,
  by_contra' h,
  rw subtype.coe_eq_iff at h,
  cases h with hj hx,
  exact j.prop hj,
end

variables {F: Type*}[field F][is_R_or_C F]
def RηC := algebra_map ℝ ℂ

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

lemma matrix.left_mul_inj_of_invertible (P : matrix m m R) [invertible P] :
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
  funext x y, rw pi.zero_apply,rw pi.zero_apply,
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



--/-!
lemma svd_decompose{m n : ℕ} (A: matrix (fin m) (fin n) ℂ): 
∃ 
  (U: matrix (fin m) (fin m) ℂ)
  (Q: matrix (fin m) (fin n) ℝ)
  (V: matrix (fin n) (fin n) ℂ), 
  A = U⬝(Q.map RηC)⬝Vᴴ ∧ 
  V⬝Vᴴ = 1 ∧
  U⬝Uᴴ = 1 ∧
  Uᴴ⬝U = 1 ∧ 
  Vᴴ⬝V = 1 ∧
  ∀(i: fin m) (j : fin n),((i:ℕ) ≠ (j:ℕ)) → Q i j = 0
  := 
begin
  let hAHA := is_hermitian_transpose_mul_self A,
  let V := hAHA.eigenvector_matrix,
  let S := diagonal hAHA.eigenvalues,
  have spectralAHA : (Aᴴ⬝A) = V⬝ S.map RηC ⬝ Vᴴ, {sorry,},

  let pn := λ i, hAHA.eigenvalues i ≠ 0,
  let e := equiv.sum_compl pn,

  let Se := reindex e.symm e.symm (S),
  let S₁₁ := Se.to_blocks₁₁,
  let S₁₂ := Se.to_blocks₁₂,
  let S₂₁ := Se.to_blocks₂₁,
  let S₂₂ := Se.to_blocks₂₂,

  have Sblock : S = reindex e e (from_blocks S₁₁ S₁₂ S₂₁ S₂₂), 
     { apply_fun reindex e.symm e.symm,
     simp only [reindex_apply, equiv.symm_symm, submatrix_submatrix, 
        equiv.symm_comp_self, submatrix_id_id],
     funext i j,
     cases i; { cases j; refl,}, 
  },

  have hS₁₂ : S₁₂ = 0, 
  sorry { change S₁₂ with (reindex e.symm e.symm (diagonal hAHA.eigenvalues)).to_blocks₁₂,
    funext i j,
    rw [dmatrix.zero_apply, to_blocks₁₂], 
    dsimp,
    rw diagonal_apply_ne,
    apply compl_subtypes_ne, },

  have hS₂₁ : S₂₁ = 0, 
  sorry { change S₂₁ with (reindex e.symm e.symm (diagonal hAHA.eigenvalues)).to_blocks₂₁,
     funext i j,
    rw [dmatrix.zero_apply, to_blocks₂₁], 
    dsimp,
    rw diagonal_apply_ne',
    apply compl_subtypes_ne, },
  have hS₂₂ : S₂₂ = 0, 
  sorry {  change S₂₂ with (reindex e.symm e.symm (diagonal hAHA.eigenvalues)).to_blocks₂₂,
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
  let xV₁ : matrix (fin 0) {a // pn a} ℂ := ![],
  let xV₂ : matrix (fin 0) {a // ¬pn a} ℂ := ![],
  have Vblock : V = (reindex eb e (from_blocks V₁ V₂ xV₁ xV₂)), 
  sorry {  apply_fun (reindex eb.symm e.symm),
     simp only [reindex_apply, equiv.symm_symm, submatrix_submatrix, 
          equiv.symm_comp_self, submatrix_id_id],
     funext i j,
     cases i, cases j, refl, refl,
     change xV₁ with vec_empty,
     change xV₂ with vec_empty,
     rw submatrix_apply, 
     cases j;
     fin_cases i, },
  have reducedSpectral : Aᴴ⬝A = V₁⬝(S₁₁.map RηC)⬝(V₁ᴴ), 
  sorry {  simp_rw [(spectralAHA), Vblock, Sblock, reindex_apply, ← submatrix_map],
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

  let Sσ := matrix.diagonal (λ i, (real.sqrt (S₁₁ i i))),
  haveI Sσinv : invertible Sσ, 
  sorry { apply invertible_of_right_inverse _  (matrix.diagonal (λ i, (1 / real.sqrt (S₁₁ i i)))),
    rw [matrix.diagonal_mul_diagonal, ← diagonal_one, diagonal_eq_diagonal_iff],
    intro i,
    have diagnz : 0 < S₁₁ i i , 
    { change S₁₁ with ((reindex e.symm e.symm) (diagonal hAHA.eigenvalues)).to_blocks₁₁,
      rw to_blocks₁₁,
      dsimp,
      rw diagonal_apply_eq,
      cases lt_or_eq_of_le (eigenvalues_nonneg_of_pos_semidef _ 
        (conj_transpose_mul_self_is_pos_semidef A) i),
      exact h,
      exfalso,
      exact i.prop (h.symm), },
    rw mul_one_div_cancel,
    apply real.sqrt_ne_zero'.2 diagnz, },

  have Vinv : Vᴴ⬝V = 1, 
  sorry { apply_fun matrix.mul V,
    rw ← matrix.mul_assoc,
    rw matrix.is_hermitian.conj_transpose_eigenvector_matrix ,
    rw matrix.is_hermitian.eigenvector_matrix_mul_inv,
    rw [matrix.mul_one, matrix.one_mul],
    exact matrix.left_mul_inj_of_invertible _, },
  
  have Vbh : V₁ᴴ ⬝ V₁ = 1 ∧ V₁ᴴ ⬝ V₂ = 0 ∧ V₂ᴴ ⬝ V₁ = 0 ∧ V₂ᴴ ⬝ V₂ = 1, 
  sorry { rw [Vblock, reindex_apply, conj_transpose_submatrix, submatrix_mul_equiv,
      from_blocks_conj_transpose, from_blocks_multiply] at Vinv,
    change xV₁ with vec_empty at Vinv,
    change xV₂ with vec_empty at Vinv,
    simp only [empty_mul_empty, add_zero] at Vinv,
    apply_fun reindex e.symm e.symm at Vinv,
    rw reindex_apply at Vinv,
    simp only [equiv.symm_symm, submatrix_submatrix, equiv.symm_comp_self, 
      submatrix_id_id, reindex_apply, submatrix_one_equiv] at Vinv,
    rw [← from_blocks_one, from_blocks_inj] at Vinv, 
    exact Vinv},

  
  let U₁ := A⬝V₁⬝((Sσ⁻¹).map RηC),
  have V₁inv : V₁ᴴ⬝V₁ = 1, sorry,
  have U₁inv : U₁ᴴ⬝U₁ = 1, sorry,
  
  have U₁Sσ : U₁⬝((Sσ).map RηC) = A ⬝ V₁, 
  sorry { change U₁ with A⬝V₁⬝((Sσ⁻¹).map RηC),
    rw [matrix.mul_assoc, ← matrix.map_mul, nonsing_inv_mul, matrix.map_one, matrix.mul_one],
    exact map_zero RηC, 
    exact map_one RηC, 
    exact (is_unit_det_of_invertible Sσ), },
  
  have AV₂ : A⬝V₂ = 0, 
  sorry { suffices h : Aᴴ⬝A⬝V₂ = 0,
    apply (ker_mat_mul_conj_transpose_mul_self _ _).1 h,
    rw [reducedSpectral, matrix.mul_assoc, (Vbh.2.1), matrix.mul_zero], },

--   {
--      calc U₁ᴴ⬝U₁ = 
--   }
--   have : U₁ᴴ⬝U₁ = 1, {
--      change U₁ with A⬝V₁⬝(S₁₁⁻¹).map RηC,
--      rw conj_transpose_mul,
--      rw conj_transpose_mul,
--      rw matrix.mul_assoc,
--      rw matrix.mul_assoc,
--      rw ← matrix.mul_assoc Aᴴ,
--      rw ← matrix.mul_assoc Aᴴ,
--      simp_rw reducedSpectral,
--      have : (S₁₁⁻¹.map ⇑RηC)ᴴ ⬝ (V₁ᴴ ⬝ (V₁ ⬝ S₁₁.map ⇑RηC ⬝ V₁ᴴ ⬝ V₁ ⬝ S₁₁⁻¹.map ⇑RηC)) = 
--      (S₁₁⁻¹.map ⇑RηC)ᴴ ⬝ (V₁ᴴ ⬝ V₁) ⬝ S₁₁.map ⇑RηC ⬝ (V₁ᴴ ⬝ V₁) ⬝ (S₁₁⁻¹.map ⇑RηC),{
--           sorry,
--      },
--      rw this, rw V₁inv,
--   },
end 

-- -/

