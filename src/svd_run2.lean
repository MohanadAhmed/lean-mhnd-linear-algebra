import data.matrix.basic
import data.matrix.rank
import data.matrix.notation
import data.fin.vec_notation
import data.complex.basic
import data.real.basic
import linear_algebra.matrix.pos_def
import tactic

open matrix
open_locale matrix big_operators

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

lemma matrix.is_hermitian.eigenvector_matrix_mul_inv' 
{𝕜 : Type u_1} [is_R_or_C 𝕜] [decidable_eq 𝕜] {n : Type u_2} [fintype n] [decidable_eq n] 
{A : matrix n n 𝕜} (hA : A.is_hermitian) :
hA.eigenvector_matrix_inv.mul hA.eigenvector_matrix = 1 := begin
sorry,
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
  have SRηC : S.map RηC = diagonal (coe ∘ hAHA.eigenvalues),
  sorry { change S with diagonal hAHA.eigenvalues,
   rw [matrix.diagonal_map (map_zero _), RηC, complex.coe_algebra_map],},
  have spectralAHA : (Aᴴ⬝A) = V⬝ S.map RηC ⬝ Vᴴ, 
  sorry { change V with hAHA.eigenvector_matrix,
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
  sorry { apply_fun reindex e.symm e.symm,
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
  have Vblock : V = (reindex eb e (from_blocks V₁ V₂ ![] ![])), 
  sorry {  apply_fun (reindex eb.symm e.symm),
     simp only [reindex_apply, equiv.symm_symm, submatrix_submatrix, 
          equiv.symm_comp_self, submatrix_id_id],
     funext i j,
     cases i, cases j, refl, refl,
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
  -- haveI Sσinv : invertible Sσ, 
  -- sorry { apply invertible_of_right_inverse _  (matrix.diagonal (λ i, (1 / real.sqrt (S₁₁ i i)))),
  --   rw [matrix.diagonal_mul_diagonal, ← diagonal_one, diagonal_eq_diagonal_iff],
  --   intro i,
  --   have diagnz : 0 < S₁₁ i i , 
  --   { change S₁₁ with ((reindex e.symm e.symm) (diagonal hAHA.eigenvalues)).to_blocks₁₁,
  --     rw to_blocks₁₁,
  --     dsimp,
  --     rw diagonal_apply_eq,
  --     cases lt_or_eq_of_le (eigenvalues_nonneg_of_pos_semidef _ 
  --       (conj_transpose_mul_self_is_pos_semidef A) i),
  --     exact h,
  --     exfalso,
  --     exact i.prop (h.symm), },
  --   rw mul_one_div_cancel,
  --   apply real.sqrt_ne_zero'.2 diagnz, },
  have Sσ_inv : Sσ⁻¹ = (matrix.diagonal (λ i, (1 / real.sqrt (S₁₁ i i)))), 
  sorry { rw inv_eq_right_inv,
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
  have S₁₁diag : S₁₁ = diagonal (λ i:{a // pn a}, hAHA.eigenvalues i),
  sorry { change S₁₁ with Se.to_blocks₁₁,
    change Se with ((reindex e.symm e.symm) S),
    rw to_blocks₁₁,
    simp only [reindex_apply, equiv.symm_symm, submatrix_diagonal_equiv],
    funext j k, 
    rw of_apply,
    by_cases hjk: j = k, rw hjk, 
    rw [diagonal_apply_eq, diagonal_apply_eq, function.comp_app, equiv.sum_compl_apply_inl],
    rw [diagonal_apply_ne, diagonal_apply_ne], 
    exact hjk,
    simp only [ne.def], exact hjk, },

  have threeSs : Sσᴴ⁻¹ ⬝ (S₁₁ ⬝ Sσ⁻¹) = 1, 
  sorry { rw [← matrix.conj_transpose_nonsing_inv, Sσ_inv, S₁₁diag, diagonal_conj_transpose,
      has_trivial_star.star_trivial, diagonal_mul_diagonal, diagonal_mul_diagonal, ← diagonal_one,
      diagonal_eq_diagonal_iff],
    intro i,
    rw [diagonal_apply_eq, mul_comm, mul_assoc, div_mul_div_comm, one_mul, ← real.sqrt_mul,
      real.sqrt_mul_self, mul_div_cancel'], exact i.prop, 
      all_goals 
      { apply eigenvalues_nonneg_of_pos_semidef, 
        apply conj_transpose_mul_self_is_pos_semidef,}, },

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

  have S₁₁diag : S₁₁ = diagonal (λ i:{a // pn a}, hAHA.eigenvalues i), 
  sorry { change S₁₁ with Se.to_blocks₁₁,
    change Se with ((reindex e.symm e.symm) S),
    rw to_blocks₁₁,
    simp only [reindex_apply, equiv.symm_symm, submatrix_diagonal_equiv],
    funext j k, 
    rw of_apply,
    by_cases hjk: j = k, rw hjk, 
    rw [diagonal_apply_eq, diagonal_apply_eq, function.comp_app, equiv.sum_compl_apply_inl],
    rw [diagonal_apply_ne, diagonal_apply_ne], 
    exact hjk,
    simp only [ne.def], exact hjk, },
  
  let U₁ := A⬝V₁⬝((Sσ⁻¹).map RηC),
  have V₁inv : V₁ᴴ⬝V₁ = 1, exact Vbh.1,
  have U₁inv : U₁ᴴ⬝U₁ = 1, 
  sorry { change U₁ with A ⬝ V₁ ⬝ Sσ⁻¹.map RηC,
    rw [conj_transpose_mul, conj_transpose_mul, matrix.mul_assoc, matrix.mul_assoc, 
      matrix.mul_assoc A, ← matrix.mul_assoc Aᴴ],
    conv_lhs {congr, skip, congr, skip, congr, rw reducedSpectral,},
    rw [matrix.mul_assoc, ← matrix.mul_assoc _ V₁, V₁inv, matrix.one_mul, matrix.mul_assoc V₁,
      ← matrix.mul_assoc _ V₁, V₁inv, matrix.one_mul, ← conj_transpose_map, 
      conj_transpose_nonsing_inv, ← matrix.map_mul, ← matrix.map_mul, threeSs,
      matrix.map_one RηC (map_zero RηC) (map_one RηC)],
    exact  semiconj_RηC, },
  
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
  sorry { have spectralAAH := modified_spectral_theorem hAAH,
    rw spectralAAH,
    apply_fun matrix.mul hAAH.eigenvector_matrix_inv,
    rw [← matrix.mul_assoc, ← matrix.mul_assoc, matrix.is_hermitian.eigenvector_matrix_mul_inv' hAAH,
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
    rw [← finset.mul_sum, ← mul_apply, matrix.is_hermitian.eigenvector_matrix_mul_inv', 
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

  have : Aᴴ⬝U₂ = 0, { rw ← ker_mat_mul_self_conj_transpose, rw AAHU₂,},
  
  -- extract_goal,
  -- have : (
  --   from_blocks 
  --     (reindex (equiv.refl (fin m)) ee.symm U₁) 
  --     (U₂: matrix (fin m) {a // ¬pm a} ℂ) 
  --     ![] ![]) ⬝
  --   ((from_blocks Sσ S₁₂ S₂₁ S₂₂).map RηC) = from_blocks (A⬝V₁) (A⬝V₂) ![] ![], 
  -- sorry { rw from_blocks_map, rw from_blocks_multiply,
  --   rw [AV₂, hS₁₂, hS₂₁, hS₂₂],
  --   simp_rw [matrix.zero_mul, (matrix.map_zero _ (map_zero RηC)), matrix.mul_zero, 
  --     zero_add, add_zero, matrix.empty_mul],
  --   congr,
  --   exact U₁Sσ, },

end 

-- -/

