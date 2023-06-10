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

variables {m n p: Type*}
variables [fintype m][fintype n][fintype p]
variables [decidable_eq m][decidable_eq n][decidable_eq p]
variables {R: Type*} [comm_ring R]

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
      xV₁ : matrix (fin 0) {a // pn a} ℂ := vec_empty,
      xV₂ : matrix (fin 0) {a // ¬pn a} ℂ := vec_empty,
      Sσ : matrix {a // pn a} {a // pn a} ℝ :=
        diagonal (λ (i : {a // pn a}), real.sqrt (S₁₁ i i)),
      U₁ : matrix (fin m) {a // pn a} ℂ :=
        A ⬝ V₁ ⬝ Sσ⁻¹.map RηC
  in Aᴴ ⬝ A = V ⬝ S.map RηC ⬝ Vᴴ →
     S = (reindex e e) (from_blocks S₁₁ S₁₂ S₂₁ S₂₂) →
     S₁₂ = 0 →
     S₂₁ = 0 →
     S₂₂ = 0 →
     V = (reindex eb e) (from_blocks V₁ V₂ xV₁ xV₂) →
     Aᴴ ⬝ A = V₁ ⬝ S₁₁.map RηC ⬝ V₁ᴴ →
     V₁ᴴ ⬝ V₁ = 1 →
     U₁ᴴ ⬝ U₁ = 1 →
     U₁ ⬝ Sσ.map RηC = A ⬝ V₁ → A ⬝ V₂ = 0 :=
begin
  intros hAHA V S pn e Se S₁₁ S₁₂ S₂₁ S₂₂ eb V₁ V₂ xV₁ xV₂ Sσ U₁ 
    spectralAHA Sblock hS₁₂ hS₂₁ hS₂₂ Vblock reducedSpectral V₁inv U₁inv hU,
  suffices h : Aᴴ⬝A⬝V₂ = 0,
  apply (ker_mat_mul_conj_transpose_mul_self _ _).1 h,
  
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
  
  rw [reducedSpectral, matrix.mul_assoc, (Vbh.2.1), matrix.mul_zero],
  -- have : V₁ᴴ⬝V₂ = 0, {
  --   funext x y, 
  --   rw [ pi.zero_apply,pi.zero_apply],
  --   simp_rw [mul_apply, conj_transpose_apply],
  -- },
end

