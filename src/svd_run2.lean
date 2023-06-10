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

lemma mul_star_self_nonneg {n : ℕ} (v: (fin n) → ℂ): 0 ≤ is_R_or_C.re((star v) ⬝ᵥ v) := 
begin
  simp_rw [is_R_or_C.re_to_complex, dot_product_comm, dot_product, 
    complex.re_sum, pi.star_apply, ← star_ring_end_apply, 
    complex.mul_conj, ← complex.sq_abs, complex.of_real_re],
  apply finset.sum_nonneg,
  intros i hi, simp only [pow_nonneg, map_nonneg],
end

lemma conj_transpose_mul_self_is_pos_semidef {m n : ℕ} (A: matrix (fin m) (fin n) ℂ):
     matrix.pos_semidef (Aᴴ⬝A) 
:= begin
  split,
  exact is_hermitian_transpose_mul_self A,
  intro v,
  rw [← mul_vec_mul_vec, dot_product_mul_vec, vec_mul_conj_transpose, 
    is_R_or_C.re_to_complex, star_star], 
  apply mul_star_self_nonneg,
end

lemma eigenvalues_nonneg_of_pos_semidef {n : ℕ} (A: matrix (fin n) (fin n) ℂ) 
  (hAp: matrix.pos_semidef A) (i: fin n): 
  0 ≤ hAp.1.eigenvalues i := begin
  rw  matrix.is_hermitian.eigenvalues_eq,
  apply hAp.2,
end

/-
example {m n : ℕ}
  (A : matrix (fin m) (fin n) ℂ) :
  let hAHA : (Aᴴ ⬝ A).is_hermitian := is_hermitian_transpose_mul_self A,
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
      Sσ : matrix {a // pn a} {a // pn a} ℝ :=
          matrix.diagonal (λ i, (real.sqrt (S₁₁ i i)))
     --    matrix.of (λ i j, ite (i = j) (real.sqrt (S₁₁ i j)) 0)
  in S = (reindex e e) (from_blocks S₁₁ S₁₂ S₂₁ S₂₂) →
     S₁₂ = 0 →
     S₂₁ = 0 →
     S₂₂ = 0 → invertible Sσ :=
begin
  intros hAHA S pn e Se S₁₁ S₁₂ S₂₁ S₂₂ Sσ Sblock hS₁₂ hS₂₁ hS₂₂,
--   apply invertible_of_left_inverse _ matrix.of (λ i j, ite (i = j) (1 / real.sqrt (S₁₁ i j)) 0),
--   change Sσ with S₁₁.map (λ (x : ℝ), ite (x = 0) 0 (real.sqrt x)),
--   funext i j,
change Sσ with matrix.diagonal (λ i, (real.sqrt (S₁₁ i i))),
apply invertible_of_right_inverse _  (matrix.diagonal (λ i, (1 / real.sqrt (S₁₁ i i)))),
rw [matrix.diagonal_mul_diagonal, ← diagonal_one, diagonal_eq_diagonal_iff],
intro i,
have diagnz : 0 < S₁₁ i i , 
{ change S₁₁ with ((reindex e.symm e.symm) (diagonal hAHA.eigenvalues)).to_blocks₁₁,
  rw to_blocks₁₁,
  dsimp,
  rw diagonal_apply_eq,
  cases lt_or_eq_of_le (eigenvalues_nonneg_of_pos_semidef _ (conj_transpose_mul_self_is_pos_semidef A) i),
  exact h,
  exfalso,
  exact i.prop (h.symm), },

rw mul_one_div_cancel,
apply real.sqrt_ne_zero'.2 diagnz,
end
-/

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
  haveI Sσinv : invertible Sσ, sorry,
  let U₁ := A⬝V₁⬝((Sσ⁻¹).map RηC),
  have V₁inv : V₁ᴴ⬝V₁ = 1, sorry,
  have U₁inv : U₁ᴴ⬝U₁ = 1, sorry,
  
  have: U₁⬝((Sσ).map RηC) = A ⬝ V₁, {

  },
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
--/

#exit

/- namespace svd
variable (A: matrix m n ℂ)

def RηC := algebra_map ℝ ℂ
/- ## AᴴA is eigendecomposable into V Q Vᴴ-/
noncomputable def V := (is_hermitian_transpose_mul_self A).eigenvector_matrix
noncomputable def Q := (diagonal ((is_hermitian_transpose_mul_self A).eigenvalues)).map RηC

lemma hermitianAhA_eigendeomposable: (Aᴴ⬝A) = (V A)⬝(Q A)⬝(V A)ᴴ := sorry

/- ## We can repartition Q into zero and non-zero eigenvalue entries -/
def ppos := (λ i,  (is_hermitian_transpose_mul_self A).eigenvalues i = 0)
-- noncomputable def p_dec: decidable_pred (ppos A) := begin
--   unfold decidable_pred,
--   intro a,
--   rw ppos, dsimp,
--   exact real.decidable_eq _ _,
-- end

noncomputable def Q11 := A

def e := equiv.sum_compl (ppos A)

-- /- ## We show that AᴴA is positive semidefinite -/
-- lemma conj_transpose_mul_self_pos_semidef : matrix.pos_semidef (Aᴴ⬝A) := sorry

end svd -/