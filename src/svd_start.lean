import data.complex.basic
import linear_algebra.matrix.hermitian
import linear_algebra.matrix.pos_def
import linear_algebra.matrix.determinant
import linear_algebra.matrix.spectrum

open matrix
open_locale matrix complex_conjugate big_operators

variables {F: Type*}[field F][is_R_or_C F]
variables m n : ℕ
variables [ne_zero m][ne_zero n]
variables A: matrix (fin m) (fin n) ℂ

lemma mul_star_self_nonneg  (v: (fin n) → ℂ): 0 ≤ is_R_or_C.re((star v) ⬝ᵥ v) := 
begin
  simp_rw [is_R_or_C.re_to_complex, dot_product_comm, dot_product, 
    complex.re_sum, pi.star_apply, ← star_ring_end_apply, 
    complex.mul_conj, ← complex.sq_abs, complex.of_real_re],
  apply finset.sum_nonneg,
  intros i hi, simp only [pow_nonneg, map_nonneg],
end

lemma conj_transpose_mul_self_is_pos_semidef: matrix.pos_semidef (Aᴴ⬝A) 
:= begin
  split,
  exact is_hermitian_transpose_mul_self A,
  intro v,
  rw [← mul_vec_mul_vec, dot_product_mul_vec, vec_mul_conj_transpose, 
    is_R_or_C.re_to_complex, star_star], 
  apply mul_star_self_nonneg,
end

lemma mul_conj_transpose_self_is_pos_semidef: matrix.pos_semidef (A⬝Aᴴ) 
:= begin
  split,
  exact is_hermitian_mul_conj_transpose_self A,
  intro v,
  rw [← mul_vec_mul_vec, dot_product_mul_vec], 
  nth_rewrite 0 ← conj_transpose_conj_transpose A,
  rw [vec_mul_conj_transpose, is_R_or_C.re_to_complex, star_star], 
  apply mul_star_self_nonneg,
end

lemma eigenvalues_nonneg_of_pos_semidef (A: matrix (fin n) (fin n) ℂ) 
  (hAp: matrix.pos_semidef A) (i: fin n): 
  0 ≤ hAp.1.eigenvalues i := begin
  rw  matrix.is_hermitian.eigenvalues_eq,
  apply hAp.2,
end



variables {L M N: Type*}
variables [fintype M][decidable_eq M]
variables [fintype N][decidable_eq N]
variables [fintype L][decidable_eq L]


def colpart₁ (A : matrix (M) (N ⊕ L) F) : matrix M N F :=
  matrix.of (λ (i : M)(j : N), A i (sum.inl j))

def colpart₂ (A : matrix (M) (N ⊕ L) F) : matrix M L F :=
  matrix.of (λ (i : M)(j : L), A i (sum.inr j))

-- def X := !![1, 2, 3; 4, 5, 6]
-- def p := (λ (i: fin 3), i = 2)
-- def p_dec: decidable_pred p := begin
--   unfold decidable_pred,
--   intro a,
--   rw p, dsimp,
--   exact eq.decidable a 2,
-- end

def pn := (λ i, ¬((is_hermitian_transpose_mul_self A).eigenvalues i = 0))
def pm := (λ i, ¬((is_hermitian_mul_conj_transpose_self A).eigenvalues i = 0))
def ex : {j: fin n // (pn m n A) j} ≃ {i: fin m // (pm m n A) i} := sorry


/- lemma eigvs_of_AAh_AhA
  (A : matrix (fin m) (fin n) ℂ) (i: fin n)
  (e: {i: fin m // (is_hermitian_mul_conj_transpose_self A).eigenvalues i ≠ 0} ≃
      {j: fin n // (is_hermitian_transpose_mul_self A).eigenvalues j ≠ 0} )
  (hi: (is_hermitian_transpose_mul_self A).eigenvalues i ≠ 0):
  let 
    v := ((is_hermitian_transpose_mul_self A).eigenvector_matrix_inv i), 
    u := ((is_hermitian_mul_conj_transpose_self A).eigenvector_matrix_inv (⇑(e i))),
    σ := (is_hermitian_transpose_mul_self A).eigenvalues i)
  in
  u := σ • A.mul_vec v := 
begin

end -/


def RηC := (algebra_map ℝ ℂ)

/- We want to say that for a matrix A: with vᵢ an eigenvecter of AᴴA and with eigenvalue
σᵢ, then σᵢ⁻¹Avᵢ is an eigenvector of (AAᴴ). This can be seen by:
  (AᴴA)vᵢ = σᵢvᵢ → A(AᴴA)vᵢ = σᵢAvᵢ → (AAᴴ)(Avᵢ)=σᵢ(Avᵢ)
-/
/- 
example (m n : ℕ)
  (A : matrix (fin m) (fin n) ℂ) :
  let Z : (Aᴴ ⬝ A).is_hermitian := is_hermitian_transpose_mul_self A,
      Z' : (A ⬝ Aᴴ).is_hermitian := is_hermitian_mul_conj_transpose_self A,
      V : matrix (fin n) (fin n) ℂ := Z.eigenvector_matrix,
      U : matrix (fin m) (fin m) ℂ := Z'.eigenvector_matrix,
      Q : matrix (fin m) (fin n) ℝ := 
        matrix.of (λ (i : fin m) (j : fin n), 
          ite ((i:ℕ) = (j:ℕ)) (real.sqrt(Z'.eigenvalues i)) 0)
  in A = U ⬝ Q.map ⇑RηC ⬝ Vᴴ :=
begin
  intros Z Z' V U Q,
  -- change V with Z.eigenvector_matrix,
  -- change U with Z'.eigenvector_matrix,
  -- rw is_hermitian.conj_transpose_eigenvector_matrix,
  have SU := Z'.spectral_theorem,
  have SV := Z.spectral_theorem,

  let pn := (λ i, ¬(Z.eigenvalues i = 0)),
  let pm := (λ i, ¬(Z'.eigenvalues i = 0)),
  have en := equiv.sum_compl pn,
  have em := equiv.sum_compl pm,
  let V' := reindex (equiv.refl (fin n)) en.symm V,
  let U' := reindex (equiv.refl (fin m)) em.symm U,
  have Va := colpart₁ V',
  have Vb := colpart₂ V',
  have Ua := colpart₁ U',
  have Ub := colpart₂ U',
  let S := reindex en.symm en.symm (diagonal (Z.eigenvalues)),
  have S₁₁ := S.to_blocks₁₁,
  have S₁₂ := S.to_blocks₁₂,
  have S₂₁ := S.to_blocks₂₁,
  have S₂₂ := S.to_blocks₂₂,
  have zS₁₂ : S₁₂ = 0,{sorry,},
  have zS₂₁ : S₂₁ = 0,{sorry,},
  have zS₂₂ : S₂₂ = 0,{sorry,},

end
 -/


/- lemma svd_decompose: 
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
  let Z := is_hermitian_transpose_mul_self A,
  let Z' := is_hermitian_mul_conj_transpose_self A,
  let V := Z.eigenvector_matrix,
  let U := Z'.eigenvector_matrix,
  let Q := matrix.of (λ (i: fin m) (j: fin n), ite ((i:ℕ) = (j:ℕ)) (Z'.eigenvalues i) 0 ),
  use U, use Q, use V,
  split, 
  sorry,

  split,
  change V with Z.eigenvector_matrix,
  rw is_hermitian.conj_transpose_eigenvector_matrix,
  apply matrix.is_hermitian.eigenvector_matrix_mul_inv,
  split,
  change U with Z'.eigenvector_matrix,
  rw is_hermitian.conj_transpose_eigenvector_matrix,
  apply matrix.is_hermitian.eigenvector_matrix_mul_inv,
  split,
  change U with Z'.eigenvector_matrix,
  rw is_hermitian.conj_transpose_eigenvector_matrix,
  rw matrix.mul_eq_one_comm,
  apply matrix.is_hermitian.eigenvector_matrix_mul_inv,
  split,
  change V with Z.eigenvector_matrix,
  rw is_hermitian.conj_transpose_eigenvector_matrix,
  rw matrix.mul_eq_one_comm,
  apply matrix.is_hermitian.eigenvector_matrix_mul_inv,
  intros i j hij,
  change Q with matrix.of (λ (i: fin m) (j: fin n), ite ((i:ℕ) = (j:ℕ)) (Z'.eigenvalues i) 0 ),
  rw ne.def at hij,
  dsimp,
  rw if_neg hij,
end -/