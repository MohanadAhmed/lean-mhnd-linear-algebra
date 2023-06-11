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
  in S.map RηC = diagonal (coe ∘ hAHA.eigenvalues) →
     Aᴴ ⬝ A = V ⬝ S.map RηC ⬝ Vᴴ →
     S = (reindex e e) (from_blocks S₁₁ S₁₂ S₂₁ S₂₂) →
     S₁₂ = 0 →
     S₂₁ = 0 →
     S₂₂ = 0 →
     V = (reindex eb e) (from_blocks V₁ V₂ xV₁ xV₂) →
     Aᴴ ⬝ A = V₁ ⬝ S₁₁.map RηC ⬝ V₁ᴴ →
     Vᴴ ⬝ V = 1 →
     V₁ᴴ ⬝ V₁ = 1 ∧
       V₁ᴴ ⬝ V₂ = 0 ∧
         V₂ᴴ ⬝ V₁ = 0 ∧ V₂ᴴ ⬝ V₂ = 1 →
     V₁ᴴ ⬝ V₁ = 1 →
     U₁ᴴ ⬝ U₁ = 1 →
     U₁ ⬝ Sσ.map RηC = A ⬝ V₁ →
     A ⬝ V₂ = 0 →
     from_blocks U₁ 0 vec_empty vec_empty ⬝
         (from_blocks Sσ S₁₂ S₂₁ S₂₂).map RηC =
       from_blocks (A ⬝ V₁) (A ⬝ V₂) vec_empty vec_empty :=
begin
  intros hAHA V S pn e Se S₁₁ S₁₂ S₂₁ S₂₂ eb V₁ V₂ xV₁ xV₂ Sσ U₁ 
    SRηC spectralAHA Sblock hS₁₂ hS₂₁ hS₂₂ Vblock reducedSpectral Vinv Vbh V₁inv U₁inv U₁Sσ AV₂,
  rw from_blocks_map, rw from_blocks_multiply,
  rw [AV₂, hS₁₂, hS₂₁, hS₂₂],
  simp_rw [matrix.zero_mul, (matrix.map_zero _ (map_zero RηC)), matrix.mul_zero, 
    zero_add, add_zero, matrix.empty_mul],
  congr,
  exact U₁Sσ,
end

