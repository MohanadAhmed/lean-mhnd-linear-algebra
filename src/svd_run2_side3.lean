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

lemma rank_eq_count_nonzero_eigs' (A: matrix n n ℂ)(hA: A.is_hermitian) :
  A.rank =  (fintype.card {i // (hA.eigenvalues) i ≠ 0}) := sorry
-- begin   
--   rw rank_eq_rank_diagonal A hA,
--   rw rank_diagonal_matrix,
--   simp only [of_real_eq_zero, fintype.card_subtype_compl, nat.cast_id],
-- end

example {m n : ℕ}
  (A : matrix (fin m) (fin n) ℂ) :
  let hAHA : (Aᴴ ⬝ A).is_hermitian := (is_hermitian_transpose_mul_self A),
      pn : fin n → Prop := λ (i : fin n), hAHA.eigenvalues i ≠ 0,
      en : {a // pn a} ⊕ {a // ¬pn a} ≃ fin n := equiv.sum_compl pn,
      hAAH : (A ⬝ Aᴴ).is_hermitian := (is_hermitian_mul_conj_transpose_self A),
      pm : fin m → Prop := λ (i : fin m), hAAH.eigenvalues i ≠ 0,
      em : {a // pm a} ⊕ {a // ¬pm a} ≃ fin m := equiv.sum_compl pm
  in
     fintype.card {a // pm a} = fintype.card {a // pn a} :=
begin
  intros hAHA pn en hAAH pm em,
    rw [← rank_eq_count_nonzero_eigs', ← rank_eq_count_nonzero_eigs', 
      matrix.rank_self_mul_conj_transpose A,
      matrix.rank_conj_transpose_mul_self],
  admit,
end

