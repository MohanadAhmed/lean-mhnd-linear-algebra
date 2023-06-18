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

example {m n r : ℕ}
  (A : matrix (fin m) (fin n) ℂ)
  (hrank : r = A.rank) 
  (hc: fintype.card {i // (is_hermitian_transpose_mul_self A).eigenvalues i ≠ 0} = r)
  (hdiag: ∀ (a: {i // (is_hermitian_transpose_mul_self A).eigenvalues i ≠ 0}), 
    0 < ((is_hermitian_transpose_mul_self A).eigenvalues a) ):
  let 
    hAHA := (is_hermitian_transpose_mul_self A), 
    pn := (λ i, hAHA.eigenvalues i ≠ 0),
    e_pn_r : {a // pn a} ≃ fin r := fintype.equiv_fin_of_card_eq hc
  in
    (∀ (i j : fin r), i ≠ j → diagonal (λ (i : {a // pn a}), real.sqrt (hAHA.eigenvalues ↑i))
      ((e_pn_r.symm) i) ((e_pn_r.symm) j) = 0) 
      ∧
    (∀ (i : fin r), (0:ℝ) < (
        of (λ (i j : fin r), diagonal (λ (i : {a // pn a}), real.sqrt (hAHA.eigenvalues ↑i))
        ((e_pn_r.symm) i) ((e_pn_r.symm) j)) i i)) :=
begin
  intros hAHA pn e_pn_r,
  simp_rw [of_apply, diagonal_apply_eq, ne.def, real.sqrt_pos],
  split,
  intros i j hij,
  apply diagonal_apply_ne,
  rwa [ne.def, embedding_like.apply_eq_iff_eq ],
  intros i,
  apply hdiag,
end

