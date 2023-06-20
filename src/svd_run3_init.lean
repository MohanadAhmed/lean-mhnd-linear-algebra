import data.matrix.basic
import data.matrix.notation
import data.complex.basic
import linear_algebra.matrix.pos_def
import linear_algebra.matrix.spectrum

open matrix
open_locale matrix big_operators

namespace svd

variables {m n: ℕ}
variables (A: matrix (fin m) (fin n) ℂ)


def RηC := algebra_map ℝ ℂ
-- include A
noncomputable def V : matrix (fin n) (fin n) ℂ :=
((matrix.diagonal (is_hermitian_transpose_mul_self A).eigenvalues).map RηC)

noncomputable def U : matrix (fin m) (fin m) ℂ := 
((matrix.diagonal (is_hermitian_mul_conj_transpose_self A).eigenvalues).map RηC)

def Q : matrix (fin m) (fin n) ℝ := (A.map (λ x: ℂ, x.re))

/-Now this one does not typecheck as well-/
lemma svd_eq: A = (svd.U A)⬝((svd.Q A).map RηC)⬝(svd.V A) := sorry 
/- Still does not typecheck-/
lemma right_conj_transpose_eigenvector_mul: (svd.Vᴴ) ⬝ svd.V = 1 := sorry

-- More lemmas about the U, Q, V matrices should be here

end svd
