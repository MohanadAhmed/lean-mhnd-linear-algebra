import data.matrix.basic
import data.complex.basic
import linear_algebra.matrix.determinant
import linear_algebra.matrix.schur_complement
import data.polynomial.basic

open polynomial matrix function
open_locale big_operators polynomial matrix

variables {m n q R: Type*}
variables [fintype m][fintype n][decidable_eq m][decidable_eq n]
variables [fintype q][decidable_eq q]
variables [field R]

noncomputable def charpow_mat (M : matrix q q R) : (matrix q q R[X]) :=
(1: matrix q q R[X]) - (matrix.scalar q (polynomial.X))  ⬝ ((C : R →+* R[X]).map_matrix M)

noncomputable def charpow (M: matrix q q R): polynomial R := 
(charpow_mat M).det

lemma charpow_comm (A: matrix m n R)(B: matrix n m R):
  charpow (A⬝B) =  charpow (B ⬝ A) := 
begin
  unfold charpow, unfold charpow_mat,
  simp only [coe_scalar, ring_hom.map_matrix_apply, matrix.map_mul, smul_mul, matrix.one_mul],
  rw ← matrix.smul_mul,
  rw det_one_sub_mul_comm,
  rw matrix.mul_smul,
end

lemma charpow_eq_X_pow_n_mul_charpoly_inv (M : matrix q q R):
  charpow M = ((polynomial.X) ^ (fintype.card q)) * (M.charpoly.aeval X) := begin

end

lemma matrix_determinant_lemma (A: matrix m m R)(B: matrix n n R)
  (U: matrix m n R)(V: matrix  n m R) {hA: is_unit A.det}:
  (A + U⬝V).det = A.det * (1 + V⬝(A⁻¹)⬝U).det := begin
  nth_rewrite 0 ← matrix.mul_one A,
  rwa [← mul_nonsing_inv_cancel_left A (U⬝V), ← matrix.mul_add A,
    det_mul, ← matrix.mul_assoc, det_one_add_mul_comm, ← matrix.mul_assoc],
end

/- lemma charpow_eq_X_pow_n_mul_charpoly_inv (M : matrix q q R):
  charpow M = (polynomial.X) ^ (q.card) * (M.charpoly.aeval X⁻¹) := begin

end -/