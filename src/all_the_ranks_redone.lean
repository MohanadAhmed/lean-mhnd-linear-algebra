import linear_algebra.free_module.finite.rank
import linear_algebra.matrix.to_lin
import linear_algebra.finite_dimensional
import linear_algebra.matrix.dot_product
import data.complex.module
import data.matrix.rank

open_locale matrix big_operators
namespace matrix
open finite_dimensional

variables {l m n o R : Type*} [fintype m] [fintype n] [fintype o]
variables [comm_ring R]

section star_ordered_field
variables [field R][has_star R]

lemma dot_product_star_self_eq_zero' (v: n → R) :
  star v ⬝ᵥ v = 0 ↔ v = 0 := 
begin
  simp_rw [dot_product, pi.star_apply],
  split,
  intro h,
  rw star_self
  intro h, rw h, simp only [pi.zero_apply, mul_zero, finset.sum_const_zero],
end

lemma ker_mul_vec_lin_conj_transpose_mul_self1 (A : matrix m n R) :
  linear_map.ker (Aᴴ ⬝ A).mul_vec_lin = linear_map.ker (mul_vec_lin A):=
begin
 /-  ext x,
  simp only [linear_map.mem_ker, mul_vec_lin_apply, ←mul_vec_mul_vec],
  split,
  { intro h,
    replace h := congr_arg (dot_product (star x)) h,
    rwa [dot_product_mul_vec, dot_product_zero, vec_mul_conj_transpose, star_star,
      dot_product_star_self_eq_zero] at h },
  { intro h, rw [h, mul_vec_zero] }, -/
  sorry,
end

lemma rank_conj_transpose_mul_self (A : matrix m n R) :
  (Aᴴ ⬝ A).rank = A.rank :=
begin
  /- dunfold rank,
  refine add_left_injective (finrank R (A.mul_vec_lin).ker) _,
  dsimp only,
  rw [linear_map.finrank_range_add_finrank_ker,
    ←((Aᴴ ⬝ A).mul_vec_lin).finrank_range_add_finrank_ker],
  congr' 1,
  rw ker_mul_vec_lin_conj_transpose_mul_self, -/
  sorry,
end

-- this follows the proof here https://math.stackexchange.com/a/81903/1896
/-- TODO: prove this in greater generality. -/
@[simp] lemma rank_conj_transpose1 (A : matrix m n R) : Aᴴ.rank = A.rank := sorry
/- le_antisymm
  (((rank_conj_transpose_mul_self _).symm.trans_le $ rank_mul_le_left _ _).trans_eq $
    congr_arg _ $ conj_transpose_conj_transpose _)
  ((rank_conj_transpose_mul_self _).symm.trans_le $ rank_mul_le_left _ _)
 -/
@[simp] lemma rank_self_mul_conj_transpose1 (A : matrix m n R) : (A ⬝ Aᴴ).rank = A.rank := sorry
/- by simpa only [rank_conj_transpose, conj_transpose_conj_transpose]
  using rank_conj_transpose_mul_self Aᴴ
 -/
end star_ordered_field

section linear_ordered_field
variables [fintype m] [linear_ordered_field R]

lemma ker_mul_vec_lin_transpose_mul_self1  (A : matrix m n R) :
  linear_map.ker (Aᵀ ⬝ A).mul_vec_lin = linear_map.ker (mul_vec_lin A):= 
begin
  sorry,
/-   ext x,
  simp only [linear_map.mem_ker, mul_vec_lin_apply, ←mul_vec_mul_vec],
  split,
  { intro h,
    replace h := congr_arg (dot_product x) h,
    rwa [dot_product_mul_vec, dot_product_zero, vec_mul_transpose,
      dot_product_self_eq_zero] at h },
  { intro h, rw [h, mul_vec_zero] }, -/
end

lemma rank_transpose_mul_self1 (A : matrix m n R) : (Aᵀ ⬝ A).rank = A.rank :=
begin
/-   dunfold rank,
  refine add_left_injective (finrank R (A.mul_vec_lin).ker) _,
  dsimp only,
  rw [linear_map.finrank_range_add_finrank_ker,
    ←((Aᵀ ⬝ A).mul_vec_lin).finrank_range_add_finrank_ker],
  congr' 1,
  rw ker_mul_vec_lin_transpose_mul_self, -/
  sorry,
end

/-- TODO: prove this in greater generality. -/
@[simp] lemma rank_transpose1 (A : matrix m n R) : Aᵀ.rank = A.rank :=
le_antisymm
  ((rank_transpose_mul_self _).symm.trans_le $ rank_mul_le_left _ _)
  ((rank_transpose_mul_self _).symm.trans_le $ rank_mul_le_left _ _)

@[simp] lemma rank_self_mul_transpose (A : matrix m n R) : (A ⬝ Aᵀ).rank = A.rank :=
by simpa only [rank_transpose, transpose_transpose] using rank_transpose_mul_self Aᵀ

end linear_ordered_field

/-- The rank of a matrix is the rank of the space spanned by its rows.

TODO: prove this in a generality that works for `ℂ` too, not just `ℚ` and `ℝ`. -/
lemma rank_eq_finrank_span_row [linear_ordered_field R] [finite m] (A : matrix m n R) :
  A.rank = finrank R (submodule.span R (set.range A)) :=
begin
  casesI nonempty_fintype m,
  rw [←rank_transpose, rank_eq_finrank_span_cols, transpose_transpose]
end

end matrix