import data.matrix.basic
import data.matrix.rank
import data.matrix.notation
import data.fin.vec_notation
import data.complex.basic
import data.real.basic
import linear_algebra.matrix.pos_def
import linear_algebra.matrix.nonsingular_inverse
import tactic

open matrix
open_locale matrix big_operators complex_conjugate


lemma sum_add_sum_compl_eq_sum_univ {z R: Type*}[fintype z][decidable_eq z][field R]
    {p: z → Prop} [decidable_pred p] (f: z → R):
     (∑ i : {a // p a}, f i) + (∑ (i : {a // ¬p a}), f i) = ∑ i : z, f i :=
begin
  -- rw ← fintype.sum_sum_elim,
  -- let fp := λ x, ite (p x) (f x) 0,
  -- rw finset.sum,
  -- rw finset.sum,
  -- rw finset.sum,
  -- rw finset.sum_
  -- simp only [fintype.sum_sum_type, sum.elim_inl, sum.elim_inr], 
  rw fintype.sum_subtype_add_sum_subtype p f,
end
