import data.matrix.basic
import data.matrix.rank
import rank_surj_inv
import algebra.star.basic
import data.fin.tuple.sort

-- open matrix 
open complex
open_locale matrix big_operators

variables {m n R: Type*}
variables [fintype m][fintype n][decidable_eq m][decidable_eq n]
variables [field R][decidable_eq R][linear_order R]

lemma eq_sorted_func 
  -- (N: ℕ)
  -- (hN: N = 2)
  -- (M: ℕ)
  -- (hM: M = N.succ)
  -- (f g: (fin (N.succ)) → R)
  -- (he: ∀(i: fin (N.succ)), (∃(j: fin (N.succ)), g j = f i))
  -- (hM: M = N)
  -- (f g: (fin (N)) → R)
  -- (he: ∀(i: fin (N)), (∃(j: fin (N)), g j = f i))
  (f g: (fin (2)) → R)
  (he: ∀(i: fin (2)), (∃(j: fin (2)), g j = f i))
  (hf: monotone f)
  (hg: monotone g):
  f = g := 
begin
  -- rw hM at *,
  funext,
  fin_cases *,
  unfold monotone at *,
  have : (0: fin 2) ≤ 1, by simp only [fin.zero_le],
  specialize hf this,
  specialize hg this,
  have he0 := he 0,
  have he1 := he 1,
  cases he0 with j0 hj0,
  cases he1 with j1 hj1,
  fin_cases *, fin_cases *, symmetry', assumption', symmetry', assumption',
  fin_cases *,
  symmetry' at hj0,
  rw ← hj1 at hf, rw ← hj0 at hg,
  exact le_antisymm hf hg,
  

  -- induction N with N ihN,
  -- specialize he x,cases he with y hy,
  -- have : x = y, {simp only [eq_iff_true_of_subsingleton],},
  -- rwa [this, eq_comm], rwa this at hy,
  -- have : ∃ M: ℕ, M = N.succ, {sorry,},
  -- cases this with M hM,
  -- rw ← hM at *,
  
  -- specialize he x,
  -- by_contra,
  -- rw monotone at *,
  -- cases he with y hy, symmetry' at hy,
  -- by_cases hw: x ≤ y,
  -- specialize hf hw,
  -- specialize hg hw,
  -- by_cases hw1: x = y,
  -- rw ← hw1 at hy,
  -- exact h hy,
  -- have hw2 := lt_of_le_of_ne hw hw1,
  -- -- apply h,
  -- have ho := lt_or_eq_of_le hg,
  -- cases ho with ha hb,
  -- revert x,
  -- by_contra,
end
