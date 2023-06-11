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

/- The condition that there exists an index where the value is located in the other set is
not enough. Consider A = [1, 2, 2] and B = [1, 1, 2]. These are clearly not the same as each
other but would satisfy the codition. -/

noncomputable def wierd_inj {N: ℕ} (f g: (fin N) → ℝ)(hfg: ∀ i, (∃ j, f  i = g j)) : 
  (fin N) → (fin N) := begin
    intro x,
    specialize hfg x,
    have j := classical.some hfg,
    exact j,
end

lemma eq_sorted_func (N: ℕ)
  (f g: (fin N) → ℝ)(hfg: ∀ i, (∃ j, f  i = g j)) :  
  ∃ z, f∘z = g :=
begin
  by_contra,
  rw not_exists at h,
  


end
