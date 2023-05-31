import data.complex.basic
import linear_algebra.matrix.hermitian
import linear_algebra.matrix.pos_def
import linear_algebra.matrix.determinant
import linear_algebra.matrix.spectrum

open matrix
open_locale matrix complex_conjugate big_operators

def m: ℕ := 10
def n: ℕ := 14

/- Nonzero in fm is in fn -/
lemma zero_or_fm_in_fn (fm : fin m → ℝ)(fn : fin n → ℝ):
  ∀(i: fin m), fm i = 0 ∨ (∃ (j: fin n), fn j = fm i) := sorry

/- Flipped Around -/
lemma zero_or_fn_in_fm  (fm : fin m → ℝ)(fn : fin n → ℝ):
  ∀(j: fin n), fn j = 0 ∨ (∃ (i: fin m), fn j = fm i) := sorry

def pm (fm : fin m → ℝ): fin m → Prop := (λ i, (fm i = 0))
def pn (fn : fin n → ℝ): fin n → Prop := (λ j, (fn j = 0))

/- I want to say there is an equivalence relation between 
elements of fin m giving nonzero values for fm and the 
elements of fin n giving nonzero values for fn.
-/
lemma non_zero_parts_equiv (fm : fin m → ℝ)(fn : fin n → ℝ):
  ∃ e: ({i : fin m // pm fm} ≃ {j : fin n // pn fn}) := sorry

