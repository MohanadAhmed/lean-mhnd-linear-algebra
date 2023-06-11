import data.matrix.basic
import data.matrix.rank
import rank_surj_inv
import algebra.star.basic
import data.fin.tuple.sort
import data.complex.basic
import data.real.basic
import linear_algebra.matrix.pos_def

-- open matrix 
open complex matrix
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

lemma xeigs {m n r : ℕ}[ne_zero m][ne_zero n](A: matrix (fin m) (fin n) ℂ) (hr: A.rank = r)
  (hrm: r ≤ m)(hrn: r ≤ n):
  let 
    eigAAH := (matrix.is_hermitian_mul_conj_transpose_self A).eigenvalues,
    eigAHA := (matrix.is_hermitian_transpose_mul_self A).eigenvalues,
    sAAH := tuple.sort eigAAH,
    sAHA := tuple.sort eigAHA,
    fin_m_l : (fin m) := fin.last (m - 1),
    fin_n_l : (fin n) := fin.last (n - 1)
  in
  ∀ i: (fin r), 
    eigAAH (sAAH (fin_m_l - fin.cast_lt i (lt_of_le_of_lt' hrm (fin.is_lt i)))) = 
    eigAHA (sAHA (fin_n_l - fin.cast_lt i (lt_of_le_of_lt' hrn (fin.is_lt i)))) := 
begin
  intros eigAAH eigAHA sAAH sAHA fin_m_l fin_n_l,
  intro i,
  dsimp,
end
