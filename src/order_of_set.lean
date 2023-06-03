import set_theory.cardinal.basic
import data.real.basic

open_locale cardinal

lemma non_zero_parts_equiv {m n : ℕ} (fm : fin m → ℝ) (fn : fin n → ℝ)
  -- the number of non-zero entries is equal
  (h : #{i // fm i ≠ 0} = #{i // fn i ≠ 0}) :
  -- the indices of non-zero entries are equivalent
  nonempty ({i // fm i ≠ 0} ≃ {i // fn i ≠ 0}) :=
begin
exact cardinal.eq.mp h
end


