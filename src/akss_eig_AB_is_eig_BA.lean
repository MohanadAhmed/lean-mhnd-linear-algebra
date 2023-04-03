import tactic
import data.complex.basic
import data.matrix.basic
import linear_algebra.matrix.to_lin
import linear_algebra.eigenspace

open_locale matrix big_operators complex_conjugate
open matrix
open module.End
open linear_map

variables {m n l p : Type*}
variables [fintype m] [fintype n] [fintype l] [fintype p]
variables [decidable_eq m] [decidable_eq n] [decidable_eq l] [decidable_eq p]


lemma ABveqzv_BABveqzBV {A: matrix m n ℂ} {B: matrix n m ℂ} {z: ℂ} {v: m → ℂ}
(hinj: (A⬝B).mul_vec v = z•v) :
(B⬝(A⬝B)).mul_vec v = z•(B.mul_vec v) :=
begin
  -- apply_fun (B.mul_vec) at hinj, -- Alex J Best'ts Suggestion.
  -- rw [matrix.mul_vec_mul_vec, mul_vec_smul] at hinj,
  -- assumption,
  rw [←matrix.mul_vec_smul, ←hinj, ←matrix.mul_vec_mul_vec], -- Eric Wiesers Proof
end

theorem eig_AB_is_eig_BA
  {A: matrix m n ℂ} {B: matrix n m ℂ} 
  (z: ℂ)
  (hEigz: has_eigenvalue (matrix.to_lin' (A⬝B)) z)
  (hEigzNz: z ≠ 0)
  :
  (has_eigenvalue (matrix.to_lin' (B⬝A)) z) := 
begin
  have hVecExists := hEigz.exists_has_eigenvector,
  cases hVecExists with v hv,
  have hsMul := hv.apply_eq_smul,
  cases hv with _ hvNz,
  have BvNz : B.mul_vec v ≠ 0, {
    by_contra,
    rw to_lin' at hsMul,
    simp only [to_matrix'_symm, to_lin'_apply] at hsMul,
    rw ← mul_vec_mul_vec at hsMul,
    rw h at hsMul, 
    simp only [mul_vec_zero] at hsMul,
    have hxra: z•v = 0, by {rw hsMul,},
    clear hsMul,
    rw smul_eq_zero at hxra,
    cases hxra with hzz hvz,
    exact hEigzNz hzz,
    exact hvNz hvz,
  },
  
  have BvEig : has_eigenvector (matrix.to_lin' (B⬝A)) z (B.mul_vec v), {
    unfold has_eigenvector,
    rw to_lin' at hsMul,
    simp only [to_matrix'_symm, to_lin'_apply] at hsMul,
    rw mem_eigenspace_iff,
    split, rw [to_lin'], 
    simp only [to_matrix'_symm, to_lin'_mul, coe_comp, function.comp_app, to_lin'_apply, mul_vec_mul_vec], 
    exact ABveqzv_BABveqzBV hsMul,
    exact BvNz,
    -- sorry,
  },
  exact has_eigenvalue_of_has_eigenvector BvEig,
end