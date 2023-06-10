import data.matrix.basic
import data.matrix.rank
import data.matrix.notation
import tactic

open matrix
open_locale matrix big_operators

variables {F: Type*}[field F]
variables (m n: Type*)
variables [fintype m][fintype n][decidable_eq m][decidable_eq n]

def e1 : m ⊕ (fin 0) ≃ m := equiv.sum_empty m (fin 0)

def im : fin 5 := 2
#eval (equiv.refl (fin 5)) im

#check e1 (fin 5)
#eval (e1 (fin 5)).symm (im)

def A := !![(1:ℤ), 2; 3, 4;]
def B := !![(2:ℤ), 0; 0, -1;]

#eval A.mul B

