import data.matrix.basic
import data.matrix.notation
import data.real.basic
import tactic.norm_fin
import tactic

open matrix
open_locale matrix big_operators
open equiv equiv.perm finset
open complex

def N := 4
def A := !![1, 2, 3, 4; 5, 6, 7, 8; 9, 10, 11, 12; 13, 14, 15, 16]
-- variable {myF : fin N → ℕ} -- For later use once I understand this
def valsx: (list ℕ) := [0, 1, 3, 0] 
def myF : fin N → ℕ := λ i, (list.nth_le valsx i (fin.is_lt i))
def z := fintype.elems (fin 4)
def Froots := (finset.subtype {i: fin N | myF i = 0}) z
def nroots := (finset.subtype {i: fin N | ¬(myF i = 0)}) z

#check Froots -- Type does not look correct
#check (Froots) ⊕ (nroots) -- Type does not look correct

--#eval reindex e (equiv.refl (fin N)) A 
-- should give !![1, 2, 3, 4; 13, 14, 15, 16; 5, 6, 7, 8; 9, 10, 11, 12;]

/- An example of a working reindexing but not with a function! -/
def shiftk {N: ℕ}{hN: ne_zero N} (k: fin N):(fin N → fin N) 
  := λ n: (fin N), (n + k)
def shiftk_equiv {N: ℕ} {hN: ne_zero N} (k: fin N) : (fin N) ≃ (fin N) :=
{ to_fun := @shiftk N hN (-k),
  inv_fun := @shiftk N hN (k),
  left_inv := by {intro x, simp_rw [shiftk, neg_add_cancel_right],},
  right_inv := by {intro x, simp_rw [shiftk, add_neg_cancel_right],}, }
def nz : ne_zero N := begin rw N, rw ne_zero_iff, norm_num, end
def e := @shiftk_equiv 4 nz 2
def B := !![1, 2, 3, 4; 0, 0, 0, 0; 9, 10, 11, 12; 0, 0, 0, 0;]
#eval reindex (equiv.refl (fin N)) e B 
-- gives !![9, 10, 11, 12; 13, 14, 15, 16; 1, 2, 3, 4; 5, 6, 7, 8]