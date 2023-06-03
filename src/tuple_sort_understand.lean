import data.matrix.basic
import data.matrix.notation
import data.int.basic
import data.fin.tuple.sort
import tactic.norm_fin
import tactic

open matrix
open_locale matrix big_operators
open equiv equiv.perm finset
open complex

def N := 4
def A := !![1, 2, 3, 4; 5, 6, 7, 8; 9, 10, 11, 12; 13, 14, 15, 16]
def valsx: (list (fin 10)) := [0, 1, 3, 0] 
def myF : fin 4 → (fin 10) := λ i, (list.nth_le valsx i (fin.is_lt i))
#eval fintype.elems (fin 4)
#check (tuple.sort myF)
def sList: fin 4 → (fin 4) := (λ i,  (tuple.sort myF) i)
#eval sList

