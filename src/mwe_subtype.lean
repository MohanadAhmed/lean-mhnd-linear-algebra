import data.matrix.basic
import data.matrix.notation

def A := !![1, 2, 3, 4; 5, 6, 7, 8; 9, 10, 11, 12; 13, 14, 15, 16]
def r := λ i, ((i + 1): fin 4)
#eval A.submatrix r r /- Gives the nice matrix !![6, 7, 8, 5; 10, 11, 12, 9; 14, 15, 16, 13; 2, 3, 4, 1] -/

def valsx: (list ℕ) := [0, 1, 2, 0] 
def myF (i : fin 4) := (list.nth_le valsx i (fin.is_lt i))
def Froots := finset.subtype {i: fin 4 | myF i = 0}
def nroots := finset.subtype {i: fin 4 | ¬(myF i = 0)}
