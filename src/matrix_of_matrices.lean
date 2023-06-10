import data.matrix.basic
import data.complex.basic
import data.matrix.rank
import linear_algebra.matrix.determinant
import linear_algebra.matrix.schur_complement

def A11 := !![(1:ℝ), 0; 0, 1;]
def A12 := !![(1:ℝ), 0; 0, 2;]
def A21 := !![(1:ℝ), 0; 0, 1;]
def A22 := !![(1:ℝ), 0; 0, 2;]

def A := !![
  A11, A12; 
  A21, A22;
]
