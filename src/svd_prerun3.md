# Formalization of Singular Value Decomposition in Lean

Let $m,n,r$ be three natural numbers. Let $A \in \mathbb{C}^{m\times n}$ be an $m\times n$ comlpex matrix. There exist three matrices $U \in \mathbb{C}^{m \times m},S \in \mathbb{R}^{m \times n},V \in \mathbb{C}^{n \times n}$ such that $$A=USV^H$$
with $$ U^HU = I_m\quad UU^H=I_m\quad V^HV=I_n\quad VV^H=I_n$$
Given that $r = \text{rank}(A)$, the matrices $U,S,V$ can be partitioned as follows:
$$
A = 
\begin{bmatrix}U_1 & U_2\end{bmatrix}
\begin{bmatrix}S_{11} & 0 \\ 0 & 0 \end{bmatrix}
\begin{bmatrix}V_1 & V_2\end{bmatrix}^H
$$
such that
$$\begin{aligned}
U_1  &\in \mathbb{C}^{m \times r}  & U_2 &\in \mathbb{C}^{m \times (m-r)}\\ 
S_{11} &\in\mathbb{R}^{r\times r} \\
V_1  &\in \mathbb{C}^{n \times r}  & V_2 &\in \mathbb{C}^{n \times (n-r)}
\end{aligned}

$$

<!-- with $U_1 \in \mathbb{C}^{m \times r}, U_2 \in \mathbb{C}^{m \times (m-r)}, S_{11}\in\mathbb{R}^{r\times r}, V_1 \in \mathbb{C}^{n \times r}, V_2 \in \mathbb{C}^{n \times (n-r)}$ -->

## Outline of the Proof
We will denote by $[n] \triangleq \{0, 1, 2, 3 \ldots n-1\}$

1. $A^H A$ is a hermitian matrix: already in mathlib.
1. Let $\mu: [n] \to \mathbb{R}$ be the function that computes the eigenvalues of the matrix $A^H A$.
1. Let the matrix $D_V = \text{Diag} \;{\mu [n]}$ be the real matrix of $n\times n$.
    * The real matrix $D_n$ can be upgraded to a complex matrix with the obvious inclusion of reals into complexes.
1. $A^HA = V_nD_cV_n^H$ by the spectral theorem of hermitian matrices.
1. Let $p_n: [n] \to \text{Prop}$ be a predicate that assigns true to non-zero eigenvalues and false otherwise, i.e $$p_n(a) \triangleq (\mu(a) \neq 0)$$
1. Using this predicate we can form an equivalence $$e_n: [n] \cong [n_+] \oplus [n_0]$$ with: $$[n_+] \triangleq \{a \in [n] \; | \; \mu(a) \neq 0\}, \quad [n_0] \triangleq \{a \in [n] \; | \; \mu(a) = 0\}$$
    * Note that equivalence does not say anything about the order of the eigenvalues, just that they are separated into non-zero and zero eigenvalues. There are $r!\times (n-r)!$ such equivlences!
1. Using the equivalence $e_n$ we partition $V_n$ into two column matrices: $$V = \text{reindex}[\text{id},e_n]\{V_n\} = \begin{bmatrix}V_1 & V_2\end{bmatrix}$$
1. Using the equivalence $e_n$ we partition $D_n$ into 4 matrices: $$D = \text{reindex}[e_n,e_n]\{D_n\} = \begin{bmatrix}D_{11} & D_{12} \\ D_{21} & D_{22}\end{bmatrix}$$
 We then show that: 
    * $D_{12}=0$, $D_{21}=0$ on account of being off-diagonal entries of a diagonal matrix.
    * and $D_{22} = 0$ since off-diagonal elements are also off diagonals of the original $D_n$ and its diagonal elements are zero by the condition of the predicate.
    * and $D_{11}$ is a diagonal matrix. Consider $\mu_p: [n_p] \to \mathbb{R}$, the restriction of $\mu$ to the set $[n_p]$. Then: $$ D_{11} = \text{Diag}\; \mu_p [n_p]$$
1. Since $D_{12}=0, D_{21}=0, D_{22}=0$ we can reduce the spectral theorem into: $$A^HA = V_1D_{11}V_1^H$$
1. Define $S'_\sigma$, the non-zero singular values matrix as: $$S'_\sigma = \text{Diag}\; \sqrt{\mu_p [n_p]} $$.
    * Show that the inverse of $S'_\sigma$ is given by: $${S'}_\sigma^{-1} = \text{Diag}\; 1/\sqrt{\mu_p [n_p]} $$
    * We also prove that the determinant is non-zero for when we need it. [Check if we can do both using invertible like Eric Wieser did in his inv-block branch on mathlib.]
1. We show that the "sandwiched" product is identity: $${S'}_\sigma^{-1} D_{11} {S'}_\sigma^{-1} = I $$
1. We show that: $$V_1^HV_1 = I, V_1^HV_2 = 0, V_2^HV_1 = 0, V_2^HV_2=I$$
1. We show that: $V_1V_1^H + V_2V_2^H = I$. Thus: $$\begin{bmatrix}V_1 & V_2\end{bmatrix}\begin{bmatrix}V_1 & V_2\end{bmatrix}^H = I$$
1. Define $$U'_1 = AV_1{S'}_\sigma^{-1}$$
    We show that:
    *  $U_1'^HU_1' = I$
    * $U_1'S'_\sigma = AV_1$
1. We show that: $$AV_2 = 0$$
1. $AA^H$ is also a hermitian matrix. The spectral theorem gives: $AA^H = U_mD'U_m^H$
    * Let $\mu': [m] \to \mathbb{R}$ be a function computes the eigenvalues of $AA^H$. 
    * Let $p_m: [m] \to \text{Prop} \triangleq a \to \mu'(a) = 0$ be a predicate that checks whether the $\mu'$  is positive or zero.
    * Form the equivalence $e_m$ such that: $e_m \cong [m_+] \oplus [m_0]$ with $[m_+] = \{a \in m \; | \; p_m a\}$ and $[m_0] = \{a \in m \; | \; \neg p_m a\}$
    * Define $U_2$ as the zero corersponding eigenvectors of $U_m$: $$ U' = \text{reindex}[id, e_m]\{U_m\} = \begin{bmatrix} * & U_2 \end{bmatrix}$$
1. We show that: $$AA^HU_2 = 0$$
1. The above implies $A^H U_2 = 0$.
1. We show that $U_1'^HU_2 = 0, U_2^HU_1' = 0, U_2^HU_2 = I$. 
    Further we show that: 
    * we can form an equivalence $e_{mn} \triangleq [m_+] \cong [n_+]$ since both sets have equal cardinality. $|[m_+]| = r = |[n_+]|$
    * We can reindex $U_1'$ and $S'_\sigma$ using the new equivlence to obtain: $$U_1 = \text{reindex}[id, e_{mn}]\{U_1'\} \quad S_\sigma = \text{reindex}[e_{mn}, id]\{S_\sigma\}$$
    *We can then show that 

    $$\begin{bmatrix}U_1 & U_2\end{bmatrix}^H \begin{bmatrix}U_1 & U_2\end{bmatrix} = I$$
1. We show that: $AV_1 = U_1'S'_\sigma = U_1S_\sigma$. Then we get: $$A\begin{bmatrix}V_1 & V_2\end{bmatrix} = \begin{bmatrix}U_1 & U_2\end{bmatrix}\begin{bmatrix}S_\sigma & 0 \\ 0 & 0\end{bmatrix}$$
1. Finally we show that: $$A = \begin{bmatrix}U_1 & U_2\end{bmatrix}\begin{bmatrix}S_\sigma & 0 \\ 0 & 0\end{bmatrix}\begin{bmatrix}V_1 & V_2\end{bmatrix}^H$$
