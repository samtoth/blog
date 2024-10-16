<!--
```agda
open import Cat.Prelude
import LinearAlgNotes
open import Algebra.Ring.Cat.Initial
open import Data.Fin
open import Data.Int.HIT
```
-->

```agda
module Examples where

module Equation-in-Z where

  open LinearAlgNotes {lzero} Liftℤ
  
  private instance
    numInt : Number ⌞ Liftℤ ⌟
    numInt = R-number
    numNeg : Negative ⌞ Liftℤ ⌟
    numNeg = R-negative
```


```agda
  A B C D : Vector 3
  A = λ where fzero               →  1
              (fsuc fzero)        →  2
              (fsuc (fsuc fzero)) →  3

  B = λ where fzero               →  2
              (fsuc fzero)        → -3
              (fsuc (fsuc fzero)) →  1
              
  C = λ where fzero               →  3
              (fsuc fzero)        →  2
              (fsuc (fsuc fzero)) → -1

  D = λ where fzero               →  6
              (fsuc fzero)        → 14
              (fsuc (fsuc fzero)) → -2

  exampleEq : Fin 3 → Vector 3
  exampleEq fzero = A
  exampleEq (fsuc fzero) = B
  exampleEq (fsuc (fsuc fzero)) = C

  eq : LinearEquation 3 3
  eq = exampleEq , D

  open LinearComb 3 3 exampleEq
```

## Elimination method for solving linear equations:

3 ops
 - Scaling eq by non zero number
 - Swapping two equations
 - Replace $R_i = R_i + cR_j$ where $c \neq 0$.

 Replacement example

$$
\begin{align}
\begin{cases}
 x + 2y + 3z = 6 \\
 2x - 3y + 2z = 14 \\
 3x + y - z = -2 
\end{cases} =&
\begin{cases}
 x + 2y + 3z = 6 \\
 -7y - 4z = 2\ \ (R_2 = R_2 - 2R_1) \\
 -5y - 10z = -20 \ \ (R_3 = R_3 - 3R_1) 
\end{cases} \\ = 
\begin{cases}
 x + 2y + 3z = 6 \\
 -7y - 4z = 2 \\
 y + 2z = 4 \ \ (R_3 = -1/5 R_3) 
\end{cases} =_{R_2 \leftrightarrow R_3}&
\begin{cases}
 x + 2y + 3z = 6 \\
 y + 2z = 4 \\ 
 -7y - 4z = 2 \\
\end{cases} \\=
\begin{cases}
 x + 2y + 3z = 6 \\
 y + 2z = 4 \\ 
 z = 3\ (R_3 = \frac{1}{10}(R_3 + 7R_2)) \\ 
\end{cases} =&
\begin{cases}
 x + 2y = -3\ (R_1 = R_1 - 3R_3) \\
 y = -2\ (R_2 = R_2 - 2R_3) \\
 z = 3\\ 
\end{cases}\\ =& 
\begin{cases}
x = 1\ (R_1 = R_1 - 2R_2) \\
y = -2 \\
z = 3\\ 
\end{cases}
\end{align}
$$

Note see sec 2.2-2.3 in Ulrichs book for red row echelon form (rref).
*Stuff about using augmentation matrices* 



```agda
  aSpan : Solution eq
  aSpan = (λ where fzero               →  1
                   (fsuc fzero)        → -2
                   (fsuc (fsuc fzero)) →  3) ,
          ext (λ where fzero               → same-difference refl
                       (fsuc fzero)        → same-difference refl
                       (fsuc (fsuc fzero)) → same-difference refl)
 
```