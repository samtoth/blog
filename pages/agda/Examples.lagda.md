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

  A B C : Vector 3
  A = λ where fzero               →  1
              (fsuc fzero)        →  2
              (fsuc (fsuc fzero)) →  6

  B = λ where fzero               → -1
              (fsuc fzero)        → -2
              (fsuc (fsuc fzero)) → -1
              
  C = λ where fzero               →  8
              (fsuc fzero)        →  16
              (fsuc (fsuc fzero)) →  3

  exampleEq : Fin 2 → Vector 3
  exampleEq fzero = A
  exampleEq (fsuc fzero) = B

  eq : LinearEquation 2 3
  eq = exampleEq , C

  open LinearComb 3 2 exampleEq

  aSpan : Solution eq
  aSpan = (λ where fzero               → -1
                   (fsuc fzero)        → -9) ,
          ext (λ where fzero               → same-difference refl
                       (fsuc fzero)        → same-difference refl
                       (fsuc (fsuc fzero)) → same-difference refl)

```