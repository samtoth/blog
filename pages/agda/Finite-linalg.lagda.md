```agda
open import Cat.Prelude hiding (_+_; _*_)
open import Cat.Displayed.Univalence.Thin
open import Data.Dec.Base
open import Data.Nat renaming (Nat to ℕ; _+_ to _+N_; _*_ to _*ℕ_) hiding (*-zeror;*-associative)
open import Data.Fin
open import Data.Vec.Base
open import Algebra.Ring
open import Algebra.Ring.Module
open import Data.Dec
open import Algebra.Group.NAry
open import Algebra.Group
open import Algebra.Group.Ab
```


```agda
module Finite-linalg {ℓ} (R : Ring ℓ) where

open import LinearAlgNotes R
open import Algebra.Ring.Module.Vec R

open Ring-on (R .snd) hiding (_↪_)
private instance
  Rnum : Number ⌞ R ⌟
  Rnum = R-number

private instance
  Rneg : Negative ⌞ R ⌟
  Rneg = R-negative
  
```

The category of finite spaces has natural numbers as it's objects
and as homs, n×m matrices of the underlying ring $R$.

```agda
Matrix : ℕ → ℕ → Type ℓ
Matrix n m = Fin n → Vector m
```

```agda
ConstantV : ∀ {n} → ⌞ R ⌟ → Vector n
ConstantV n = λ _ → n

tailV : ∀ {n} → Vector (suc n) → Vector n
tailV v n = v (fsuc n)

DiagonalM : ∀ {n} → Vector n → Matrix n n
DiagonalM {zero} v ()
DiagonalM {suc n} v fzero fzero = v 0
DiagonalM {suc n} v fzero (fsuc _) = 0
DiagonalM {suc n} v (fsuc _) fzero = 0
DiagonalM {suc n} v (fsuc i) (fsuc j) = DiagonalM (λ x → v (fsuc x)) i j

UndiagonalM : ∀ {n} → (v : Vector n) → ∀ k → DiagonalM v k k ≡ v k
UndiagonalM v fzero = refl
UndiagonalM v (fsuc k) = UndiagonalM (λ n → v (fsuc n)) k

zeroNonDiag : ∀ {n} (v : Vector n) → ∀ i j → ¬ i ≡ j → DiagonalM v i j ≡ 0r
zeroNonDiag v fzero fzero p = absurd (p refl)
zeroNonDiag v fzero (fsuc j) p = refl
zeroNonDiag v (fsuc i) fzero p = refl
zeroNonDiag v (fsuc i) (fsuc j) p = zeroNonDiag (λ i → v (fsuc i)) i j λ q → p (ap fsuc q)

transposeM : ∀ {n m} → Matrix n m → Matrix m n
transposeM A i j = A j i

transposeDiag : ∀ {n} (v : Vector n) → transposeM (DiagonalM v) ≡ DiagonalM v
transposeDiag {n} v = ext go where
  go : ∀ (i j : Fin n) → _
  go i j with i ≡? j 
  ... | yes p = J (λ k p' → DiagonalM v k i ≡ DiagonalM v i k) refl p
  ... | no ¬p = zeroNonDiag v j i (λ p → ¬p (sym p)) ∙ sym (zeroNonDiag v i j ¬p)
```

```agda
private
  *-ab : Abelian-group-on ⌞ R ⌟
  *-ab = Module-on→Abelian-group-on (representable-module R .snd)

  *-grp : Group-on ⌞ R ⌟
  *-grp = Abelian→Group-on *-ab 

```

```agda
IdentityM : ∀ {n} → Matrix n n
IdentityM = DiagonalM (ConstantV 1r)

SumColId : ∀ {n} k → ∑ *-grp (IdentityM {n} k) ≡ 1r
SumColId {suc n} fzero = ap (1r +_) (∑-zero {n} *-grp) ∙ +-idr {1r}
SumColId {suc n} (fsuc k) = +-idl ∙ SumColId k

_*M_ : ∀ {n m k} → Matrix n m → Matrix m k → Matrix n k
(A *M B) i j = ∑ *-grp (λ e → A i e * B e j)

IdM-lid : ∀ {n m} (B : Matrix n m) → IdentityM *M B ≡ B
IdM-lid {0} B = funext (λ ())
IdM-lid {suc _} B = ext (go B) where
  go : ∀ {n} {m} (B : Matrix n m) → (i : Fin n) → (j : Fin m) → ∑ *-grp (λ e → IdentityM i e * B e j) ≡ B i j
  go {suc n} B fzero j 
    = (1r * B 0 j) + ∑ *-grp (λ e → 0 * B (fsuc e) j)   ≡⟨ ap (_+ ∑ *-grp (λ e → 0 * B (fsuc e) j)) *-idl ⟩
      B fzero j + ∑ *-grp (λ e → 0r * B (fsuc e) j)     ≡⟨ (λ i → B fzero j + ∑ *-grp (λ e → *-zerol {_} {_} {_} {B (fsuc e) j} i)) ⟩
      B fzero j + ∑ {n} *-grp (λ e → 0r)                ≡⟨ ap (B fzero j +_) (∑-zero {n} *-grp) ⟩
      B fzero j + 0r                                    ≡⟨ +-idr ⟩
      B fzero j ∎
  go {suc n} {suc m} B (fsuc i) fzero 
    = (0r * B 0 0) + ∑ *-grp (λ e → IdentityM (fsuc i) (fsuc e) * B (fsuc e) fzero)    ≡⟨ ap (_+ ∑ *-grp (λ e → IdentityM (fsuc i) (fsuc e) * B (fsuc e) fzero)) *-zerol ∙ +-idl ⟩
      ∑ *-grp (λ e → IdentityM i e * B (fsuc e) fzero)                                 ≡⟨ ∑-diagonal-lemma *-grp i _ (ap (_* _) (UndiagonalM (ConstantV _) i) ∙ *-idl) (λ j p → ap (_* _) (zeroNonDiag _ i j p) ∙ *-zerol) ⟩
      B (fsuc i) fzero ∎
  go B (fsuc i) (fsuc j) 
    = (0r * B _ _) + ∑ *-grp (λ e → IdentityM (fsuc i) (fsuc e) * B (fsuc e) (fsuc j)) ≡⟨ ap (_+ ∑ *-grp (λ e → IdentityM (fsuc i) (fsuc e) * B (fsuc e) _)) *-zerol ∙ +-idl ⟩
      ∑ *-grp (λ e → IdentityM (fsuc i) (fsuc e) * B (fsuc e) (fsuc j))                ≡⟨ go (λ i j → B (fsuc i) (fsuc j)) i j ⟩
      B (fsuc i) (fsuc j) ∎

IdM-rid : ∀ {n m} (B : Matrix n m) → B *M IdentityM ≡ B
IdM-rid {zero} B = funext (λ ())
IdM-rid {suc _} B = ext (go B) where
  go : ∀ {n} {m} (B : Matrix n m) → (i : Fin n) → (j : Fin m) → ∑ *-grp (λ e → B i e * IdentityM e j) ≡ B i j
  go {suc n} {suc m} B i fzero
    = (B i 0) * 1r + ∑ *-grp (λ e → B i (fsuc e) * 0)  ≡⟨ ap (_+ ∑ *-grp (λ e → B i (fsuc e) * 0)) *-idr ⟩
      B i 0 + ∑ {m} *-grp (λ e → B i (fsuc e) * 0r)    ≡⟨ (λ j → B i fzero + ∑ *-grp (λ e → *-zeror {_} {_} {_} {B i (fsuc e)} j)) ⟩
      B i 0 + ∑ {m} *-grp (λ e → 0r)                   ≡⟨ ap (B i fzero +_) (∑-zero {m} *-grp) ∙ +-idr ⟩
      B i fzero ∎
  go {suc n} B fzero (fsuc j) 
    = B 0 0 * 0r + ∑ *-grp (λ e → B fzero (fsuc e) * IdentityM (fsuc e) (fsuc j)) ≡⟨ ap (_+ ∑ *-grp (λ e → B fzero (fsuc e) * IdentityM (fsuc e) (fsuc j))) *-zeror ∙ +-idl ⟩
      ∑ *-grp (λ e → B fzero (fsuc e) * IdentityM (fsuc e) (fsuc j))              ≡⟨ ∑-diagonal-lemma *-grp j _ (ap (_ *_) (UndiagonalM (ConstantV _) j) ∙ *-idr) (λ i p → ap (_ *_) (zeroNonDiag _ i j (λ p' → p (sym p'))) ∙ *-zeror) ⟩
      B fzero (fsuc j) ∎
  go {suc n} {suc m} B (fsuc i) (fsuc j) 
    = (B (fsuc i) fzero * 0) + ∑ *-grp (λ e → B (fsuc i) (fsuc e) * IdentityM (fsuc e) (fsuc j))      ≡⟨ ap (_+ (∑ *-grp (λ e → B (fsuc i) (fsuc e) * IdentityM (fsuc e) (fsuc j)))) *-zeror ∙ +-idl ⟩
      ∑ *-grp (λ e → B (fsuc i) (fsuc e) * IdentityM (fsuc e) (fsuc j))                               ≡⟨ go (λ i j → B (fsuc i) (fsuc j)) i j ⟩
      B (fsuc i) (fsuc j) ∎

∑-commute : ∀ {n m} (f : Fin n → Fin m → ⌞ R ⌟) → ∑ {n} *-grp (λ e → ∑ {m} *-grp (f e)) ≡ ∑ *-grp (λ e' → ∑ *-grp (λ e → f e e'))
∑-commute {zero} {m} f = sym (∑-zero {m} *-grp)
∑-commute {suc n} {m} f 
  = ∑ *-grp (f fzero) + ∑ *-grp (λ e → ∑ *-grp (f (fsuc e)))             ≡⟨ ap (∑ *-grp (f fzero) +_) (∑-commute (λ e → f (fsuc e))) ⟩
    ∑ *-grp (f fzero) + ∑ *-grp (λ e' → ∑ *-grp (λ e → f (fsuc e) e'))   ≡⟨ sym (∑-split *-ab (f fzero) (λ e' → ∑ *-grp (λ e → f (fsuc e) e'))) ⟩
    ∑ *-grp (λ e' → (f fzero e') + ∑ *-grp (λ e → f (fsuc e) e'))        ∎

∑-distr-r : ∀ {n} (f : Fin n → ⌞ R ⌟) → (r : ⌞ R ⌟) → ∑ {n} *-grp (λ e → f e * r) ≡ ∑ *-grp f * r
∑-distr-r {zero} f r = sym *-zerol
∑-distr-r {suc n} f r 
  = (f 0 * r) + ∑ *-grp (λ e → f (fsuc e) * r) ≡⟨ ap (f 0 * r +_) (∑-distr-r (λ e → f (fsuc e)) r) ⟩
    (f 0 * r) + ∑ *-grp (λ e → f (fsuc e)) * r ≡⟨ sym *-distribr ⟩
    (f 0 + ∑ *-grp (λ e → f (fsuc e))) * r     ≡⟨ refl ⟩
    ∑ *-grp f * r ∎

IdM-assoc : ∀ {n m k l} (A : Matrix n m) (B : Matrix m k) (C : Matrix k l) → (A *M B) *M C ≡ A *M (B *M C)
IdM-assoc A B C = ext (go A B C) where
  go : ∀ {n m k l} → (A : Matrix n m) → (B : Matrix m k) → (C : Matrix k l) → (i : Fin n) → (j : Fin l) 
    → ∑ *-grp (λ e → ∑ *-grp (λ e' → A i e' * B e' e) * C e j) ≡ ∑ *-grp (λ e → A i e * ∑ *-grp (λ e' → B e e' * C e' j))
  go {n} {m} {k} {l} A B C i j 
    = ∑ *-grp (λ e → ∑ *-grp (λ e' → A i e' * B e' e) * C e j)    ≡⟨ ap (∑ {k} *-grp) (funext λ e → sym (∑-distr-r (λ e' → A i e' * B e' e) (C e j))) ⟩
      ∑ *-grp (λ e → ∑ *-grp (λ e' → A i e' * B e' e  * C e j))   ≡⟨ ∑-commute (λ e e' → A i e' * B e' e  * C e j) ⟩
      ∑ *-grp (λ e' → ∑ *-grp (λ e → A i e' * B e' e  * C e j))   ≡⟨ ap (∑ {m} *-grp) (funext (λ e → ap (∑ {k} *-grp) (funext λ e' → sym *-associative))) ⟩
      ∑ *-grp (λ e' → ∑ *-grp (λ e → A i e' * (B e' e  * C e j))) ≡⟨ sym (ap (∑ *-grp) (funext λ e' → ∑-distr (representable-module R) (A i e') λ e → B e' e  * C e j)) ⟩
      ∑ *-grp (λ e' → A i e' * ∑ *-grp (λ e → B e' e  * C e j))   ∎
```

```agda
R-mod : Precategory lzero ℓ
R-mod .Precategory.Ob = ℕ
R-mod .Precategory.Hom n m = Matrix m n
R-mod .Precategory.Hom-set _ _ = hlevel!
R-mod .Precategory.id = IdentityM
R-mod .Precategory._∘_ A B = A *M B
R-mod .Precategory.idr = IdM-rid
R-mod .Precategory.idl = IdM-lid
R-mod .Precategory.assoc f g h = sym (IdM-assoc f g h)
``` 

```agda
*M-linear : ∀ {m n} → Matrix m n → Linear-map (Fin-vec-module n) (Fin-vec-module m)
*M-linear {0} {n} A = record { map = λ v () ; lin = record { linear = λ where r s t i () } }

*M-linear {suc m} {n} A .Algebra.Ring.Module.map v i = (_*M_ {1} {n} {suc m} (λ _ x → v x) (transposeM A)) fzero i
*M-linear {suc m} {n} A .lin .linear r s t = funext (go r s t) where
  go : ∀ r s t (i : Fin (suc m)) →  ((λ _ →
          (Fin-vec-module n .snd Module-on.+
          (Fin-vec-module n .snd Module-on.⋆ r) s)
          t)
          *M transposeM A)
            (fzero {n}) i
          ≡
          (Fin-vec-module (suc m) .snd Module-on.+
          (Fin-vec-module (suc m) .snd Module-on.⋆ r)
          (λ i → ((λ _ → s) *M transposeM A) (fzero {n})i))
          (λ i → ((λ _ → t) *M transposeM A) (fzero {n}) i) i
  go r s t i 
    = ∑ *-grp (λ e → (r * (s e) + (t e))*(A i e))                     ≡⟨ ap (∑ {n} *-grp) (funext (λ e → *-distribr)) ⟩
      ∑ *-grp (λ e → ((r * s e) * A i e) + (t e * A i e))             ≡⟨ ap (∑ {n} *-grp) (funext (λ e → ap (_+ (t e * A i e)) (sym *-associative))) ⟩
      ∑ *-grp (λ e → (r * (s e * A i e)) + (t e * A i e))             ≡⟨ ∑-split *-ab (λ e →  r * (s e * A i e)) (λ e → t e * A i e) ⟩
      ∑ *-grp (λ e → r * (s e * A i e)) + ∑ *-grp (λ e → t e * A i e) ≡⟨ ap (_+ ∑ *-grp (λ e → t e * A i e)) (sym (∑-distr (representable-module R) r (λ e → s e * A i e))) ⟩
      r * ∑ *-grp (λ e → s e * A i e) + ∑ *-grp (λ e → t e * A i e)   ∎


include : Functor R-mod (R-Mod R ℓ)
include .Functor.F₀ = Fin-vec-module
include .Functor.F₁ A = linear-map→hom (*M-linear A)

include .Functor.F-id {zero} = ext (λ x ())
include .Functor.F-id {suc x} = ext (λ v i → ap (λ e → ((λ _ → v) *M e) (fzero {x}) i) (transposeDiag (ConstantV 1r)) ∙ happly (happly (IdM-rid λ _ → v) (fzero {x})) i)

include .Functor.F-∘ {x} {y} {zero} f g = ext (λ i ())
include .Functor.F-∘ {x} {zero} {suc z} f g = ext (λ v j → ap (∑ {x} *-grp) (funext (λ _ → *-zeror)) ∙ ∑-zero {x} *-grp)
include .Functor.F-∘ {zero} {suc y} {suc z} f g = ext go where
  go : (v : _) → (i : _) → _
  go v i = sym (
    0r * _ + _                          ≡⟨ ap (_+ ∑ {y} *-grp (λ e → 0r * f i (fsuc e))) *-zerol ∙ +-idl ⟩
    ∑ *-grp (λ e → 0r * (f i (fsuc e))) ≡⟨ ap (∑ {y} *-grp) (funext (λ e → *-zerol)) ∙ ∑-zero {y} *-grp ⟩
    0r ∎
    ) 
include .Functor.F-∘ {suc x} {suc y} {suc z} f g = ext (λ v j → 
    {!   !} ≡⟨ {!   !} ⟩
    ((v 0 * g 0 0 + ∑ {x} *-grp (λ e → v (fsuc e) * g 0 (fsuc e))) * f j fzero) + ∑ {y} *-grp (λ e2 → ((v 0 * g (fsuc e2) 0) + ∑ {x} *-grp λ e3 → v (fsuc e3) * g (fsuc e2) (fsuc e3)) * f j (fsuc e2)) ∎
    )
 
``` 