Constructing Uemeras notion of categories with representable maps

```agda
module CwR where

open import Cat.Prelude
open import Cat.Diagram.Limit.Finite
open import Cat.Functor.WideSubcategory
open import Cat.Diagram.Everything
open import Cat.Functor.Pullback
open import Cat.Instances.Slice
open import Cat.Functor.Adjoint
open import Cat.Displayed.Base
open import Cat.Displayed.Cartesian.Discrete
open import Cat.Displayed.Total
open import Cat.Displayed.Functor
open import Cat.Displayed.Composition

import Cat.Reasoning
```

First we note that a CwR is a cartesian category with a class $\cR$ of representable maps,
which is stable under pullback.

```agda
record CwR {o ℓ} r (𝓒 : Precategory o ℓ) : Type (o ⊔ ℓ ⊔ lsuc r) where
    open Cat.Reasoning 𝓒 public

    field
      has-is-lex : Finitely-complete 𝓒
      R          : Wide-subcat {C = 𝓒} r

    open Finitely-complete has-is-lex public

    module R = Wide-subcat R

    field
      R-stable : is-pullback-stable 𝓒 R.P
      f*       : ∀ {A B} → {f : Hom A B} → R.P f → Functor (Slice 𝓒 A) (Slice 𝓒 B)
      f⊣f*     : ∀ {A B} → {f : Hom A B} → (Rf : R.P f) → Base-change pullbacks f ⊣ f* Rf
```


<!--
```agda
private unquoteDecl Vf-eqv = declare-record-iso Vf-eqv (quote Vertical-functor)

Vertical-functor-is-set : ∀ {o} {B} {C D : Displayed B o o} → Discrete-fibration D
            → is-set (Vertical-functor C D)
Vertical-functor-is-set {C} {D} discrete =
  Iso→is-hlevel 2 Vf-eqv (hlevel 2)
  where
    open Displayed.Displayed-HLevel-instance D
    module D = Displayed D
    open Discrete-fibration discrete
    instance
      Dob : ∀ {x} → H-Level (D.Ob[ x ]) 2
      Dob = basic-instance 2 (fibre-set _)
```   
-->

```agda
module _ {o ℓ} r {𝓒 : Precategory o ℓ} (C : CwR r 𝓒) (S : Precategory o ℓ) where

  open CwR C

  data IterDFib (X : Ob) : Type (lsuc o ⊔ ℓ)
  Unfold : ∀ {A} → (I : IterDFib A) → Displayed S o o
  
  
  data IterDFib X where
    base   : ∀ (C : Displayed S o o) → Discrete-fibration C → IterDFib X
    extend : ∀ {A} (f : Hom A X) → (idf : IterDFib A) → (C : Displayed (∫ (Unfold idf)) o o) → Discrete-fibration C → IterDFib X

  Unfold (base C x) = C
  Unfold (extend f x C x₁) = Unfold x D∘ C

  Unfold-discrete : ∀ {X} (I : IterDFib X) → Discrete-fibration (Unfold I)
  Unfold-discrete (base C x) = x
  Unfold-discrete (extend f x C x₁) = {! discrete∘  !}
 
  RIterDFib : ∀ {X} → IterDFib X → Type (o ⊔ ℓ)
  RIterDFib (base C x) = Lift _ ⊤
  RIterDFib (extend f A' B' Bd) = Σ[ Extend ∈ Functor (∫ (Unfold A')) (∫ B') ] (πᶠ B' ⊣ Extend)

  -- record ItDFibs-Ob : Type (lsuc (o ⊔ ℓ)) where
  --   constructor IDF
  --   field 
  --     {a b} : Ob
  --     {f} : Hom a b
  --     dfib : IterDFib b
  --     resp-R : RIterDFib dfib

  ItDFibs : Displayed 𝓒 _ _
  Displayed.Ob[ ItDFibs ] x = Σ (IterDFib x) RIterDFib
  Displayed.Hom[ ItDFibs ] f (A , _) (B , _) = Vertical-functor (Unfold A) (Unfold B)
  Displayed.Hom[ ItDFibs ]-set f (A , _) (B , _) = Vertical-functor-is-set S (Unfold-discrete B)
  ItDFibs .Displayed.id' = {!   !}
  ItDFibs .Displayed._∘'_ = {!   !}
  ItDFibs .Displayed.idr' = {!   !}
  ItDFibs .Displayed.idl' = {!   !}
  ItDFibs .Displayed.assoc' = {!   !}
     
```  