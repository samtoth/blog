

# Shallower deep embedding

```agda
open import Cat.Prelude
import Cat.Reasoning

module Theories.ShallowerDeep {o h : Level} (Σ : Precategory o h) where
open Cat.Reasoning Σ
```

```agda 
data Ty : Type o where
    Base : Ob → Ty
    _⇒_  : Ty → Ty → Ty


data Ctx : Type o where
    ∅   : Ctx
    _⨾_ : Ctx → Ty → Ctx

infixl 20 _⨾_

variable
    X Y Z : Ob
    Γ Δ E : Ctx
    A B   : Ty

data Var : Ctx → Ty → Type o where
    here  : Var (Γ ⨾ A) A
    there : Var Γ A → Var (Γ ⨾ B) A

variable
    ν υ : Var Γ A

data Term : Ctx → Ty → Type (o ⊔ h)

data Term where
    lam : (t : Term (Γ ⨾ A) B) → Term Γ (A ⇒ B)
    app : (f : Term Γ (A ⇒ B)) → (x : Term Γ A) → Term Γ B
    var : (ν : Var Γ A) → Term Γ A

    fun : Hom X Y → Term Γ (Base X ⇒ Base Y)

data Sub (Γ : Ctx) : Ctx → Type (o ⊔ h) where
    !     : Sub Γ ∅
    ⟨_,_⟩ : Sub Γ Δ → Term Γ A → Sub Γ (Δ ⨾ A)

record Weakens (Γ Δ : Ctx) : Type (o ⊔ h) where
    field wkSub : Sub Δ Γ
    field wkTm : Term Γ A → Term Δ A


open Weakens {{...}}




private
    {-# TERMINATING #-}
    weakUnder : ∀ {Γ Δ} {A B} → (∀ {A} → Term Γ A → Term Δ A) → Term (Γ ⨾ B) A → Term (Δ ⨾ B) A
    weakExt : ∀ {Γ} {A B} → Term Γ A → Term (Γ ⨾ B) A
    
    weakExt (lam x) = lam (weakUnder weakExt x)
    weakExt (app f x) = app (weakExt f) (weakExt x)
    weakExt (fun f) = fun f
    weakExt (var ν) = var (there ν)
    
    weakUnder f (lam x) = lam (weakUnder (weakUnder f) x)
    weakUnder f (app g x) = app (weakUnder f g) (weakUnder f x)
    weakUnder f (fun g) = fun g
    weakUnder f (var here) = var here
    weakUnder f (var (there ν)) = weakExt (f (var ν)) 

    weakHere : (Term Γ A → Term Δ A) → Term Γ A → Term (Δ ⨾ B) A
    weakHere f t = weakExt (f t)

extSub : Sub Γ Δ → Sub (Γ ⨾ A) Δ
extSub ! = !
extSub ⟨ σ , x ⟩ = ⟨ extSub σ , weakExt x ⟩

underSub : Sub Γ Δ → Sub (Γ ⨾ A) (Δ ⨾ A)
underSub σ = ⟨ extSub σ , var here ⟩

idSub : Sub Γ Γ
idSub {Γ = ∅} = !
idSub {Γ = Γ ⨾ x} = ⟨ extSub idSub , var here ⟩

instance
    WeakensBase : Weakens Γ Γ
    WeakensBase .Weakens.wkSub = idSub
    WeakensBase .Weakens.wkTm x = x

    WeakensUnder : {{_ : Weakens Γ Δ}} → Weakens (Γ ⨾ A) (Δ ⨾ A)
    WeakensUnder .Weakens.wkSub = underSub wkSub
    WeakensUnder .Weakens.wkTm = weakUnder wkTm

    WeakensExt : {{_ : Weakens Γ Δ}} → Weakens Γ (Δ ⨾ A)
    WeakensExt .Weakens.wkSub = extSub wkSub
    WeakensExt .Weakens.wkTm = weakHere wkTm

    Weakens! : Weakens ∅ Γ
    Weakens! .Weakens.wkSub = !
    Weakens! {∅} .Weakens.wkTm x = x
    Weakens! {Γ ⨾ A} .Weakens.wkTm t = weakHere wkTm t

{-# OVERLAPPING Weakens! #-}
{-# INCOHERENT WeakensUnder WeakensExt #-}

```

Now let's define some convenient syntax.

```agda
lamSyn : (Term (Γ ⨾ A) A → Term (Γ ⨾ A) B) → Term Γ (A ⇒ B)
lamSyn f = lam (f (var here))

infixr 5 lamSyn
syntax lamSyn (λ v → bod) = v ↦ bod

_⋆_ : (t : Term Γ (A ⇒ B)) → (x : Term Δ A) → {{tw : Weakens Γ E}} → {{xw : Weakens Δ E}} → Term E B
t ⋆ x  = app (wkTm t) (wkTm x)
infixl 10 _⋆_
infixr 5 _⇒_
```

And profit!!!

```agda
peano0 peano1 : Term Γ ((A ⇒ A) ⇒ (A ⇒ A))
peano0 = f ↦ x ↦ x
peano1 = f ↦ x ↦ f ⋆ x

peanoN : Nat → Term Γ ((A ⇒ A) ⇒ A ⇒ A)
peanoN n = f ↦ x ↦ help f x n where
    help : _ → _ → Nat → Term (Γ ⨾ (A ⇒ A) ⨾ A) A
    help f x 0 = x
    help f x (suc n) = f ⋆ help f x n

```
