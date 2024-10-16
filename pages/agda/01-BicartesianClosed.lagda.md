<!--
```agda
open import Cat.Prelude hiding (⌜_⌝;_∧_;_∨_;¬_) renaming (⊤ to 𝟙; ⊥ to 𝟘)
open Functor
open import Cat.CartesianClosed.Instances.PSh 
open import Cat.Diagram.Product
import Cat.Morphism
import Cat.Reasoning
import Cat.Displayed.Reasoning
open import Cat.Diagram.Coproduct
open import Cat.Diagram.Terminal
open import Cat.Diagram.Initial
open import Cat.Diagram.Limit.Finite
open import Cat.Diagram.Colimit.Finite
open import Cat.Diagram.Exponential
open import Cat.Diagram.Pullback
open import Cat.Functor.FullSubcategory
open import Cat.Functor.Kan.Nerve
open import Cat.Diagram.Monad
open import Cat.Functor.Base
open import Cat.Functor.Adjoint
open import Cat.Instances.Comma
open import Cat.Instances.Shape.Interval
open import Cat.Instances.Slice
open import Cat.Displayed.Base
open import Cat.Displayed.Cartesian
open import Cat.Displayed.Total
open import Cat.Displayed.Instances.Pullback
open import Cat.Displayed.Instances.Slice
import Cat.Functor.Hom
open import Data.Bool
open import Data.List
```
-->

```agda
module 01-BicartesianClosed where
``` 


# Bi-cartesian closed categories and Proposition Logic

In my first year computer science degree we are doing a course on propositional
logic and I wanted to write small post to show the connection that exists 
between these logics and a special class of [[categories|category]] called bi-cartesian closed
categories.

As an extremely quick refresher, we are introduced to propositional logic as a theory
with boolean values usually denoted by letters $P,Q,R,S,...$, and a set of logical
connectives including $-\land-$, $-\lor-$, $-\Rightarrow-$ and $\neg-$ (with their usual meanings).
In addition we have the binary relation $P\vdash Q$ (pronounced entails) which externally
reflects the internal implication operator. i.e. $P\vdash Q$ just when $P\Rightarrow Q$ is a tautology.

If you are at all familiar with categories you might be starting to smell something here. It is quite
trivial to verify a few facts about entailment. Namely, any proposition entails itelf, and, given
$P\vdash Q$ and $Q\vdash R$ we can derive $P\vdash R$. There are many ways to verify this,
one such way being to use a truth table.
<details>
$((P \Rightarrow Q) \land (Q \Rightarrow R)) \Rightarrow (P \Rightarrow R)$ is a tautology
 as witnessed by the following truth table:

| P | Q | R | $P\Rightarrow Q$ | $Q\Rightarrow R$ | $P\Rightarrow R$ |
|---|---|---|---|---|---|
| 0 | 0 | 0 | 1 | 1 | 1 |
| 0 | 0 | 1 | 1 | 1 | 1 |
| 0 | 1 | 0 | 1 | 0 | 1 |
| 0 | 1 | 1 | 1 | 1 | 1 |
| 1 | 0 | 0 | 0 | 1 | 0 |
| 1 | 0 | 1 | 0 | 1 | 1 |
| 1 | 1 | 0 | 1 | 0 | 0 |
| 1 | 1 | 1 | 1 | 1 | 1 |
</details>



[`Homotopy Type Theory`]: 1Lab.Intro.html

From this, we have enough information to give a category of booleans and entailments beween them:

```agda
Bool⊢ : Precategory lzero lzero
```

Our objects are booleans and, as desired, there is a morphism only when the implication is true for
all x and y.
```agda
Bool⊢ .Precategory.Ob = Bool
Bool⊢ .Precategory.Hom x y = imp x y ≡ true
```

Both the identity entailment and the composition ot entailments are defined by
'pattern matching', which if you haven't come across before (in the special case
 of bools) you can think of a bit like writing down a truth table and considering
all different values of the variables involved. 

```agda
Bool⊢ .Precategory.id {true} = refl
Bool⊢ .Precategory.id {false} = refl

Precategory._∘_ Bool⊢ {true} {_}     {true}  _ _ = refl
Precategory._∘_ Bool⊢ {true} {true}  {false} x _ = x
Precategory._∘_ Bool⊢ {true} {false} {false} _ y = y
Precategory._∘_ Bool⊢ {false} {_}    {_}     _ _ = refl
```
<!--
```agda
Bool⊢ .Precategory.Hom-set x y = hlevel 2

Bool⊢ .Precategory.idr f = Bool-is-set _ _ _ _
Bool⊢ .Precategory.idl f = Bool-is-set _ _ _ _
Bool⊢ .Precategory.assoc f g h = Bool-is-set _ _ _ _
```
--->

So we now have the basic structure of a category down... but there is a lot more structure
to these entailment relations than just identity and composition right?
Well it turns out category theory already has a name for most of this structure... (no prizes
for guessing this one).
Before fully diving into Bicartesian-closed categories, let's consider a motivating 
example: $-\land-$.

It's defining properties are that both $P \land Q \vdash P$ and
$P \land Q \vdash Q$. In adition it is easy to check that given
that both $A \vdash P$ *and* $A \vdash Q$ then we must have
$A \vdash P \land Q$, This can be summed up in the following
diagram:

~~~{.quiver}
\[\begin{tikzcd}
  & A \\
  P & P \land Q & Q 
  \arrow[from=2-2, to=2-1]
  \arrow[from=2-2, to=2-3]
  \arrow[from=1-2, to=2-1]
  \arrow[from=1-2, to=2-2]
  \arrow[from=1-2, to=2-3]
\end{tikzcd}\]
~~~

Of course, this is looking very familiar, the good old categorical [[Product]].
Other examples you might have stumbled accross are cartesian products of
sets, and 'pair' types in Haskell. We can show formally that $-\land-$
is a product by the following term:

```agda
Bool-Products : has-products Bool⊢
Bool-Products a b .Product.apex = and a b

Bool-Products true true .Product.π₁ = refl
Bool-Products true false .Product.π₁ = refl
Bool-Products false b .Product.π₁ = refl

Bool-Products true b .Product.π₂ = id {b} where open Precategory Bool⊢
Bool-Products false b .Product.π₂ = refl

is-product.⟨_,_⟩ (Bool-Products true b .Product.has-is-product) {true} _ y = y
is-product.⟨_,_⟩ (Bool-Products false b .Product.has-is-product) {true} x _ = x
is-product.⟨_,_⟩ (Bool-Products a b .Product.has-is-product) {false} _ _ = refl
```
<!--
```agda
Bool-Products a b .Product.has-is-product .is-product.π₁∘factor = Bool-is-set _ _ _ _
Bool-Products a b .Product.has-is-product .is-product.π₂∘factor = Bool-is-set _ _ _ _
Bool-Products a b .Product.has-is-product .is-product.unique f g h = Bool-is-set _ _ _ _
```
--->

And so it turns out each of the operations that were introduced have a corresponding categorical
phrasing.

|  Proposition | limit  | Proposition | colimit  |
| --- | --- | --- | --- |
| $-\land-$ | [[Product]] | $-\lor-$ | [[Coproduct]] |
| $\top$ | [`Terminal`] | $\bot$ | [`Initial`] |
| $-\Rightarrow -$ | [`Exponential`] | ?? - not a very common thing | Coexponential | 

It is too much to cover in detail but if you explore the links you will be able to see how to give
a fairly trivial instance of each limit for our category `Bool⊢`.

When a category has all products and a terminal object, we say it is finitely complete, and
when it has the dual notion we say it is Finitely-cocomplete. On top of this we need a property
called cartesian closure which states that for all  Objects, A and B we need an object called their
exponential (think $A \implies B$ in the case of Boolean algebra) that behaves in specific way with
respect to products.

The defining property of this exponential is that $A \times B \vdash C$, just when
$A \vdash B \Rightarrow C$. The maps that take you from one to the other are called
_currying_ and _uncurrying_.
<details>
In full generallity, the exponential is defined as a functor $C \times C \to C$, such that
there is an ajunction: $- \times B \dashv - \rightarrow B$
</details>

So we will now describe what these special categories are in the language of type theory:

```agda
record Bicartesian-closed {o} {ℓ}  (𝓒 : Precategory o ℓ) : Type (o ⊔ lsuc ℓ) where
    field complete : Finitely-complete 𝓒
    field cocomplete : Finitely-cocomplete 𝓒

    open Finitely-complete complete
    open Finitely-cocomplete cocomplete

    field cc : Cartesian-closed 𝓒 products terminal

    open Cat.Reasoning 𝓒 renaming (Hom to _⊢_) public
    open Binary-products 𝓒 products renaming (_⊗₀_ to _∧_) public
    open Binary-coproducts 𝓒 coproducts hiding (unique₂) renaming (_⊕₀_ to _∨_) public
    open Cartesian-closed cc hiding (unique₂) public
    open Terminal terminal renaming (top to ⊤) public
    open Initial initial renaming (bot to ⊥) public

    coswap : ∀ {A B} → (A ∨ B) ⊢ (B ∨ A)
    coswap = [ in₁ , in₀ ]

    _⇒_ : ∀ A B → Ob
    _⇒_ = Exp.B^A
```

We have familiar rules such as modus ponens and negation.

```agda
    mp : ∀ {A B} → ((A ⇒ B) ∧ A) ⊢ B
    mp = ev
    
    ¬ : Ob → Ob
    ¬ A = A ⇒ ⊥
 
    _⇐_ : Ob → Ob → Ob
    A ⇐ B = B ⇒ A
```

We can also see how the exponential 'reflects' implication into the level of the
logic.

```agda
    internalize : ∀ {A B} → A ⊢ B → ⊤ ⊢ (A ⇒ B)
    internalize x = ƛ (x ∘ π₂)

    const : ∀ {A B} → B ⊢ (A ⇒ B)
    const = ƛ π₁
    
    ¬⇐ : ∀ {A B} → ¬(A ⇐ B) ⊢ (A ⇒ B)
    ¬⇐ = ƛ (¡ ∘ ev ∘ id ⊗₁ const)

    internalComp : ∀ {A B C} → ((A ⇒ B) ∧ (B ⇒ C)) ⊢ (A ⇒ C)
    internalComp {A} {B} {C} = ƛ (mp 
                                        ∘ swap 
                                        ∘ ⟨ mp ∘ π₁ , π₂ ⟩
                            ∘ ⟨ ⟨ π₁ ∘ π₁ {- A ⇒ B -} , π₂ {- A -} ⟩ , π₂ ∘ π₁ {- B ⇒ C -} ⟩
                                        )
    mt : ∀ {A B} → (A ⇒ B ∧ ¬ B) ⊢ ¬ A
    mt {A} {B} = internalComp  

    internalId : ∀ {A} → ⊤ ⊢ (A ⇒ A)
    internalId = ƛ π₂

    

    contrapositive : ∀ {A} {B} → A ⊢ B → ¬ B ⊢ ¬ A
    contrapositive p = ƛ (ev ∘ (id ⊗₁ p))

    distrib : ∀ {P Q R} → (P ∧ (Q ∨ R)) ⊢ ((P ∧ Q) ∨ (P ∧ R))
    distrib = unlambda [ ƛ (in₀ ∘ swap) , ƛ (in₁ ∘ swap) ] ∘ swap

    distrib-inv : ∀ {P Q R} → ((P ∧ Q) ∨ (P ∧ R)) ⊢ (P ∧ (Q ∨ R))
    distrib-inv = [ id ⊗₁ in₀ , id ⊗₁ in₁ ]
    
    demorgan : ∀ {A} {B} → (¬ (A ∨ B)) ⊢ ((¬ A) ∧ (¬ B))
    demorgan = ⟨ ƛ (mp ∘ id ⊗₁ in₀) , ƛ (mp ∘ id ⊗₁ in₁) ⟩

    demorganInv : ∀ {A} {B} → ((¬ A) ∧ (¬ B)) ⊢ (¬ (A ∨ B))
    demorganInv = ƛ (unlambda (unlambda -- after rearanging some things
                     [ ƛ (¡ ∘ mp ∘ swap)    -- we get to the 'meat' of the problem
                     , ƛ (ƛ (¡ ∘ mp ∘ swap) ∘ π₁) ] -- either we have an A or a B
                     ) ∘ ⟨ ⟨ π₂ , π₁ ∘ π₁ ⟩ , π₂ ∘ π₁ ⟩)
``` 

As you can can see above, even writing very trivial proofs is very tedious.
Luckily we can use a special type of Bicartesian-closed category to help us here.
If you are a functional programmer, you are in luck as you are probably already
familiar with this category... 

Before describing it though, we have to make a quick diversion into yet another
category. We know that Functors are maps between categories that preserve the
category structure (id and $-\circ-$). And that these maps form a category where
the objects are themselves categories. We can restrict this idea such that the
objects are restricted to just those categories that are Bicartesian closed, and the
functors must preserve the extra structure. We can call this category $\mathfrak{BCC}$.

So just as we looked at the structure of the category of propositional logic earlier,
we can ask if this new category has any interesting structure. (the answer is yes, lots!).
In particular we can ask for an initial object in this category, this means that we want
a particular category $\mathcal{I}$, such that for any other $\mathcal{C}\ :\ \mathfrak{BCC}$, 
there is a unique structure preserving functor $\mathcal{I} \rightarrow \mathcal{C}$.

It turns out that this category exactly corresponds to the Simply Typed Lambda Calculus, which
is like an extremely primitive functional programming language. The universal property of
intial object means that if you can give a term in the lambda calculus of type B in context A,
you get a morphism $\mathcal{C}[ A , B ]$ in any Bicartesian-closed category $\mathcal{C}$.
This effectively gives us a more convenient language to write the proofs above.

For the rest of this article, we will construct this category, show that it is initial, and
furthermore prove some interesting metatheoretic properties, such as closed canonicity and
strong normalization.


```agda
module Lambda {o} (𝓒 : Precategory o o) (bCCC : Bicartesian-closed 𝓒) 
        (B : Set o) (⟦_⟧ᵇ : ⌞ B ⌟ → 𝓒 .Precategory.Ob) where

        open Bicartesian-closed bCCC 
        
        open Cat.Functor.Hom 𝓒          
        -- In this module we show how to use the syntax of the lambda calculus to prove
        -- stuff about Bicartesian closed categories

        data Ty : Type o where
            _`×_ : Ty → Ty → Ty
            _`∪_ : Ty → Ty → Ty
            _`⇒_ : Ty → Ty → Ty
            `_   : ⌞ B ⌟ → Ty
```

We also need to show that Ty foarms a set
```agda
        Ty-is-set : is-set Ty
```
<!--
```agda

        CodeTy : Ty → Ty → Type o
        CodeTy (x `× y) (x' `× y') = CodeTy x x' × CodeTy y y'
        CodeTy (x `× y) _ = Lift _ 𝟘
        CodeTy (x `∪ y) (x' `∪ y') = CodeTy x x' × CodeTy y y'
        CodeTy (x `∪ y) _ = Lift _ 𝟘
        CodeTy (x `⇒ y) (x' `⇒ y') = CodeTy x x' × CodeTy y y'
        CodeTy (x `⇒ y) _ = Lift _ 𝟘
        CodeTy (` x) (` x') = x ≡ x'
        CodeTy (` x) _ = Lift _ 𝟘

        decodeTy : {x y : Ty} → CodeTy x y → x ≡ y
        decodeTy {x `× x₁} {y `× y₁} (P , Q) = ap₂ _`×_ (decodeTy P) (decodeTy Q)
        decodeTy {x `× x₁} {y `∪ y₁} ()
        decodeTy {x `× x₁} {y `⇒ y₁} ()
        decodeTy {x `× x₁} {` x₂} ()
        decodeTy {x `∪ x₁} {y `× y₁} ()
        decodeTy {x `∪ x₁} {y `∪ y₁} (P , Q) = ap₂ _`∪_ (decodeTy P) (decodeTy Q)
        decodeTy {x `∪ x₁} {y `⇒ y₁} ()
        decodeTy {x `∪ x₁} {` x₂} ()
        decodeTy {x `⇒ x₁} {y `× y₁} ()
        decodeTy {x `⇒ x₁} {y `∪ y₁} ()
        decodeTy {x `⇒ x₁} {y `⇒ y₁} (P , Q) = ap₂ _`⇒_ (decodeTy P) (decodeTy Q)
        decodeTy {x `⇒ x₁} {` x₂} ()
        decodeTy {` x} {` x₁} C = ap `_ C
        
        first : Ty → Ty → Ty
        first _ (x `× _) = x
        first _ (x `∪ _) = x
        first _ (x `⇒ _) = x
        first a (` _) = a

        second : Ty → Ty → Ty
        second _  (_ `× x) = x
        second _  (_ `∪ x) = x
        second _  (_ `⇒ x) = x
        second a  (` _) = a

        base : ⌞ B ⌟ → Ty → ⌞ B ⌟
        base b (_ `× _) = b
        base b (_ `∪ _) = b
        base b (_ `⇒ _) = b
        base _ (` x) = x

        Code1 : Ty → Ty → Type o
        Code1 (x `× y) (x' `× y') = Lift _ 𝟙
        Code1 (x `× y) _ = Lift _ 𝟘
        Code1 (x `∪ y) (x' `∪ y') = Lift _ 𝟙
        Code1 (x `∪ y) _ = Lift _ 𝟘
        Code1 (x `⇒ y) (x' `⇒ y') = Lift _ 𝟙
        Code1 (x `⇒ y) _ = Lift _ 𝟘
        Code1 (` x) (` x') = Lift _ 𝟙
        Code1 (` x) _ = Lift _ 𝟘

        encodeTy : {x y : Ty} → x ≡ y → CodeTy x y

        encodeTy {x `× x1} {y `× y1} P = (encodeTy {x = x} {y = y} (ap (first x) P)
                                         , encodeTy {x = x1} {y = y1} (ap (second x1) P) )
        encodeTy {a@(_ `× _)} {_ `∪ _} P = subst (Code1 a) P _ 
        encodeTy {a@(_ `× _)} {_ `⇒ _} P = subst (Code1 a) P _
        encodeTy {a@(_ `× _)} {` _} P = subst (Code1 a) P _

        encodeTy {x `∪ x1} {y `∪ y1} P = (encodeTy {x = x} {y = y} (ap (first x) P)
                                         , encodeTy {x = x1} {y = y1} (ap (second x1) P))
        encodeTy {a@(_ `∪ _)} {_ `× _} P = subst (Code1 a) P _
        encodeTy {a@(_ `∪ _)} {_ `⇒ _} P = subst (Code1 a) P _
        encodeTy {a@(_ `∪ _)} {` _} P = subst (Code1 a) P _

        encodeTy {x `⇒ x1} {y `⇒ y1} P = (encodeTy {x = x} {y = y} (ap (first x) P)
                                         , encodeTy {x = x1} {y = y1} (ap (second x1) P))
        encodeTy {a@(_ `⇒ _)} {_ `× _} P = subst (Code1 a) P _
        encodeTy {a@(_ `⇒ _)} {_ `∪ _} P = subst (Code1 a) P _
        encodeTy {a@(_ `⇒ _)} {` _} P = subst (Code1 a) P _

        encodeTy {` x} {` y} P = ap (base x) P 
        encodeTy {a@(` x)} {_ `× _} P = subst (Code1 a) P _
        encodeTy {a@(` x)} {_ `∪ _} P = subst (Code1 a) P _
        encodeTy {a@(` x)} {_ `⇒ _} P = subst (Code1 a) P _

        encodeDecode : {x y : Ty} → (P : CodeTy x y) → encodeTy (decodeTy P) ≡ P
        encodeDecode {_ `× _} {_ `× _} (P , Q) i = (encodeDecode P i) , (encodeDecode Q i)
        encodeDecode {_ `∪ _} {_ `∪ _} (P , Q) i = (encodeDecode P i) , (encodeDecode Q i)
        encodeDecode {_ `⇒ _} {_ `⇒ _} (P , Q) i = (encodeDecode P i) , (encodeDecode Q i)
        encodeDecode {` _} {` _} P = refl

        decodeEncode : {x y : Ty} → (P : x ≡ y) → decodeTy (encodeTy P) ≡ P
        decodeEncode = J (λ y p → decodeTy (encodeTy p) ≡ p) de-refl where
            de-refl : {x : Ty} → decodeTy (encodeTy (λ _ → x)) ≡ (λ _ → x)
            de-refl {x `× y} i j = de-refl {x} i j `× de-refl {y} i j
            de-refl {x `∪ y} i j = de-refl {x} i j `∪ de-refl {y} i j
            de-refl {x `⇒ y} i j = de-refl {x} i j `⇒ de-refl {y} i j
            de-refl {` _} = refl

        Path≃Code : {x y : Ty} → (x ≡ y) ≃ (CodeTy x y)
        Path≃Code = Iso→Equiv (encodeTy , (iso decodeTy encodeDecode decodeEncode))

        Ty-is-set x y = is-hlevel≃ 1 Path≃Code CodeProp where 
          CodeProp : {x y : Ty} → is-prop (CodeTy x y)
          CodeProp {_ `× _} {_ `× _} (P1 , P2) (Q1 , Q2)  = ap₂ _,_ (CodeProp P1 Q1) (CodeProp P2 Q2)
          CodeProp {_ `∪ _} {_ `∪ _} (P1 , P2) (Q1 , Q2)  = ap₂ _,_ (CodeProp P1 Q1) (CodeProp P2 Q2)
          CodeProp {_ `⇒ _} {_ `⇒ _} (P1 , P2) (Q1 , Q2) = ap₂ _,_ (CodeProp P1 Q1) (CodeProp P2 Q2)
          CodeProp {` _} {` _} P Q = B .is-tr _ _ P Q
```
--->


```agda
        data Cx : Type o where
            ∅   : Cx
            _,_ : Cx → Ty → Cx
```

<!--
```agda

        Cx≃List : Cx ≃ List Ty
        Cx≃List = Iso→Equiv (toL , iso fromL tofrom fromto) where
            toL : Cx → List Ty
            toL ∅ = []
            toL (Γ , A) = A ∷ toL Γ
            fromL : _
            fromL [] = ∅
            fromL (A ∷ Γ) = fromL Γ , A
            tofrom : _
            tofrom [] = refl
            tofrom (A ∷ Γ) = ap₂ _∷_ refl (tofrom Γ)
            fromto : _
            fromto ∅ = refl
            fromto (Γ , A) i = fromto Γ i , A
            
        Cx-is-set : is-set Cx
        Cx-is-set = is-hlevel≃ 2 Cx≃List (ListPath.is-set→List-is-set Ty-is-set)
```
--->

```agda
        private variable
            Γ Δ Θ : Cx
            τ σ ρ  : Ty

        data Var : Cx → Ty → Type o where
            stop : Var (Γ , τ) τ
            pop  : Var Γ τ → Var (Γ , σ) τ

        ⟦_⟧ᵗ : Ty → Ob
        ⟦_⟧ᶜ : Cx → Ob
        data Tm : Cx → Ty → Type o

        data Tm where
            `var    : Var Γ τ                          → Tm Γ τ
            `π₁     : Tm Γ (τ `× σ)                  → Tm Γ τ
            `π₂     : Tm Γ (τ `× σ)                  → Tm Γ σ
            `⟨_,_⟩  : Tm Γ τ        → Tm Γ σ       → Tm Γ (τ `× σ)
            `in₀    : Tm Γ τ                         → Tm Γ (τ `∪ σ)
            `in₁    : Tm Γ σ                         → Tm Γ (τ `∪ σ)
            `[_,_]  : Tm (Γ , τ) ρ  → Tm (Γ , σ) ρ → Tm (Γ , (τ `∪ σ)) ρ
            `λ      : Tm (Γ , τ) σ                   → Tm Γ (τ `⇒ σ)
            _`$_    : Tm Γ (τ `⇒ σ) → Tm Γ τ       → Tm Γ σ
            `_      : ∀ {o} → ⟦ Γ ⟧ᶜ ⊢ ⟦ o ⟧ᵇ           → Tm Γ (` o)
            

        ⟦ x `× y ⟧ᵗ = ⟦ x ⟧ᵗ ∧ ⟦ y ⟧ᵗ
        ⟦ x `∪ y ⟧ᵗ = ⟦ x ⟧ᵗ ∨ ⟦ y ⟧ᵗ
        ⟦ x `⇒ y ⟧ᵗ = ⟦ x ⟧ᵗ ⇒ ⟦ y ⟧ᵗ
        ⟦ ` x ⟧ᵗ = ⟦ x ⟧ᵇ
        
        ⟦ ∅ ⟧ᶜ = ⊤
        ⟦ Γ , t ⟧ᶜ = ⟦ Γ ⟧ᶜ ∧ ⟦ t ⟧ᵗ

        
        ⟦_⟧ⁿ : Var Γ τ → ⟦ Γ ⟧ᶜ ⊢ ⟦ τ ⟧ᵗ
        ⟦ stop ⟧ⁿ = π₂
        ⟦ pop v ⟧ⁿ = ⟦ v ⟧ⁿ ∘ π₁

        ⟦_⟧ᵉ : Tm Γ τ → ⟦ Γ ⟧ᶜ ⊢ ⟦ τ ⟧ᵗ
        ⟦ `var v ⟧ᵉ = ⟦ v ⟧ⁿ
        ⟦ `π₁ e ⟧ᵉ = π₁ ∘ ⟦ e ⟧ᵉ
        ⟦ `π₂ e ⟧ᵉ = π₂ ∘ ⟦ e ⟧ᵉ
        ⟦ `⟨ f , g ⟩ ⟧ᵉ = ⟨ ⟦ f ⟧ᵉ , ⟦ g ⟧ᵉ ⟩
        ⟦ `in₀ e ⟧ᵉ = in₀ ∘ ⟦ e ⟧ᵉ
        ⟦ `in₁ e ⟧ᵉ = in₁ ∘ ⟦ e ⟧ᵉ
        ⟦ `[ f , g ] ⟧ᵉ = [ ⟦ f ⟧ᵉ , ⟦ g ⟧ᵉ ] ∘ distrib
        ⟦ `λ e ⟧ᵉ = ƛ ⟦ e ⟧ᵉ
        ⟦ f `$ e ⟧ᵉ = ev ∘ ⟨ ⟦ f ⟧ᵉ , ⟦ e ⟧ᵉ ⟩
        ⟦ ` f ⟧ᵉ = f

        

        interpret : ∀ P Q → Tm (∅ , P) Q → ⟦ P ⟧ᵗ ⊢ ⟦ Q ⟧ᵗ
        interpret P Q e = ⟦ e ⟧ᵉ ∘ ⟨ ! , id ⟩


        data Wk : Cx → Cx → Type o where
            stop : Wk Γ Γ
            drop : Wk Γ Δ → Wk (Γ , τ) Δ
            keep : Wk Γ Δ → Wk (Γ , τ) (Δ , τ)

        _∘w_ : Wk Δ Θ → Wk Γ Δ → Wk Γ Θ 
        ρ ∘w stop = ρ
        ρ ∘w drop σ = drop (ρ ∘w σ)
        stop ∘w keep σ = keep σ
        drop ρ ∘w keep σ = drop (ρ ∘w σ)
        keep ρ ∘w keep σ = keep (ρ ∘w σ)

        widl : (f : Wk Γ Δ) → stop ∘w f ≡ f
        widl stop = refl
        widl (drop f) = ap drop (widl f)
        widl (keep f) = refl

        wassoc : ∀ {Γ Δ Θ Ψ} (f : Wk Θ Ψ) (g : Wk Δ Θ) (h : Wk Γ Δ)
                → f ∘w (g ∘w h) ≡ (f ∘w g) ∘w h
        wassoc f g stop = refl
        wassoc f g (drop h) = ap drop (wassoc f g h)
        wassoc f stop (keep h) = refl
        wassoc f (drop g) (keep h) = ap drop (wassoc f g h)
        wassoc stop (keep g) (keep h) = refl
        wassoc (drop f) (keep g) (keep h) = ap drop (wassoc f g h)
        wassoc (keep f) (keep g) (keep h) = ap keep (wassoc f g h)

```
We can now form show that Cx with Weakenings form a Precategory $(\cW)$
```agda

        𝓦 : Precategory o o
        𝓦 .Precategory.Ob = Cx
        𝓦 .Precategory.Hom = Wk
        𝓦 .Precategory.Hom-set = {!   !}
        𝓦 .Precategory.id = stop
        𝓦 .Precategory._∘_ = _∘w_
        𝓦 .Precategory.idr _ = refl
        𝓦 .Precategory.idl = widl
        𝓦 .Precategory.assoc = wassoc
```
We will also show that there is an embedding of Weakenings into Homs
in the semantic category, and together with ⟦-⟧ᶜ, this forms a functor
$E$ that embeds 𝓦 back into the semantic category.
```agda
        ⟦_⟧ʷ : Wk Γ Δ → ⟦ Γ ⟧ᶜ ⊢ ⟦ Δ ⟧ᶜ
        ⟦ stop ⟧ʷ = id
        ⟦ drop f ⟧ʷ = ⟦ f ⟧ʷ ∘ π₁
        ⟦ keep f ⟧ʷ = ⟦ f ⟧ʷ ⊗₁ id

        ⟦-⟧ʷ∘ : (f : Wk Δ Θ) (g : Wk Γ Δ) → ⟦ f ⟧ʷ ∘ ⟦ g ⟧ʷ ≡ ⟦ f ∘w g ⟧ʷ
        ⟦-⟧ʷ∘ f stop = idr _
        ⟦-⟧ʷ∘ f (drop g) = assoc _ _ π₁ ∙ (⟦-⟧ʷ∘ f g ⟩∘⟨refl)
        ⟦-⟧ʷ∘ stop (keep g) = idl _
        ⟦-⟧ʷ∘ (drop f) (keep g) = sym (assoc _ _ _) ∙ (refl⟩∘⟨ π₁∘⟨⟩)
                               ∙ assoc _ _ _       ∙ (⟦-⟧ʷ∘ f g ⟩∘⟨refl)
        ⟦-⟧ʷ∘ (keep f) (keep g) = sym (×-functor .F-∘ _ _)
                                   ∙ ap₂ _⊗₁_ (⟦-⟧ʷ∘ f g) (idl id)

        E : Functor 𝓦 𝓒
        E .F₀ = ⟦_⟧ᶜ
        E .F₁ = ⟦_⟧ʷ
        E .F-id = refl
        E .F-∘ f g = sym (⟦-⟧ʷ∘ f g)

        data Nf : Cx → Ty → Type o
        data Ne : Cx → Ty → Type o

        data Nf where
          `ne : Ne Γ τ → Nf Γ τ
          `lam : Nf (Γ , τ) σ → Nf Γ (τ `⇒ σ)
          `pair : Nf Γ τ → Nf Γ σ → Nf Γ (τ `× σ) 

        data Ne where 
          `app : Ne Γ (τ `⇒ σ) → Nf Γ τ → Ne Γ σ
          `var : Var Γ τ → Ne Γ τ
          `fst : Ne Γ (τ `× σ) → Ne Γ τ
          `snd : Ne Γ (τ `× σ) → Ne Γ σ
          `const : {o : ⌞ B ⌟} → ⟦ Γ ⟧ᶜ ⊢ ⟦ o ⟧ᵇ → Ne Γ (` o) 

        _[_]wV  : Var Δ τ → Wk Γ Δ → Var Γ τ
        v [ stop ]wV = v
        v [ drop ρ ]wV = pop (v [ ρ ]wV)
        stop [ keep ρ ]wV = stop
        pop v [ keep ρ ]wV = pop (v [ ρ ]wV)
        
        _[_]wNe : Ne Δ τ → Wk Γ Δ → Ne Γ τ
        _[_]wNf : Nf Δ τ → Wk Γ Δ → Nf Γ τ
        `app f x [ ρ ]wNe = `app (f [ ρ ]wNe) (x [ ρ ]wNf)
        `var x [ ρ ]wNe = `var (x [ ρ ]wV)
        `fst x [ ρ ]wNe = `fst (x [ ρ ]wNe)
        `snd x [ ρ ]wNe = `snd (x [ ρ ]wNe)
        `const f [ ρ ]wNe = `const (f ∘ ⟦ ρ ⟧ʷ)
        `ne x [ ρ ]wNf = `ne (x [ ρ ]wNe)
        `lam x [ ρ ]wNf = `lam (x [ keep ρ ]wNf)
        `pair x x₁ [ ρ ]wNf = `pair (x [ ρ ]wNf) (x₁ [ ρ ]wNf)

        _[Id]wNe : (t : Ne Γ τ) → t [ stop ]wNe ≡ t
        _[Id]wNf : (t : Nf Γ τ) → t [ stop ]wNf ≡ t
        `app t x [Id]wNe = ap₂ `app (t [Id]wNe) (x [Id]wNf)
        `var x [Id]wNe = refl
        `fst t [Id]wNe = ap `fst (t [Id]wNe)
        `snd t [Id]wNe = ap `snd (t [Id]wNe)
        `const x [Id]wNe = ap `const (idr x)
        `ne x [Id]wNf = ap `ne (x [Id]wNe)
        `lam x [Id]wNf = {!   !}
        `pair x x₁ [Id]wNf = ap₂ `pair (x [Id]wNf) (x₁ [Id]wNf)


        []wNe∘ : ∀ (f : Wk Δ Θ) (g : Wk Γ Δ) (t : Ne Θ τ) → t [ f ∘w g ]wNe ≡ (t [ f ]wNe) [ g ]wNe
        []wNf∘ : ∀ (f : Wk Δ Θ) (g : Wk Γ Δ) (t : Nf Θ τ) → t [ f ∘w g ]wNf ≡ (t [ f ]wNf) [ g ]wNf
        []wNe∘ f g (`app t x) = ap₂ `app ([]wNe∘ f g t) ([]wNf∘ f g x)
        []wNe∘ f g (`var x) = {!   !}
        []wNe∘ f g (`fst t) = ap `fst ([]wNe∘ f g t)
        []wNe∘ f g (`snd t) = ap `snd ([]wNe∘ f g t)
        []wNe∘ f g (`const x) = ap `const ((refl⟩∘⟨ E .F-∘ f g) ∙ assoc x _ _)
        []wNf∘ f g (`ne x) = ap `ne ([]wNe∘ f g x)
        []wNf∘ f g (`lam t) = {!   !}
        []wNf∘ f g (`pair t t₁) = ap₂ `pair ([]wNf∘ f g t) ([]wNf∘ f g t₁)

        module PsW = Precategory (PSh o 𝓦)

        NE : (τ : Ty) → PsW.Ob
        NE τ .F₀ Γ = el (Ne Γ τ) {!   !}
        NE τ .F₁ ρ = _[ ρ ]wNe
        NE τ .F-id = ext _[Id]wNe
        NE τ .F-∘ f g = ext ([]wNe∘ g f)
    
        NF : (τ : Ty) → PsW.Ob
        NF τ .F₀ Γ = el (Nf Γ τ) {!   !}
        NF τ .F₁ ρ = _[ ρ ]wNf
        NF τ .F-id = ext _[Id]wNf
        NF τ .F-∘ f g = ext ([]wNf∘ g f)

        YW : (τ : Ty) → PsW.Ob
        YW τ = {!   !}

        ιnf : ∀ (τ : Ty) → PsW.Hom (NF τ) (YW τ)
        ιne : ∀ (τ : Ty) → PsW.Hom (NE τ) (YW τ)
        ιnf τ = {!   !}
        ιne τ = {!   !}

        record TwGl-Ob (τ : Ty) : Type (lsuc o) where 
          field ⦅-⦆ : PsW.Ob
          field u   : PsW.Hom (NE τ) ⦅-⦆
          field q   : PsW.Hom ⦅-⦆ (NF τ)

          field comm : (ιnf τ) PsW.∘ q PsW.∘ u ≡ (ιne τ)
       

        TwGl-Ctx : (Γ : Cx) → Type (lsuc o)
        TwGl-Ctx ∅ = Lift _ 𝟘
        TwGl-Ctx (Γ , x) = TwGl-Ctx Γ × TwGl-Ob x

        liftToCtx : (Ty → PsW.Ob) → Cx → PsW.Ob
        liftToCtx A ∅ = bot where open Initial (PSh-initial {κ = o} {C = 𝓦})
        liftToCtx A (Γ , τ) = liftToCtx A Γ ⊗₀ A τ where
         open Binary-products (PSh o 𝓦) (PSh-products {κ = o} {C = 𝓦})

        YWᶜ = liftToCtx YW
        NFᶜ = liftToCtx NF

        YWterm : {Γ : Cx} → {τ : Ty} → Tm Γ τ → PsW.Hom (YWᶜ Γ) (YW τ)
        YWterm {Γ} {τ} x ._=>_.η = {!   !}
        YWterm x ._=>_.is-natural = {!   !}
        
        liftToCtxtw : (A : {τ : Ty} → TwGl-Ob τ → PsW.Ob) → (∀ {Γ : Cx} → TwGl-Ctx Γ → PsW.Ob)
        liftToCtxtw A {∅} ()
        liftToCtxtw A {xs , x} (txs , tx) = liftToCtxtw A txs ⊗₀ A tx where
          open Binary-products (PSh o 𝓦) (PSh-products {κ = o} {C = 𝓦})

        
        ⦅_⦆ᶜ = liftToCtxtw TwGl-Ob.⦅-⦆

        qᶜ : ∀ {g} (Γ : TwGl-Ctx g) → PsW.Hom ⦅ Γ ⦆ᶜ (NFᶜ g)
        qᶜ Γ ._=>_.η Δ = {!   !}
        qᶜ Γ ._=>_.is-natural = {!   !}

        ιnfᶜ : ∀ Γ → PsW.Hom (NFᶜ Γ) (YWᶜ Γ)
        ιnfᶜ = {!   !}

        TmF : Functor 𝓒 (PSh o 𝓦)
        TmF = Nerve E
 
        ArtGl : Displayed 𝓒 (lsuc o) o
        ArtGl = Change-of-base TmF (Slices (PSh o 𝓦))

        ArtGl-Fibration : Cartesian-fibration ArtGl
        ArtGl-Fibration = Change-of-base-fibration _ _
                           (Codomain-fibration _ (PSh-pullbacks {κ = o} {C = 𝓦}))

        module 𝒢 = Displayed ArtGl 

        R : Ty → PsW.Ob
        R = ps where
          open Binary-products (PSh o 𝓦) (PSh-products {κ = o} {C = 𝓦})
          open Pullbacks (PSh o 𝓦) (PSh-pullbacks {κ = o} {C = 𝓦})
          module PsC = Cartesian-closed (PSh-closed {κ = o} {C = 𝓦})

           
          ps : Ty → PsW.Ob
          ps (A `× B) = ps A ⊗₀ ps B
          ps (A `∪ B) = {!  !}
          ps (A `⇒ B) = Pb {x = TmF .F₀ ⟦ A `⇒ B ⟧ᵗ} {y = PsC.Exp.B^A (ps A) (ps B)}
           ν {!   !} where
                ν : PsW.Hom (TmF .F₀ (⟦ A ⟧ᵗ ⇒ ⟦ B ⟧ᵗ)) (PsC.Exp.B^A (ps A) (TmF .F₀ ⟦ B ⟧ᵗ))
                ν = {!   !}
          ps (` x) = NF (` x)

        ⟦_⟧ᵍ : (τ : Ty) → 𝒢.Ob[ ⟦ τ ⟧ᵗ ]
        ⟦ τ ⟧ᵍ ./-Obj.domain = R τ
        ⟦ τ ⟧ᵍ ./-Obj.map = {!   !}


        -- ArtGl = GblSec ↓ CdmFib

        -- module 𝒢 = Cat.Reasoning ArtGl

        -- gl : Functor ArtGl 𝓒
        -- gl = Dom _ _

        -- -- Show 𝒢 is bicartesian closed
        -- 𝒢-Term : Terminal ArtGl
        -- 𝒢-Term = record { top = t ; has⊤ = tun }
        --   where
        --     t : 𝒢.Ob
        --     t .↓Obj.x = ⊤
        --     t .↓Obj.y = (el! (Lift _ 𝟙)) , cut {domain = el! (Lift _ 𝟙)} (λ _ → _)
        --     t .↓Obj.map _ = _

        --     tun : is-terminal ArtGl t
        --     tun x = contr (↓hom {α = !}
        --                          {β = total-hom (λ _ → _)
        --                           (slice-hom (λ _ → _) refl)} refl)
        --                  λ x →  ↓Hom-path GblSec CdmFib
        --                          (!-unique (x .↓Hom.α))
        --                           (total-hom-path (Slices (Sets ℓ)) refl refl)



        record TwGl-Hom {Γ : Cx} (Γtw : TwGl-Ctx Γ)
                {τ : Ty} (Δ : TwGl-Ob τ) : Type (lsuc o) where
          
          module Δ = TwGl-Ob Δ
          field ⦅α⦆ : PsW.Hom ⦅ Γtw ⦆ᶜ Δ.⦅-⦆
          field α   : Tm Γ τ

          field comm : (ιnf τ) PsW.∘ Δ.q PsW.∘ ⦅α⦆ ≡ YWterm α PsW.∘ (ιnfᶜ Γ) PsW.∘ (qᶜ Γtw)
    

          
```       