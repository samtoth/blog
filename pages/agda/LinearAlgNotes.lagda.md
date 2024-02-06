<!---
```agda
open import Cat.Prelude hiding (_+_;_*_)
open import Cat.Diagram.Everything
open import Cat.Diagram.Product.Finite
open import Cat.Instances.Comma
open import Cat.Instances.Slice
open import Cat.Instances.Delooping
open import Cat.Functor.Adjoint
open import Cat.Displayed.Univalence.Thin
open import Cat.Functor.FullSubcategory
open import Algebra.Ring
open import Algebra.Group.NAry
open import Algebra.Group.Ab
open import Data.Nat renaming (Nat to ℕ; _+_ to _+N_; _*_ to _*ℕ_)
   hiding (*-associative; +-associative)
open import Data.Fin
import Algebra.Ring.Module.Vec as VecM
open import Algebra.Group
open import Algebra.Ring.Module
open import Algebra.Ring.Commutative
open import Algebra.Ring.Solver
open import Algebra.Ring.Module.Category
import Algebra.Ring.Module.Free
open import Cat.Abelian.Base
import Cat.Abelian.Images
open import 1Lab.Function.Embedding
```
--->
# Maths for Computer Scientists 2: Linear Algebra

These are my lecture notes for the first year maths 2 module at Nottingham Uni.
Alongside the notes is a cubical agda implementation of some of the maths.
Enjoy! :)

```agda
module LinearAlgNotes {ℓ} (R : Ring ℓ) where

open Ring-on (R .snd) hiding (_↪_)
open VecM R

R-number : Number ⌞ R ⌟
R-number .Number.Constraint = λ x → Lift _ ⊤
R-number .Number.fromNat n = go n  where
   go : ℕ → ⌞ R ⌟
   go zero = 0r
   go (suc n) = 1r + go n
  
private instance
  Rnum : Number ⌞ R ⌟
  Rnum = R-number

R-negative : Negative ⌞ R ⌟
R-negative .Negative.Constraint = λ _ → Lift _ ⊤
R-negative .Negative.fromNeg n = go n where
  go : ℕ → _
  go n = - fromNat n

private instance
  Rneg : Negative ⌞ R ⌟
  Rneg = R-negative


```

Although in the lectures most of the examples are given in terms of $\mathbb{R}$,
due to it being complicated to work with, and with the goal of generality in mind,
I have parameterized this document over an arbritary ring, denoted by $R$. As and
when we need to upgrade R to a field or division ring etc. we can add that requirment
as a module argument.


TODO: Section on motivation. What's it all about???

## Vectors

> [! def: Vector]
> Given an $n : \mathbb{N}$, $R^{n}$ denotes an $n$ dimensional $R$-vector.
> $R^n$ is just the $n$-ary product of $R$'s.

In type theory we can define n length vectors as a function from the finite set
of size $n$ to the underlying set of $R$.

```agda
Vector : ℕ → Type ℓ
Vector n = Fin n → ⌞ R ⌟
```

We will give some examples of vectors here:
<!--
```agda
private module _ where
```
-->

To give some arbritary 3d vector $\begin{pmatrix}0\\8\\-5\end{pmatrix}$ we
write the following:

```agda
  some3dVec : Vector 3
  some3dVec fzero = 0
  some3dVec (fsuc fzero) = 8
  some3dVec (fsuc (fsuc fzero)) = -5
```

An interesting example to consider is the 0-dimensional vector.
Because the 0-sized finite set is equivalent to the empty type, 
`Vector 0` is equivalent to a function $\bot \to R$. Functions from
the empty type always exist and are unique so the above function type
is equivalent to a singleton. In the language of Homotopy Type Theory
this is called being a Contractible Type.

```agda
  0Vec : Vector 0
  0Vec ()
```

Here we prove that any other inhabitant of `Vector 0` is equal to
`0vec` above and therefore that Vector 0 is a Contractible type.
The proof goes through trivially via function extensionality.


```agda
  Vector0-is-contr : is-contr (Vector 0)
  Vector0-is-contr .centre = 0Vec
  Vector0-is-contr .paths x = ext (λ where ())
```


### Operations on Vectors

We can define some simple operations on our vectors. We can add together
two vectors in a component wise fashion just so long as they have the
same dimension. We can also multiply a $R$-vector by an element of R itself
known as scalar multiplication.

Using this functional style definition of vectors makes defining these
operations as they all act component wise.

```agda
_+v_ : ∀ {n} → Vector n → Vector n → Vector n
v +v w = λ i → v i + w i
```
The above definition simply says that the value of the vector at index $i$ is
the value of $v$ at index $i$ plus $w$ at $i$.

```agda
_s⋆v_ : ∀ {n} → ⌞ R ⌟ → Vector n → Vector n
x s⋆v v = λ i → x * v i
```

Geometrically, these two operations are well motivated by the picture of 
stacking two arrows end on end and scalling an arrow respectively.

Later on, we will look at what properties these operations have so that
we can ask whether there are other objects that behave a little like vectors.


Given these first two operations we can define other bits of arithmetic;
For example, subtraction can be written as $v + (-1)w$.

```agda
_-v_ : ∀ {n} → Vector n → Vector n → Vector n
v -v w = v +v (-1 s⋆v v)
```

#### Properties of these operations

Firstly, note that all of the properties of addition in $R$ will hold for addition
of vectors, this can be seen by noting that both addition and equality can be given
component wise. This means that $(\mathrm{Vec}_n, -+-)$ form an abelian group.
Secondly notice the following laws concerning scalar multiplication hold:

 - $1v=v$
 - $(rs)⋅v=r⋅(s⋅v)$
 - $(r+s)v=rv+sv$
 - $r(v+w)=rv+rw$


### Spans and Linear combinations

In a more general sense we can define the linear combinations of a (finite?) 
set of vectors: Given $v_1,...v_i \in R^n$, and $c_1,...,c_i \in R$, the linear
combination of $v$ by $c$ is $c_1v_1 + ... + c_iv_i$.



```agda
module LinearComb (n i : ℕ) (v : Fin i → Vector n) where
```
Fixing $v$ as an $i$ sized finite set of $n$-dimensional vectors, we can define
a function that takes a list of $i$ scalars, or equivalently an $i$-dimensional
vector, and returns the linear combination of it with the set $v$ of vectors.

```agda
  linear-combination : Vector i → Vector n
  linear-combination c = 
    linear-extension (Fin-vec-module _) v .Linear-map.map c
``` 

Happily, this function has already been defined for us in the 1lab under the name
`linear-extension`. In fact, `linear-extension` is not just a function but a linear
map - the type of Morphisms in the category of Modules ($\mathrm{RMod}$).

The span of $v$ is the set of all vectors that can be constructed from linear
combinations of $v$ with some $c$'s. First we use the naive type theoretic encoding of
this data:

```agda
  Span : Type ℓ
  Span = Σ (Vector n) (fibre linear-combination)

  Span-is-set : is-set Span
  Span-is-set = hlevel!
```
We can prove that spans are closed under $-+-$ and $-⋆-$ due to the fact that 
linear-combination is not just a function, but a linear map.

```agda
  Span-closed-+ : Span → Span → Span
  Span-closed-+ (x , a , p) (y , b , q)
   = (x +v y , a +v b , 
      linear-extension (Fin-vec-module _) v .Linear-map.pres-+ a b 
      ∙ ap₂ _+v_ p q)

  Span-closed-⋆ : ⌞ R ⌟ → Span → Span
  Span-closed-⋆ x (y , a , p) 
    = (x s⋆v y , x s⋆v a ,
       Linear-map.pres-⋆ (linear-extension (Fin-vec-module _) v) x a 
       ∙ ap (x s⋆v_) p)
```

I have stopped short of showing that Span with these $+$ and $⋆$ gives rise to a module, because
there is another construction of Span that will make these things go through by definition. When
the linear combination is considered as a morphism $f : Vec_i \to Vec_n$ in $\mathrm{RMod}$,
we take $span\ v$ to be the image of $f$. (We have images in $RMod$ because it is an
[ab category](./RMod-Ab).

```agda
  postulate
    R-Mod-is-ab : is-abelian (R-Mod R ℓ) -- Working on it!!! :(

  module RAb = Cat.Abelian.Images {C = R-Mod R ℓ} R-Mod-is-ab
  module RSpan = Image (R-Mod R ℓ) 
      (RAb.images (linear-map→hom $ linear-extension (Fin-vec-module _) v))

  RSpan : R-Mod.Ob
  RSpan = RSpan.Im
```
Using the categorical notion of RSpan we can easily show that RSpan is a submodule of
$Vec_n$.

```agda
  RSpan-submodule : RSpan R-Mod.↪ Fin-vec-module n
  RSpan-submodule = record { mor = RSpan.Im→codomain ; monic = RSpan.Im→codomain-is-M }

```

Linear combinations can be used to represent systems of linear equations. For example,
if you have a system of equations:
$$
\begin{cases}
x - y = 8 \\
2x + 2y = 16 \\
6x - y = 3
\end{cases}
$$
you can represent them as the following linear combination:
$$
x\begin{pmatrix}1\\2\\6\end{pmatrix} +
y\begin{pmatrix}-1\\-2\\-1\end{pmatrix} =
\begin{pmatrix}8\\16\\3\end{pmatrix}
$$



```agda
LinearEquation : ∀ i n → Type ℓ
LinearEquation i n = (Fin i → Vector n) × Vector n

Solution : ∀ {i n} → LinearEquation i n → Type ℓ
Solution {i} {n} (v , b) = fibre linear-combination b
 where open LinearComb n i v
```
You might notice that the type `Solution` is just a repackaging of the data of span.
A linear equation is called consistent iff it's span is inhabited and otherwise it's
called inconsistent.

In HoTT this translates to the type of solutions being *merely* inhabited.

```agda
is-consistent : ∀ {i n} → LinearEquation i n → Type ℓ
is-consistent x = ∥ Solution x ∥

is-consistent-is-prop : ∀ {i n} → (eq : LinearEquation i n) → is-prop (is-consistent eq)
is-consistent-is-prop eq = hlevel!
```

See [[Examples]] to see how this works through for some arbritary linear equation.

## Bases
```agda
open Binary-products (R-Mod R ℓ) (is-additive.has-prods (R-Mod-is-additive R))
-- open is-additive (R-Mod-is-additive R {ℓ})
```

A module over R is said to have a basis if it is freely generated by a 
linearly-independant finite subset of R. A classic example is the standard basis
for some $R^n$. Take $n = 3$:
$$
R^3 = Span \{\left(\begin{smallmatrix}1\\0\\0\end{smallmatrix}\right),\
            \left(\begin{smallmatrix}0\\1\\0\end{smallmatrix}\right),\
            \left(\begin{smallmatrix}0\\0\\1\end{smallmatrix}\right)
\} 
$$

An alternative characterisation of this fact is that a basis is a linear isomorphism
between a module $M$ and a direct sum of copies of $R$ regarded as a module - 
$M \xrightarrow{\sim} \oplus_{i\in I}\ R$. You might notice that when $I$ is a finite
set, $\oplus_{i \in I}R$ is actually just equivalent to our type $Vec_n$.

First the general case. We need to show that R-Mod has indexed products:

```agda
-- Direct-sum : ∀ {ℓ'} → has-indexed-products (R-Mod R ℓ) ℓ'
-- Direct-sum F .Indexed-product.ΠF = {!   !}
-- Direct-sum F .Indexed-product.π = {!   !}
-- Direct-sum F .Indexed-product.has-is-ip = {!   !}
```

```agda
module _ (M : Module R ℓ) where

  has-dimension : ℕ → Type ℓ
  has-dimension dim = M R-Mod.≅ Fin-vec-module dim

  Finite-Basis : Type ℓ
  Finite-Basis = Σ[ dim ∈ ℕ ] has-dimension dim
```


Due to univalence, this says that the only finite-dimensional modules are the vectors.
This definition seems unmotivated, but, we can show that it is in fact equivalent to
the more standard definition that basis for a module is a linearly-independant
spanning set.

### Linear independance

A set of vectors is said to be linearly dependant if you can write one as a linear
combination of the others - and linearly independant otherwise. In terms of bases
you can think of this like a redundancy in the coordinate system.

The standard definition states that for a set of vectors to be linearly independant
a linear combination $\sum_i^n{a_iv_i} = 0\ \textit{iff}\ \ \forall i.\ a_i = 0$.

Note that due to this definition relying on linear combinations, it only applies to
finite sets. There is another very elegant definition which makes use of the free
functor from $Sets \to RMods$.

#### Free functor

The free functor is a left adjoint to the forgetfull functor into $Sets$. It is
constructed here in cubical agda using a Higher Inductive Type (or specifically a
Quotient Inductive Type). On finite sets of vectors it is equivalent to the Span of
the vectors.

```agda
module _ where
  open Algebra.Ring.Module.Free R

  _ : Functor (Sets ℓ) (R-Mod R ℓ)
  _ = Free-module {ℓ}

  _ : Free-module {ℓ} ⊣ Forget-module R ℓ
  _ = Algebra.Ring.Module.Free.Free⊣Forget R
```

```agda
  module FreeM = Functor (Free-module {ℓ})
  module _ {n} {i} (v : Fin i → Vector n) where
  -- S : Type ℓ
  -- S = image v

  -- FiniteFree≅Span : LinearComb.RSpan n i v R-Mod.≅ FreeM.₀ (el! (image v))
  -- FiniteFree≅Span = ?
```

#### Linear independace - freely!

So now given module $M$ over $R$, and a subset $S \subseteq |M|$. Consider the action of 
the free functor $F$ on the subset inclusion $i_s : S \hookrightarrow |M|$. Which gives
us a not-necisarrily mono module homomorphism $F\ i : R S \to M$. The subset $S$ is 
linearly independant just when $F\ i$ is monic. 

```agda
linearly-independant : (M : Module R ℓ) → (S : Σ[ S ∈ Set ℓ ] (⌞ S ⌟ ↪ ⌞ M ⌟)) → Type (lsuc ℓ)
linearly-independant (M , _) (S , (i , _)) = R-Mod.is-monic (FreeM.₁ {S} {M} i)
``` 

```agda
record is-basis (M : Module R ℓ) (S : Set ℓ) (i : ⌞ S ⌟ ↪ ⌞ M ⌟) : Type (lsuc ℓ) where
  field lid      : linearly-independant M (S , i)
  field spanning : FreeM.₀ S R-Mod.≅ M


record Basis (M : Module R ℓ) : Type (lsuc ℓ) where
  field 
    {S} : Set ℓ
    i : ⌞ S ⌟ ↪ ⌞ M ⌟
    has-is-basis : is-basis M S i

  open is-basis has-is-basis public

  is-finite : Type ℓ
  is-finite = Finite ⌞ S ⌟
```

```agda
module _ (M : Module R ℓ) where

  -- Fin-Basis→Basis : Finite-Basis M → Basis M
  -- Fin-Basis→Basis (dim , p) = b where
  --   open Basis
  --   b : Basis M
  --   b .S = {!   !}
  --   b .i = {!   !}
  --   b .has-is-basis = {!   !} 

  -- Basis-is-finite→Fin-Basis : (B : Basis M) → Basis.is-finite B → Finite-Basis M
  -- Basis-is-finite→Fin-Basis b = {!   !}

```



## Ab-presheaf interpretation

### Oidification of rings

Another word for Ab-category is a ringoid (usually reserved for when the category
is small). This means that it is the horizontal categorification of a ring.
You might be familiar with the (slightly tounge in cheek) name for (small) categories:
Monoidoid - and there are many paralels we can draw here. Firstly, recall that a one
object category is a monoid; in parralel a one object Ab-category is a ring.

These are already constructs in the one lab:

```agda
_ : Precategory lzero ℓ
_ = B (record {  _⋆_ = _*_ ; has-is-monoid = *-monoid }) -- B stands for delooping...
                                                         -- for some reason....

_ : Ab-category _
_ = Ringoid

```
 
For $A$ and $B$ Ab-categories, the Ab-enriched-functor category $[A, B]$ is also
an Ab-category. The Ab-analogue of presheafs is the category $[R^{op}, Ab]$, where
R is some Ab-category and $Ab$, the Ab-category of abelian groups, takes the place
of $Set$. This category is an 
[Ableian Category](https://ncatlab.org/nlab/show/additive+and+abelian+categories).
There are analogues between Abelian Category and Topoi that were explored by
Freyd in his presentation of [AT-categories](https://ncatlab.org/nlab/show/AT+category)

It turns out that when fixing R to be some ring, the category $RMod$ is
actually equivalent to the ab-functor ab-category $[R^{op},Ab]$. And we will 
now show a proof of this.