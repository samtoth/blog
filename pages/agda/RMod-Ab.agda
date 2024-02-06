open import Cat.Prelude hiding (_+_; _*_)
open import Algebra.Ring
open import Algebra.Ring.Commutative
open import Cat.Abelian.Base
open import Algebra.Group.Ab
open import Algebra.Group
open import Algebra.Monoid
open import Algebra.Semigroup
open import Algebra.Ring.Module
open import Algebra.Ring.Module.Category
open import Cat.Diagram.Everything
open import Cat.Displayed.Total
open import 1Lab.HIT.Truncation

module RMod-Ab {ℓ} (R : Ring ℓ) (cring : is-commutative-ring R) where

-- open is-additive (R-Mod-is-additive R {ℓ}) renaming (_+_ to _+ab_)
open Precategory (R-Mod R ℓ)

R-Mod-is-pre-abelian : is-pre-abelian (R-Mod R ℓ)
R-Mod-is-pre-abelian .is-pre-abelian.has-additive = R-Mod-is-additive R
R-Mod-is-pre-abelian .is-pre-abelian.kernel {A = A} {B} f@(total-hom map linear) = ker 
  where
    module A = Module-on (A .snd)
    module B = Module-on (B .snd)
    module Linear =  is-linear-map linear 

    add : image map → image map → image map 
    add (x , xim) (y , yim) = (x B.+ y) , do
        (a , p) ← xim
        (b , q) ← yim
        pure (a A.+ b , Linear.pres-+ a b ∙ ap₂ B._+_ p q)

    lac : ⌞ R ⌟ → image map → image map
    lac x (y , yim) = (x B.⋆ y) , do 
        (b , p) ← yim
        pure (x A.⋆ b , Linear.pres-⋆ x b ∙ ap (x B.⋆_) p)

    inv : image map → image map
    inv (x , xim) = B.- x ,  do 
        (a , p) ← xim
        pure (A.- a , Linear.pres-neg ∙ ap (B.-_) p)

    mk-group : make-group (image map)
    mk-group .make-group.group-is-set = hlevel!
    mk-group .make-group.mul = add
    mk-group .make-group.inv = inv
    mk-group .make-group.assoc (x , xi) (y , yi) (z , zi) = Σ-path B.+-assoc (squash _ _)
    mk-group .make-group.unit = B.0g , pure (A.0g , Linear.pres-0)
    mk-group .make-group.invl _ = Σ-path B.+-invl (squash _ _)
    mk-group .make-group.idl _ = Σ-path B.+-idl (squash _ _)

    add-ab : is-abelian-group add
    add-ab .is-abelian-group.has-is-group = Group-on.has-is-group (to-group-on mk-group)
    add-ab .is-abelian-group.commutes = Σ-path B.+-comm (squash _ _)

    add-lac-mod : is-module R add lac
    add-lac-mod .is-module.has-is-ab = add-ab
    add-lac-mod .is-module.⋆-distribl _ _ _ = Σ-path (B.⋆-distribl _ _ _) (squash _ _)
    add-lac-mod .is-module.⋆-distribr _ _ _ = Σ-path (B.⋆-distribr _ _ _) (squash _ _)
    add-lac-mod .is-module.⋆-assoc _ _ _ = Σ-path (B.⋆-assoc _ _ _) (squash _ _)
    add-lac-mod .is-module.⋆-id _ = Σ-path (B.⋆-id _) (squash _ _)

    image-module : Module-on R (image map)
    image-module .Module-on._+_ = add
    image-module .Module-on._⋆_ = lac
    image-module .Module-on.has-is-mod = add-lac-mod

    kOb : Ob
    kOb = (el! (image map) , image-module)

    kern : Hom kOb A
    kern = total-hom {!   !} {!   !}

    ker : Kernel _ _ f
    ker .Kernel.ker = kOb
    ker .Kernel.kernel = {!   !} 
    ker .Kernel.has-is-kernel = {!   !}
R-Mod-is-pre-abelian .is-pre-abelian.cokernel = {!   !}   

-- R-Mod-is-abelian : is-abelian (R-Mod R ℓ)    
-- R-Mod-is-abelian .is-abelian.has-is-preab = {!   !}  
-- R-Mod-is-abelian .is-abelian.coker-ker≃ker-coker = {!   !}    