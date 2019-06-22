--library=maths

open import Relation.Binary.Core
open import Agda.Primitive

open import Base.Equivalence renaming (_∘_ to _comp_)
open import Algebra.Group.Group
open import Base.Sets
open import Base.Factorization
open import Base.PropTruncation
import Algebra.Group.Subgroup as Subgroup

module SubgroupProps {l k} (G : Set l) (G' : Group G) (H : 𝒫 G {k}) (H' : Subgroup.Subgroup G G' H) where 

open Group G'
open import Algebra.Group.GroupProps1 G G'


_~_ : Rel G k
_~_ a b = a ∘ (b ⁻¹) ∈ H

open IsEquivalence

open Subgroup.Subgroup H'

eqr : IsEquivalence _~_
IsEquivalence.refl eqr {x} = subst (_∈ H) (=sym (RInv x)) e∈U --[ LInv x ]and[ e∈U ] {P = λ z → z ∈ H}  
sym eqr {x} {y} xy⁻¹∈H = subst (_∈ H) ((x ∘ y ⁻¹) ⁻¹      =⟨ ∘-inv x (y ⁻¹) ⟩
                                       (y ⁻¹) ⁻¹ ∘ (x ⁻¹) =⟨ doubleInv y under _∘ (x ⁻¹) ⟩
                                       y ∘ (x ⁻¹)         □=) (inv-closed (x ∘ y ⁻¹) xy⁻¹∈H)
trans eqr {x} {y} {z} xy⁻¹∈H yz⁻¹∈H = subst (_∈ H) ((x ∘ y ⁻¹) ∘ (y ∘ z ⁻¹) =⟨ Assoc x (y ⁻¹) (y ∘ z ⁻¹) ⟩
                                                    x ∘ (y ⁻¹ ∘ (y ∘ z ⁻¹)) =⟨ =sym (Assoc (y ⁻¹) y (z ⁻¹)) under x ∘_ ⟩
                                                    x ∘ ((y ⁻¹ ∘ y) ∘ z ⁻¹) =⟨ LInv y under (λ t → x ∘ (t ∘ z ⁻¹)) ⟩
                                                    x ∘ (e ∘ z ⁻¹)          =⟨ LNeut (z ⁻¹) under x ∘_ ⟩
                                                    x ∘ z ⁻¹                □=) (∘-closed (x ∘ y ⁻¹) (y ∘ z ⁻¹) xy⁻¹∈H yz⁻¹∈H)



normal : Set (l ⊔ k)
normal = (x h : G) → h ∈ H → x ∘ (h ∘ (x ⁻¹)) ∈ H 


factorGroup : Set (l ⊔ k)
factorGroup = factorize G _~_ eqr



_='⟨_⟩_ : ∀{k l} → {A : Set k} → {P : A → Set l} (x : A) → {y : A} → x ≡ y → P x → P y 
_='⟨_⟩_ x refl px = px



∘-cong : normal → (x y v w : G) → x ~ y → v ~ w → factormap {R = _~_} {eqr = eqr} (x ∘ v) ≡ factormap (y ∘ w)
∘-cong norm x y v w x~y v~w = factmap-cong (x ∘ v) (y ∘ w) ([_]and[_] {P = λ t → t ∈ H} eq pf2)
                                       where g = v ∘ (w ⁻¹)
                                             pf1 : x ∘ g ∘ (x ⁻¹) ∈ H
                                             pf1 = norm x g v~w
                                             pf2 : (x ∘ g ∘ (x ⁻¹)) ∘ (x ∘ (y ⁻¹)) ∈ H
                                             pf2 = ∘-closed (x ∘ g ∘ (x ⁻¹)) (x ∘ (y ⁻¹)) pf1 x~y
                                             eq : (x ∘ v) ∘ ((y ∘ w) ⁻¹) ≡ (x ∘ g ∘ (x ⁻¹)) ∘ (x ∘ (y ⁻¹))
                                             eq = (x ∘ v) ∘ ((y ∘ w) ⁻¹)       =⟨ ∘-inv y w under (x ∘ v) ∘_ ⟩
                                                  (x ∘ v) ∘ (w ⁻¹ ∘ y ⁻¹)      =⟨ Assoc x v ((w ⁻¹) ∘ (y ⁻¹)) ⟩
                                                  x ∘ (v ∘ (w ⁻¹ ∘ y ⁻¹))      =⟨ =sym (Assoc v (w ⁻¹) (y ⁻¹)) under x ∘_ ⟩
                                                  x ∘ g ∘ (y ⁻¹)               =⟨ =sym (LNeut (y ⁻¹)) under (λ t → x ∘ g ∘ t) ⟩
                                                  x ∘ g ∘ (e ∘ y ⁻¹)           =⟨ =sym (LInv x) under (λ t → x ∘ g ∘ (t ∘ (y ⁻¹))) ⟩
                                                  x ∘ g ∘ (x ⁻¹ ∘ x) ∘ (y ⁻¹)  =⟨ Assoc (x ⁻¹) x (y ⁻¹) under (λ t → x ∘ g ∘ t) ⟩
                                                  x ∘ g ∘ (x ⁻¹) ∘ x ∘ y ⁻¹    =⟨ =sym (Assoc g (x ⁻¹) (x ∘ y ⁻¹)) under x ∘_ ⟩
                                                  x ∘ (g ∘ x ⁻¹) ∘ (x ∘ y ⁻¹)  =⟨ =sym (Assoc x (g ∘ (x ⁻¹)) (x ∘ y ⁻¹)) ⟩
                                                  (x ∘ g ∘ x ⁻¹) ∘ (x ∘ y ⁻¹) □=

factor-∘ : normal → factorGroup → factorGroup → factorGroup
factor-∘ norm = liftToFactor2 (λ x y → factormap (x ∘ y)) (∘-cong norm)

inv-cong : normal → (x y : G) → x ~ y → factormap {R = _~_} {eqr = eqr} (x ⁻¹) ≡ factormap (y ⁻¹)
inv-cong norm x y x~y = factmap-cong (x ⁻¹) (y ⁻¹) ([_]and[_] {P = λ t → t ∈ H} eq (norm (y ⁻¹) ((x ∘ y ⁻¹) ⁻¹) (inv-closed (x ∘ y ⁻¹) x~y)))
                                         where eq = x ⁻¹ ∘ (y ⁻¹) ⁻¹                 =⟨ doubleInv y under x ⁻¹ ∘_ ⟩
                                                    x ⁻¹ ∘ y                         =⟨ =sym (LNeut (x ⁻¹ ∘ y)) ⟩
                                                    e ∘ x ⁻¹ ∘ y                     =⟨ =sym (LInv y) under _∘ (x ⁻¹ ∘ y) ⟩ 
                                                    (y ⁻¹ ∘ y) ∘ x ⁻¹ ∘ y            =⟨ Assoc (y ⁻¹) y (x ⁻¹ ∘ y) ⟩
                                                    y ⁻¹ ∘ y ∘ x ⁻¹ ∘ y              =⟨ =sym (Assoc y (x ⁻¹) y) under y ⁻¹ ∘_ ⟩
                                                    y ⁻¹ ∘ (y ∘ x ⁻¹) ∘ y            =⟨ =sym (doubleInv y) under (λ t → y ⁻¹ ∘ (t ∘ x ⁻¹) ∘ y) ⟩
                                                    y ⁻¹ ∘ ((y ⁻¹) ⁻¹ ∘ x ⁻¹) ∘ y    =⟨ =sym (∘-inv x (y ⁻¹)) under (λ t → y ⁻¹ ∘ t ∘ y) ⟩
                                                    y ⁻¹ ∘ (x ∘ y ⁻¹) ⁻¹ ∘ y         =⟨ =sym (doubleInv y) under (λ t → y ⁻¹ ∘ (x ∘ y ⁻¹) ⁻¹ ∘ t) ⟩
                                                    y ⁻¹ ∘ (x ∘ y ⁻¹) ⁻¹ ∘ (y ⁻¹) ⁻¹ □=
factor-inv : normal → factorGroup → factorGroup
factor-inv norm = liftToFactor (λ x → factormap (x ⁻¹)) (inv-cong norm)


factorGroupStruct : normal → Group factorGroup
Group.e (factorGroupStruct _) = factormap e
Group._∘_ (factorGroupStruct norm) = factor-∘ norm
Group._⁻¹ (factorGroupStruct norm) = factor-inv norm
Group.Assoc (factorGroupStruct norm) x y z = getEq (proof-lift3 (λ a b c → (a ∙ b) ∙ c ≡ a ∙ (b ∙ c)) lowerPf x y z)
                                                  where _∙_ = factor-∘ norm
                                                        lowerPf : (x y z : G) → ∥ (factormap x ∙ factormap y) ∙ factormap z ≡
                                                                                factormap x ∙ (factormap y ∙ factormap z) ∥
                                                        lowerPf x y z = ∣ (x* ∙ y*) ∙ z*           =⟨ lift2-cong (λ x y → factormap (x ∘ y)) (∘-cong norm) x y under _∙ z* ⟩
                                                                          factormap (x ∘ y) ∙ z*   =⟨ lift2-cong (λ x y → factormap (x ∘ y)) (∘-cong norm) (x ∘ y) z ⟩
                                                                          factormap ((x ∘  y) ∘ z) =⟨ Assoc x y z under factormap ⟩
                                                                          factormap (x ∘ (y ∘ z))  =⟨ =sym (lift2-cong (λ x y → factormap (x ∘ y)) (∘-cong norm) x (y ∘ z)) ⟩
                                                                          x* ∙ factormap (y ∘ z)   =⟨ =sym (lift2-cong (λ x y → factormap (x ∘ y)) (∘-cong norm) y z under x* ∙_) ⟩
                                                                          x* ∙ (y* ∙ z*) □= ∣
                                                         where x* = factormap x
                                                               y* = factormap y
                                                               z* = factormap z
Group.LNeut (factorGroupStruct norm) x = getEq (proof-lift (λ a → (factormap e) ∙ a ≡ a) lowerPf x)
                                           where _∙_ = factor-∘ norm
                                                 lowerPf : (x : G) → ∥ (factormap e) ∙ factormap x ≡ factormap x ∥
                                                 lowerPf x = ∣ e* ∙ x*           =⟨ lift2-cong (λ x y → factormap (x ∘ y)) (∘-cong norm) e x ⟩
                                                               factormap (e ∘ x) =⟨ (LNeut x) under factormap ⟩
                                                               x* □= ∣
                                                   where x* = factormap x
                                                         e* = factormap e
Group.RNeut (factorGroupStruct norm) x = getEq (proof-lift (λ a → a ∙ (factormap e) ≡ a) lowerPf x)
                                           where _∙_ = factor-∘ norm
                                                 lowerPf : (x : G) → ∥ (factormap x) ∙ factormap e ≡ factormap x ∥
                                                 lowerPf x = ∣ x* ∙ e*           =⟨ lift2-cong (λ x y → factormap (x ∘ y)) (∘-cong norm) x e ⟩
                                                               factormap (x ∘ e) =⟨ (RNeut x) under factormap ⟩
                                                               x* □= ∣
                                                   where x* = factormap x
                                                         e* = factormap e
Group.LInv (factorGroupStruct norm) x = getEq (proof-lift (λ a → (inv a) ∙ a ≡ factormap e) lowerPf x)
                                           where _∙_ = factor-∘ norm
                                                 inv = factor-inv norm
                                                 lowerPf : (x : G) → ∥ (inv (factormap x)) ∙ factormap x ≡ factormap e ∥
                                                 lowerPf x = ∣ (inv x*) ∙ x*         =⟨ lift-cong (λ x → factormap (x ⁻¹)) (inv-cong norm) under (λ f → (f x) ∙ x*) ⟩
                                                               factormap (x ⁻¹) ∙ x* =⟨ lift2-cong (λ x y → factormap (x ∘ y)) (∘-cong norm) (x ⁻¹) x ⟩
                                                               factormap (x ⁻¹ ∘ x)  =⟨ LInv x under factormap ⟩
                                                               e* □= ∣
                                                   where x* = factormap x
                                                         e* = factormap e
Group.RInv (factorGroupStruct norm) x = getEq (proof-lift (λ a → a ∙ (inv a)≡ factormap e) lowerPf x)
                                           where _∙_ = factor-∘ norm
                                                 inv = factor-inv norm
                                                 lowerPf : (x : G) → ∥ factormap x ∙ inv (factormap x) ≡ factormap e ∥
                                                 lowerPf x = ∣ x* ∙ (inv x*)         =⟨ lift-cong (λ x → factormap (x ⁻¹)) (inv-cong norm) under (λ f → x* ∙ (f x)) ⟩
                                                               x* ∙ factormap (x ⁻¹) =⟨ lift2-cong (λ x y → factormap (x ∘ y)) (∘-cong norm) x (x ⁻¹) ⟩
                                                               factormap (x ∘ x ⁻¹)  =⟨ RInv x under factormap ⟩
                                                               e* □= ∣
                                                   where x* = factormap x
                                                         e* = factormap e

                                       
