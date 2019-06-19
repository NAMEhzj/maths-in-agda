--library=maths

open import Relation.Binary.Core
open import Agda.Primitive

open import Base.Equivalence renaming (_∘_ to _comp_)
open import Algebra.Group.Group
open import Base.Sets
open import Base.Factorization
import Algebra.Group.Subgroup as Subgroup

module SubgroupProps {l k} (G : Set l) (G' : Group G) (H : 𝒫 G {k}) (H' : Subgroup.Subgroup G G' H) where 

open Group G'
open import Algebra.Group.GroupProps1 G G'


_≈_ : Rel G (l ⊔ k)
_≈_ a b = a ∘ (b ⁻¹) ∈ H

open IsEquivalence

open Subgroup.Subgroup H'

eqr : IsEquivalence _≈_
IsEquivalence.refl eqr {x} = subst (_∈ H) (=sym (RInv x)) e∈U --[ LInv x ]and[ e∈U ] {P = λ z → z ∈ H}  
sym eqr {x} {y} xy⁻¹∈H = subst (_∈ H) ((x ∘ y ⁻¹) ⁻¹      =⟨ ∘-inv x (y ⁻¹) ⟩
                                       (y ⁻¹) ⁻¹ ∘ (x ⁻¹) =⟨ doubleInv y under _∘ (x ⁻¹) ⟩
                                       y ∘ (x ⁻¹)         □=) (inv-closed (x ∘ y ⁻¹) xy⁻¹∈H)
trans eqr {x} {y} {z} xy⁻¹∈H yz⁻¹∈H = subst (_∈ H) ((x ∘ y ⁻¹) ∘ (y ∘ z ⁻¹) =⟨ Assoc x (y ⁻¹) (y ∘ z ⁻¹) ⟩
                                                    x ∘ (y ⁻¹ ∘ (y ∘ z ⁻¹)) =⟨ =sym (Assoc (y ⁻¹) y (z ⁻¹)) under x ∘_ ⟩
                                                    x ∘ ((y ⁻¹ ∘ y) ∘ z ⁻¹) =⟨ LInv y under (λ t → x ∘ (t ∘ z ⁻¹)) ⟩
                                                    x ∘ (e ∘ z ⁻¹)          =⟨ LNeut (z ⁻¹) under x ∘_ ⟩
                                                    x ∘ z ⁻¹                □=) (∘-closed (x ∘ y ⁻¹) (y ∘ z ⁻¹) xy⁻¹∈H yz⁻¹∈H)


factorGroup : Set (l ⊔ k)
factorGroup = factorize G _≈_ eqr

factorGroupStruct : Group factorGroup
Group.e factorGroupStruct = factormap e
Group._∘_ factorGroupStruct = liftToFactor2 (λ a b → factormap  (a ∘ b)) λ x y v w x≈y v≈w → {!!}
