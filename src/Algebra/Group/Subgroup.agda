--library=maths

open import Algebra.Group.Group
open import Base.Sets
open import Base.Equivalence hiding (_∘_)
open import Agda.Primitive
open import Base.PropTruncation
open import Data.Unit

module Algebra.Group.Subgroup {l} (G : Set l) (G' : Group G) where  

open Group G'

record Subgroup {b} (U : 𝒫 G {b}) : Set (l ⊔ b) where
                field
                  e∈U : e ∈ U
                  ∘-closed : (x y : G) → x ∈ U → y ∈ U → x ∘ y ∈ U 
                  inv-closed : (x : G) → x ∈ U → x ⁻¹ ∈ U



record closedProp {m} (P : (x : G) → Set m) : Set (l ⊔ m) where
                 field
                  Pe : P e
                  ∘-closed : (x y : G) → P x → P y → P (x ∘ y)
                  inv-closed : (x : G) → P x → P (x ⁻¹)


open Subgroup

propSubgroup : ∀{m} (P : (a : G) → Set m) → closedProp P → Subgroup (propSubset P)
e∈U (propSubgroup P closed) = (e , ∣ closedProp.Pe closed ∣) , refl
∘-closed (propSubgroup P closed) x y ((.x , ∣Px∣) , refl)  ((.y , ∣Py∣) , refl) = ((x ∘ y , liftToTrunc2* prf ∣Px∣ ∣Py∣) , refl)
                                                               where prf : P x → P y → ∥ P (x ∘ y) ∥
                                                                     prf Px Py = ∣ closedProp.∘-closed closed x y Px Py ∣ 
inv-closed (propSubgroup P closed) x ((.x , ∣Px∣) , refl) = ((x ⁻¹ , liftToTrunc* prf ∣Px∣) , refl)
                                                               where prf : P x → ∥ P (x ⁻¹) ∥
                                                                     prf Px = ∣ closedProp.inv-closed closed x Px ∣


open Base.Sets.𝒫

neutSubset : 𝒫 G
U neutSubset = ⊤
i neutSubset tt = e
injective neutSubset tt tt _ = refl

open import Algebra.Group.GroupProps1 G G'

neutSubgroup : Subgroup neutSubset
e∈U neutSubgroup = tt , refl
∘-closed neutSubgroup a b (tt , refl)  (tt , refl) = tt , =sym (Group.LNeut G' e) 
inv-closed neutSubgroup a (tt , refl) = tt , =sym neutInv


wholeGroup : Subgroup (wholeSet G)
e∈U wholeGroup = e , refl 
∘-closed wholeGroup a b _ _ = a ∘ b , refl
inv-closed wholeGroup a _ = a ⁻¹ , refl



