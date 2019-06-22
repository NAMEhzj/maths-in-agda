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
e∈U (propSubgroup P closed) = ∣ closedProp.Pe closed ∣
∘-closed (propSubgroup P closed) x y ∣Px∣ ∣Py∣ = liftToTrunc2* prf ∣Px∣ ∣Py∣
                                                    where prf : P x → P y → ∥ P (x ∘ y) ∥
                                                          prf Px Py = ∣ closedProp.∘-closed closed x y Px Py ∣ 
inv-closed (propSubgroup P closed) x ∣Px∣ = liftToTrunc* prf ∣Px∣
                                                    where prf : P x → ∥ P (x ⁻¹) ∥
                                                          prf Px = ∣ closedProp.inv-closed closed x Px ∣


open Base.Sets.𝒫

neutSubset : 𝒫 G
elem neutSubset x = x ≡ e
unique neutSubset x p1 p2 = axiom-k

open import Algebra.Group.GroupProps1 G G'


neutSubgroup : Subgroup neutSubset
e∈U neutSubgroup = refl
∘-closed neutSubgroup a b refl refl = Group.LNeut G' e 
inv-closed neutSubgroup a refl = neutInv


wholeGroup : Subgroup (wholeSet G)
e∈U wholeGroup = tt 
∘-closed wholeGroup a b _ _ = tt
inv-closed wholeGroup a _ = tt



