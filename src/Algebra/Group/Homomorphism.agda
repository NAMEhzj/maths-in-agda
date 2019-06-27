--library=maths

open import Agda.Primitive
open import Data.Unit

open import Base.Equivalence 
open import Base.PropTruncation
open import Base.Sets

open import Algebra.Group.Core


module Algebra.Group.Homomorphism {l m} (G : Set l) (H : Set m) (G' : Group G) (H' : Group H) where

import Algebra.Group.Props1 G G' as GP
import Algebra.Group.Props1 H H' as HP

_∙_ = Group._∘_ G'
e₁ = Group.e G'
_⁻¹₁ = Group._⁻¹ G'

infix 10 _⁻¹₁


_*_ = Group._∘_ H'
e₂ = Group.e H'
_⁻¹₂ = Group._⁻¹ H'


infix 10 _⁻¹₂


GroupHom : (G → H) → Set (l ⊔ m)
GroupHom φ = (a b : G) → φ (a ∙ b) ≡ φ a * φ b        

hom-neut-cong : (φ : G → H) → GroupHom φ → φ e₁ ≡ e₂
hom-neut-cong φ homφ = HP.LNeut-unique (φ e₁) (φ e₁)
                       ((φ e₁) * (φ e₁) =⟨ =sym (homφ e₁ e₁) ⟩
                        φ (e₁ ∙ e₁)     =⟨ Group.LNeut G' e₁ under φ  ⟩
                        φ e₁ □= )

hom-inv-cong : (φ : G → H) → GroupHom φ → (a : G) → φ (a ⁻¹₁) ≡ (φ a) ⁻¹₂
hom-inv-cong φ homφ a = HP.LInv-unique (φ (a ⁻¹₁)) (φ a)
                        ((φ (a ⁻¹₁)) * (φ a) =⟨ =sym (homφ (a ⁻¹₁) a) ⟩
                         φ ((a ⁻¹₁) ∙ a)     =⟨ Group.LInv G' a under φ ⟩
                         φ e₁                =⟨ hom-neut-cong φ homφ ⟩
                         e₂ □= )




import Algebra.Group.Subgroup G G' as SG
import Algebra.Group.Subgroup H H' as SH 


open 𝒫


preimageSubgroup : ∀{l} (φ : G → H) → GroupHom φ → (S : 𝒫 H {l}) →
                         SH.Subgroup S → SG.Subgroup (preimage φ S)
SG.Subgroup.e∈U (preimageSubgroup φ homφ S SisSG) = [ φ e₁ =⟨ hom-neut-cong φ homφ ⟩
                                                       e₂ □= ]and[ SH.Subgroup.e∈U SisSG ]
SG.Subgroup.∘-closed (preimageSubgroup φ homφ S SisSG) x y φx∈S φy∈S = [_]and[_] {P = (λ t → t ∈ S)}  φxy=φxφy φxφy∈S
                                                                          where φxy=φxφy : φ (x ∙ y) ≡ (φ x) * (φ y)
                                                                                φxy=φxφy = homφ x y
                                                                                φxφy∈S : (φ x) * (φ y) ∈ S
                                                                                φxφy∈S = SH.Subgroup.∘-closed SisSG (φ x) (φ y) φx∈S φy∈S
SG.Subgroup.inv-closed (preimageSubgroup φ homφ S SisSG) x φx∈S = [_]and[_] {P = λ t → t ∈ S}
                                                                        (φ (x ⁻¹₁) =⟨ hom-inv-cong φ homφ x ⟩
                                                                         (φ x) ⁻¹₂ □=)
                                                                        (SH.Subgroup.inv-closed SisSG (φ x) φx∈S)



kernel : (φ : G → H) → 𝒫 G
kernel φ = preimage φ SH.neutSubset 


kernelSubgroup : (φ : G → H) → GroupHom φ → SG.Subgroup (kernel φ)
kernelSubgroup φ homφ = preimageSubgroup φ homφ SH.neutSubset SH.neutSubgroup




open SH.closedProp


imClosed : (φ : G → H) → GroupHom φ → SH.closedProp (λ x → Σ G (λ a → φ a ≡ x))
Pe (imClosed φ homφ) = e₁ , hom-neut-cong φ homφ
∘-closed (imClosed φ homφ) x y (a , φa=x)  (b , φb=y) = a ∙ b , (φ (a ∙ b) =⟨ homφ a b ⟩
                                                                  φ a * φ b =⟨ φa=x under _* φ b ⟩
                                                                  x * φ b   =⟨ φb=y under x *_ ⟩
                                                                  x * y     □=)
inv-closed (imClosed φ homφ) x (a , φa=x) = a ⁻¹₁ , (φ (a ⁻¹₁) =⟨ hom-inv-cong φ homφ a ⟩
                                                     (φ a) ⁻¹₂ =⟨ φa=x under _⁻¹₂ ⟩
                                                     x ⁻¹₂ □=)


image-subgroup : (φ : G → H) → GroupHom φ → SH.Subgroup (wholeImage φ)
image-subgroup φ homφ = SH.propSubgroup (λ x → Σ G (λ a → φ a ≡ x)) (imClosed φ homφ)

open _⇔_


injective-kernel : (φ : G → H) → GroupHom φ → ((a b : G) → φ a ≡ φ b → a ≡ b) ⇔ ((kernel φ) ⊆ SG.neutSubset) 
from (injective-kernel φ homφ) kerφ⊆e a b φa=φb = a           =⟨ GP.LInv-unique a (b ⁻¹₁) ab⁻¹=e ⟩
                                                  (b ⁻¹₁) ⁻¹₁ =⟨ GP.doubleInv b ⟩
                                                  b □= 
                    where ab⁻¹∈kerφ : a ∙ (b ⁻¹₁) ∈ kernel φ
                          ab⁻¹∈kerφ = (φ (a ∙ (b ⁻¹₁))   =⟨ homφ a (b ⁻¹₁) ⟩
                                       φ a * φ (b ⁻¹₁)   =⟨ hom-inv-cong φ homφ b under (φ a *_) ⟩
                                       φ a * ((φ b) ⁻¹₂) =⟨ φa=φb under _* ((φ b) ⁻¹₂) ⟩
                                       φ b * ((φ b) ⁻¹₂) =⟨ Group.RInv H' (φ b) ⟩
                                       e₂ □=)
                          ab⁻¹=e : a ∙ (b ⁻¹₁) ≡ e₁
                          ab⁻¹=e = kerφ⊆e (a ∙ (b ⁻¹₁)) ab⁻¹∈kerφ
to (injective-kernel φ homφ) φinj a a∈kerφ = φinj a e₁ (φ a =⟨ a∈kerφ ⟩
                                                        e₂  =⟨ =sym (hom-neut-cong φ homφ) ⟩
                                                        φ e₁ □=)




surjective-image : (φ : G → H) → GroupHom φ → ((x : H) → ∥ Σ G (λ a → φ a ≡ x) ∥) ⇔ ((wholeImage φ) ⊇ wholeSet H)
from (surjective-image φ homφ) imφ⊇H x = imφ⊇H x tt
to (surjective-image φ homφ) φsurj x _ = φsurj x



