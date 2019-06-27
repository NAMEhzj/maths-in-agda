--library=maths

open import Relation.Binary.Core
open import Algebra.Field.Field
open import Agda.Primitive
open import Relation.Nullary
open import Data.List
open import Data.Sum

module Algebra.VectorSpace.Core where


record VectorSpace {a b} {A : Set a} (F : Field A) (V : Set b) : Set (a ⊔ b) where
                            infix 7 -_
                            infixr 8 _∙_
                            infixr 6 _+_
                            infixr 7 _+'_
                            infix 10 -'_
                            infixr 9 _*_
                            _+'_ = Field._+_ F
                            -'_ = Field.-_ F
                            zero = Field.zero F
                            _*_ = Field._*_ F
                            _⁻¹[_] = Field._⁻¹[_] F
                            one = Field.one F
                            field
                             zvect : V
                             _+_ : V → V → V
                             -_ : V → V
                             _∙_ : A → V → V
                             addComm : (v w : V) → v + w ≡ w + v
                             addAssoc : (u v w : V) → u + (v + w) ≡ (u + v) + w
                             zeroLNeut : (v : V) → zvect + v ≡ v
                             zeroRNeut : (v : V) → v + zvect ≡ v
                             addLInv : (v : V) → - v + v ≡ zvect
                             addRInv : (v : V) → v + - v ≡ zvect
                             scaleLDist : (α : A) → (v w : V) → α ∙ (v + w) ≡ α ∙ v + α ∙ w
                             scaleRDist : (α β : A) → (v : V) → (α +' β) ∙ v ≡ α ∙ v + β ∙ v
                             scaleMultAssoc : (α β : A) → (v : V) → α * β ∙ v ≡ α ∙ β ∙ v
                             oneNeut : (v : V) → one ∙ v ≡ v
                             isZvect : (v : V) → v ≡ zvect ⊎ ¬ v ≡ zvect
                             
                             

                       
         
