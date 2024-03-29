--library=maths-library

open import Relation.Binary.Core
open import Relation.Nullary
open import Data.Sum

module Algebra.Field.Core where




record Field {l} (F : Set l) : Set l where
         infixr 7 _+_ 
         infixr 9 _*_
         infix 11 _⁻¹[_]
         infix 10 -_
         field
           zero : F
           one : F
           _+_ : F → F → F
           _*_ : F → F → F 
           -_ : F → F
           _⁻¹[_] : (x : F) → ¬ x ≡ zero → F
           addComm : (x y : F) → x + y ≡ y + x
           addAssoc : (x y z : F) → x + (y + z) ≡ (x + y) + z
           zeroLNeut : (x : F) → zero + x ≡ x
           zeroRNeut : (x : F) → x + zero ≡ x
           addLInv : (x : F) → (- x) + x ≡ zero
           addRInv : (x : F) → x + (- x) ≡ zero
           multComm : (x y : F) → x * y ≡ y * x
           multAssoc : (x y z : F) → x * (y * z) ≡ (x * y) * z
           oneLNeut : (x : F) → one * x ≡ x
           oneRNeut : (x : F) → x * one ≡ x
           multLInv : (x : F) → (x≠0 : ¬ x ≡ zero) → x ⁻¹[ x≠0 ] * x ≡ one
           multRInv : (x : F) → (x≠0 : ¬ x ≡ zero) → x * (x ⁻¹[ x≠0 ]) ≡ one
           LDist : (x y z : F) → x * (y + z) ≡ x * y + x * z
           RDist : (x y z : F) → (x + y) * z ≡ x * z + y * z
           one≠zero : ¬ one ≡ zero
           isZero : (x : F) → x ≡ zero ⊎ ¬ x ≡ zero
           
           
          
