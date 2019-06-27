--library=maths

open import Algebra.Field.Core
open import Base.Equivalence
open import Relation.Binary.Core
open import Agda.Primitive
open import Relation.Nullary
open import Data.Product
open import Data.Empty
open import Data.Nat using (ℕ) renaming (_≤_ to _≤ℕ_)

import Algebra.Field.Props as FP


module RealNumbers where


data Sign : Set where
       pos : Sign
       zer : Sign
       neg : Sign

pos≠zer : ¬ pos ≡ zer
pos≠zer ()

pos≠neg : ¬ pos ≡ neg
pos≠neg ()

zer≠neg : ¬ zer ≡ neg
zer≠neg ()

record RealNumberImpl : Set₁ where
        field
         R : Set
         FieldR : Field R
         decSign : R → Sign
         zeroSignIsZero : (r : R) → (decSign r ≡ zer) ⇔ (r ≡ Field.zero FieldR)
        open Field FieldR
        _-₂_ = λ x y → x + (Field.-_ FieldR y)
        _times_ : ℕ → R → R
        n times r = FP.sum FieldR {n} (λ i → r) 
        field
         signFlip1 : (r : R) → (decSign r ≡ pos) → decSign (- r) ≡ neg
         signFlip2 : (r : R) → (decSign r ≡ neg) → decSign (- r) ≡ pos
         sign-add-cong : (r s : R) → decSign r ≡ pos → decSign s ≡ pos → decSign (r + s) ≡ pos
         sign-mult-cong : (r s : R) → decSign r ≡ pos → decSign s ≡ pos → decSign (r * s) ≡ pos
         archimedean : (r ε : R) → decSign r ≡ pos → decSign ε ≡ pos → Σ ℕ (λ n → decSign ((n times ε) -₂ r) ≡ pos)
         completeness : (x : ℕ → R) → ((ε : R) → decSign ε ≡ pos → Σ ℕ (λ N → (n m : ℕ) → N ≤ℕ n → N ≤ℕ m → decSign (ε + (x n -₂ x m)) ≡ pos))
                                     → Σ R (λ z → ((ε : R) → decSign ε ≡ pos  → Σ ℕ (λ N → (n : ℕ) → N ≤ℕ n → (decSign (ε + (x n -₂ z)) ≡ pos × decSign (ε + (z -₂ x n)) ≡ pos))))



postulate RealNumbers : RealNumberImpl



ℝ = RealNumberImpl.R RealNumbers
ℝ' = RealNumberImpl.FieldR RealNumbers

open FP ℝ'

sign : ℝ → Sign
sign = RealNumberImpl.decSign RealNumbers

_<_ : ℝ → ℝ → Set
x < y = sign (y + (- x)) ≡ pos

_≤_ : ℝ → ℝ → Set
x ≤ y = ¬ y < x

zeroSign : sign zero ≡ zer
zeroSign = _⇔_.from (RealNumberImpl.zeroSignIsZero RealNumbers zero) refl

signZer : (x : ℝ) → sign x ≡ zer → x ≡ zero
signZer x sx=0 = _⇔_.to (RealNumberImpl.zeroSignIsZero RealNumbers x) sx=0

signProof : (x : ℝ) → Σ Sign (λ s → sign x ≡ s)
signProof x = (sign x , refl)

data Comparison (x y : ℝ) : Set where
          Smaller : x < y → Comparison x y
          Equal : x ≡ y → Comparison x y
          Bigger : y < x → Comparison x y

_~_ : (x y : ℝ) → Comparison x y
x ~ y with signProof (x + (- y))
... | (pos , x>y) = Bigger x>y 
... | (zer , sx-y=0) = Equal (x               =⟨ =sym (Field.zeroRNeut ℝ' x) ⟩
                              x + zero        =⟨ =sym (Field.addLInv ℝ' y) under (x +_) ⟩
                              x + (- y + y)   =⟨ Field.addAssoc ℝ' x (- y) y ⟩
                              (x + (- y)) + y =⟨ signZer (x + (- y)) sx-y=0 under _+ y ⟩
                              zero + y        =⟨ Field.zeroLNeut ℝ' y ⟩
                              y □=)
... | (neg , x<y) = Smaller (sign (y + (- x))                     =⟨ =sym (doubleNeg y) under (λ t → sign (t + (- x))) ⟩
                             sign (- (- y) + (- x))               =⟨ =sym (negDist (- y) x) under sign ⟩
                             sign (- ((- y) + x))                 =⟨ Field.addComm ℝ' (- y) x under (λ t → sign (- t)) ⟩
                             sign (- (x + (- y)))                 =⟨ RealNumberImpl.signFlip2 RealNumbers (x + - y) x<y ⟩
                             pos □=)




∣_∣ : ℝ → ℝ
∣ x ∣ with (x ~ zero)
... | (Bigger _)  = x
... | (Equal  _)  = x
... | (Smaller _) = - x
