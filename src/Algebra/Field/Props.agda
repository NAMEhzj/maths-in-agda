--library=maths

open import Relation.Binary.Core
open import Relation.Nullary
open import Algebra.Field.Core
open import Base.Equivalence
open import Data.Fin renaming (zero to fzero) hiding (_+_)
open import Data.Nat using (ℕ) 

module Algebra.Field.Props {k} {F : Set k} (F' : Field F) where

infixr 5 _+_
infixr 6 _*_
infix 7 -_
infixr 8 _⁻¹[_]



zero = Field.zero F'
one = Field.one F'
_+_ = Field._+_ F'
_*_ = Field._*_ F'
-_ = Field.-_ F'
_⁻¹[_] = Field._⁻¹[_] F'


zero-LAbsorb : (x : F) → zero * x ≡ zero
zero-LAbsorb x = zero * x                   =⟨ =sym (Field.zeroRNeut F' (zero * x)) ⟩
                 zero * x + zero            =⟨ =sym (Field.addRInv F' x) under (λ t → zero * x + t) ⟩
                 zero * x + (x + - x)       =⟨ Field.addAssoc F' (zero * x) x (- x) ⟩
                 (zero * x + x) + - x       =⟨ =sym (Field.oneLNeut F' x) under (λ t → (zero * x + t) + - x) ⟩
                 (zero * x + one * x) + - x =⟨ =sym (Field.RDist F' zero one x) under (λ t → t + - x) ⟩
                 (zero + one) * x + - x     =⟨ (Field.zeroLNeut F' one) under (λ t → t * x + - x) ⟩
                 one * x + - x              =⟨ (Field.oneLNeut F' x) under (λ t → t + - x) ⟩
                 x + - x                    =⟨ Field.addRInv F' x ⟩
                 zero □=

zero-RAbsorb : (x : F) → x * zero ≡ zero
zero-RAbsorb x = x * zero  =⟨ Field.multComm F' x zero ⟩
                 zero * x  =⟨ zero-LAbsorb x ⟩
                 zero □=

negOne-Lmult : (x : F) → (- one) * x ≡ - x
negOne-Lmult x = (- one) * x                    =⟨ =sym (Field.zeroRNeut F' (- one * x)) ⟩
                (- one) * x + zero             =⟨ =sym (Field.addRInv F' x) under (- one * x +_ ) ⟩
                (- one) * x + (x + - x)        =⟨ Field.addAssoc F' (- one * x) x (- x) ⟩
                ((- one) * x + x) + - x        =⟨ =sym (Field.oneLNeut F' x) under (λ t → ((- one * x + t) + - x)) ⟩
                ((- one) * x + one * x) + - x  =⟨ =sym (Field.RDist F' (- one) one x) under (_+ - x) ⟩
                ( - one + one) * x + - x       =⟨ (Field.addLInv F' one) under (λ t → t * x + - x) ⟩
                zero * x + - x                 =⟨ zero-LAbsorb x under (_+ - x) ⟩
                zero + - x                     =⟨ Field.zeroLNeut F' (- x) ⟩
                - x □= 



negOne-Rmult : (x : F) → x * (- one) ≡ - x
negOne-Rmult x = x * (- one)  =⟨ Field.multComm F' x (- one) ⟩
                 (- one) * x  =⟨ negOne-Lmult x ⟩
                 - x  □=



addRInv-unique : (x y : F) → x + y ≡ zero → y ≡ - x
addRInv-unique x y x+y=0 = y              =⟨ =sym (Field.zeroLNeut F' y) ⟩
                           zero + y       =⟨ =sym (Field.addLInv F' x) under (_+ y) ⟩
                           (- x + x) + y  =⟨ =sym (Field.addAssoc F' (- x) x y) ⟩
                           - x + (x + y)  =⟨ x+y=0 under (- x +_) ⟩
                           - x + zero     =⟨ Field.zeroRNeut F' (- x) ⟩
                           - x □=

addLInv-unique : (x y : F) → y + x ≡ zero → y ≡ - x
addLInv-unique x y x+y=0 = y              =⟨ =sym (Field.zeroRNeut F' y) ⟩
                           y + zero       =⟨ =sym (Field.addRInv F' x) under (y +_) ⟩
                           y + (x + - x)  =⟨ Field.addAssoc F' y x (- x) ⟩
                           (y + x) + - x  =⟨ x+y=0 under (_+ - x) ⟩
                           zero + - x     =⟨ Field.zeroLNeut F' (- x) ⟩
                           - x □=

doubleNeg : (x : F) → - (- x) ≡ x
doubleNeg x = =sym (addRInv-unique (- x) x (Field.addLInv F' x))


negOne-Lmult-n : (x : F) → (- one) * (- x) ≡ x
negOne-Lmult-n x = (- one) * (- x) =⟨ negOne-Lmult (- x) ⟩
                   - (- x)         =⟨ doubleNeg x ⟩
                   x □=


negOne-Rmult-n : (x : F) → (- x) * (- one) ≡ x
negOne-Rmult-n x = (- x) * (- one) =⟨ negOne-Rmult (- x) ⟩
                   - (- x)         =⟨ doubleNeg x ⟩
                   x □=

negDist : (x y : F) → - (x + y) ≡ - x + - y
negDist x y = - (x + y)      =⟨ =sym (negOne-Lmult (x + y)) ⟩
              n1 * (x + y)    =⟨ Field.LDist F' n1 x y ⟩
              n1 * x + n1 * y =⟨ negOne-Lmult x under _+ n1 * y ⟩
              - x + n1 * y    =⟨ negOne-Lmult y under (- x +_) ⟩
              - x + - y □=
                where n1 = - one


neg-nonzero : {x : F} → ¬ x ≡ zero → ¬ - x ≡ zero
neg-nonzero {x} x≠0 nx=0 = x≠0 (x         =⟨ =sym (Field.zeroRNeut F' x) ⟩
                                x + zero  =⟨ (=sym nx=0) under (λ t → x + t) ⟩
                                x + (- x) =⟨ Field.addRInv F' x ⟩
                                zero □=)


inv-nonzero : {x : F} → (x≠0 : ¬ x ≡ zero) → ¬ x ⁻¹[ x≠0 ] ≡ zero
inv-nonzero {x} x≠0 x⁻¹=0 = Field.one≠zero F' (one             =⟨ =sym (Field.multRInv F' x x≠0) ⟩
                                               x * x ⁻¹[ x≠0 ] =⟨ x⁻¹=0 under x *_ ⟩
                                               x * zero        =⟨ zero-RAbsorb x ⟩
                                               zero □=)

nonzero-split : (x y : F) → ¬ x ≡ zero → ¬ y ≡ zero → ¬ x * y ≡ zero
nonzero-split x y x≠0 y≠0 x*y=0 = (≠sym (Field.one≠zero F')) (zero                                     =⟨ =sym (zero-LAbsorb (y⁻¹ * x⁻¹)) ⟩
                                                     zero *     (y⁻¹  * x⁻¹)  =⟨ (=sym x*y=0) under (λ t → t * (y⁻¹  * x⁻¹)) ⟩
                                                     (x *  y) * (y⁻¹  * x⁻¹)  =⟨ =sym (Field.multAssoc F' x y (y⁻¹  * x⁻¹)) ⟩
                                                      x * (y  * (y⁻¹  * x⁻¹)) =⟨ Field.multAssoc F' y (y⁻¹) (x⁻¹) under (λ t → x * t) ⟩
                                                      x * ((y *  y⁻¹) * x⁻¹)  =⟨ Field.multRInv F' y y≠0 under (λ t → x * (t * x⁻¹)) ⟩
                                                      x * (one *        x⁻¹)  =⟨ Field.oneLNeut F' (x⁻¹) under (λ t → x * t) ⟩
                                                      x *               x⁻¹   =⟨ Field.multRInv F' x x≠0 ⟩
                                                     one □= )
                                                       where x⁻¹ = x ⁻¹[ x≠0 ]
                                                             y⁻¹ = y ⁻¹[ y≠0 ]


onezero-split : (x y : F) → x * y ≡ zero → ¬ x ≡ zero → y ≡ zero
onezero-split x y x*y=0 x≠0 = y             =⟨ =sym (Field.oneLNeut F' y) ⟩
                             one * y        =⟨ =sym (Field.multLInv F' x x≠0) under (λ t → t * y) ⟩
                             (x⁻¹ * x) * y  =⟨ =sym (Field.multAssoc F' x⁻¹ x y) ⟩
                              x⁻¹ * (x * y) =⟨ x*y=0 under (λ t → x⁻¹ * t) ⟩
                              x⁻¹ * zero    =⟨ zero-RAbsorb x⁻¹ ⟩
                              zero □=
                                  where x⁻¹ = x ⁻¹[ x≠0 ]



open ℕ renaming (zero to nzero)

sum : {n : ℕ} → (xs : Fin n → F) → F
sum {nzero}  _  = zero
sum {suc n} xs = xs fzero + sum (λ i → xs (suc i))


sum-zero : {n : ℕ} → sum {n} (λ i → zero) ≡ zero
sum-zero {nzero}  = refl
sum-zero {suc n} = zero + sum {n} (λ i → zero) =⟨ Field.zeroLNeut F' (sum {n} (λ i → zero)) ⟩
                     sum {n} (λ i → zero)        =⟨ sum-zero {n} ⟩
                     zero □=


sum-join : {n : ℕ} → (xs ys : Fin n → F) → sum xs + sum ys ≡ sum (λ i → xs i + ys i)
sum-join {nzero}  _  _  = Field.zeroLNeut F' zero 
sum-join {suc n} xs ys = (x₁ + xrest) + (y₁ + yrest) =⟨ =sym (Field.addAssoc F' x₁ xrest (y₁ + yrest)) ⟩
                           x₁ + (xrest + (y₁ + yrest)) =⟨ (Field.addAssoc F' xrest y₁ yrest) under (λ t → x₁ + t) ⟩
                           x₁ + ((xrest + y₁) + yrest) =⟨ (Field.addComm F' xrest y₁) under (λ t → x₁ + (t + yrest)) ⟩
                           x₁ + ((y₁ + xrest) + yrest) =⟨ =sym (Field.addAssoc F' y₁ xrest yrest) under (λ t → x₁ + t) ⟩
                           x₁ + (y₁ + (xrest + yrest)) =⟨ sum-join (λ i → xs (suc i)) (λ i → ys (suc i)) under (λ t → x₁ + (y₁ + t)) ⟩
                           x₁ + (y₁ + x+yrest)         =⟨ Field.addAssoc F' x₁ y₁ x+yrest ⟩
                           (x₁ + y₁) + x+yrest □=
                               where x₁ = xs fzero
                                     y₁ = ys fzero
                                     xrest = sum (λ i → xs (suc i))
                                     yrest = sum (λ i → ys (suc i))
                                     x+yrest = sum (λ i → xs (suc i) + ys (suc i))


sum-swap : {n m : ℕ} → (xss : Fin n → Fin m → F) → sum (λ i → sum (xss i)) ≡ sum (λ j → sum (λ i → xss i j))
sum-swap {nzero} {m}  xss = =sym (sum-zero {m})
sum-swap {suc n} {m} xss = sum (xss fzero) + sum (λ i → sum (xss (suc i)))          =⟨ sum-swap (λ i j → xss (suc i) j) under (λ t → sum (xss fzero) + t) ⟩
                             sum (xss fzero) + sum (λ j → sum (λ i → xss (suc i) j))  =⟨ sum-join (xss fzero) (λ j → sum (λ i → xss (suc i) j)) ⟩
                             sum (λ j → (xss fzero j) + sum (λ i → (xss (suc i) j))) □=



sum-LDist : {n : ℕ} → (x : F) → (ys : Fin n → F) → x * sum ys ≡ sum (λ i → x * (ys i))
sum-LDist {nzero}  x _  = zero-RAbsorb x
sum-LDist {suc n} x ys = x * (ys fzero + sum (λ i → ys (suc i)))     =⟨ Field.LDist F' x (ys fzero) (sum (λ i → ys (suc i))) ⟩
                           x * (ys fzero) + x * sum (λ i → ys (suc i)) =⟨ sum-LDist x (λ i → ys (suc i)) under (λ t → x * (ys fzero) + t) ⟩
                           x * (ys fzero) + sum (λ i → x * ys (suc i)) □=


sum-RDist : {n : ℕ} → (xs : Fin n → F) → (y : F) → sum xs * y ≡ sum (λ i → (xs i) * y)
sum-RDist {nzero}  _ y  = zero-LAbsorb y
sum-RDist {suc n} xs y = (xs fzero + sum (λ i → xs (suc i))) * y     =⟨ Field.RDist F' (xs fzero) (sum (λ i → xs (suc i))) y ⟩
                           (xs fzero) * y + sum (λ i → xs (suc i)) * y =⟨ sum-RDist (λ i → xs (suc i)) y under (λ t → (xs fzero) * y + t) ⟩
                           (xs fzero) * y + sum (λ i → xs (suc i) * y) □=




