--library=maths

module Base.PropTruncation where

open import Relation.Binary.Core
open import Agda.Primitive
open import Data.Product
open import Function
open import Data.Unit
open import Data.Nat using (ℕ)
open import Level


open import Base.Equivalence
open import Base.Factorization

{-
record Truncation {l} (A : Set l) : Set (lsuc l) where
             field
              ∥A∥ : Set l
              to : A → ∥A∥
              from : ∥A∥ → A
              unique : (a a' : ∥A∥) → a ≡ a'

open Truncation

postulate
  defaultTruncation : ∀{l} → (A : Set l) → Truncation A

∥_∥' : ∀{l} (A : Set l) → Set l
∥ A ∥' = ∥A∥ (defaultTruncation A)

∣_∣' : ∀{l} {A : Set l} → A → ∥ A ∥'
∣_∣' {A = A} = to (defaultTruncation A)

∣_∣⁻¹ : ∀{l} {A : Set l} → ∥ A ∥' → A
∣_∣⁻¹ {A = A} = from (defaultTruncation A)

isTrunc' : ∀{l} {A : Set l} → (a a' : ∥ A ∥') → a ≡ a'
isTrunc' {A = A} = unique (defaultTruncation A)

truncate-cong : ∀{l} {A : Set l} → (a : ∥ A ∥' ) → ∣ ∣ a ∣⁻¹ ∣' ≡ a
truncate-cong a = isTrunc' ∣ ∣ a ∣⁻¹ ∣' a

-}



allRel : ∀{a} → (A : Set a) → Rel A Level.zero  
allRel _ x y = ⊤
allRelEq : ∀{a} {A : Set a} → IsEquivalence (allRel A)
allRelEq = record { refl  = tt ;
                    sym   = λ x~y → tt ;
                    trans = λ x~y y~z → tt }

∥_∥ : ∀{a} (A : Set a) → Set a
∥ A ∥ = factorize A (allRel A) allRelEq

∣_∣ : ∀{a} {A : Set a} → A → ∥ A ∥
∣_∣ = factormap  


∥_∥' : ∀{a b} {A : Set a} → (A → Set b) → A → Set b
∥_∥' P x = ∥ P x ∥   



liftToTrunc : ∀{a b} → {A : Set a} → {B : Set b} → (f : A → B) → ((x y : A) → f x ≡ f y) → ∥ A ∥ → B
liftToTrunc f f-cong = liftToFactor f (λ x y x≈y → f-cong x y)

liftToTrunc-cong : ∀{a b} → {A : Set a} → {B : Set b} → (f : A → B) → (f-cong : (x y : A) → f x ≡ f y)
                     → (x : A) → liftToTrunc f f-cong ∣ x ∣ ≡ f x
liftToTrunc-cong f f-cong x = lift-cong f (λ x y x≈y → f-cong x y) under (λ f → f x)

liftToTrunc2 : ∀{a b c} → {A : Set a} → {B : Set b} → {C : Set c} → (f : A → B → C) → ((x1 x2 : A) → (y1 y2 : B) → (f x1 y1) ≡ (f x2 y2))
                                      → ∥ A ∥ → ∥ B ∥ → C
liftToTrunc2  {A = A} {B} {C} f f-cong = liftToTrunc f1 f1-cong
                              where f1 : A → ∥ B ∥ → C
                                    f1 x = liftToTrunc (f x) (f-cong x x)
                                    f1-cong : (x1 x2 : A) → (f1 x1) ≡ (f1 x2)
                                    f1-cong x1 x2 = lift-proof-indep (f x1) (f x2) (∀≡ λ y → f-cong x1 x2 y y)



isTrunc : ∀{a} {A : Set a} → (x* y* : ∥ A ∥) → x* ≡ y*
isTrunc {A = A} x* y* = x*     =⟨ refl ⟩
                         f* y*  =⟨ (lift-unique f* id eq) under (λ h → h y*) ⟩
                         id y*  □=
          where f* : ∥ A ∥ → ∥ A ∥
                f* z* = x*
                p : A → ∥ A ∥
                p = factormap
                eqDeep : (x : A) → f* (p x) ≡ p x
                eqDeep x = f* (p x)  =⟨ refl ⟩
                           id x*     =⟨ (lift-unique id g* eq') under (λ h → h x*) ⟩ 
                           g* x*     =⟨ refl ⟩
                           p x □=
                    where g* : ∥ A ∥ → ∥ A ∥
                          g* z* = p x
                          eq' : id ∘ p ≡ g* ∘ p 
                          eq' = ∀≡ (λ y → id (p y) =⟨ refl ⟩
                                          p y      =⟨ factmap-cong y x tt ⟩
                                          p x      =⟨ refl ⟩
                                          g* (p y) □=)
                
                eq : f* ∘ p ≡ id ∘ p
                eq = ∀≡ eqDeep
                



liftToTrunc* : ∀{a b} → {A : Set a} → {B : Set b} → (f : A → ∥ B ∥) → ∥ A ∥ → ∥ B ∥
liftToTrunc* f = liftToFactor f (λ x y _ → isTrunc (f x) (f y))


liftToTrunc2* : ∀{a b c} → {A : Set a} → {B : Set b} → {C : Set c} → (f : A → B → ∥ C ∥) → ∥ A ∥ → ∥ B ∥ → ∥ C ∥
liftToTrunc2* f = liftToTrunc2 f (λ x1 x2 y1 y2 → isTrunc (f x1 y1) (f x2 y2))


-- this uses axiom K!
getEq : ∀{a} → {A : Set a} → {x y : A} → ∥ x ≡ y ∥ → x ≡ y
getEq {x = x} {y = y} = liftToTrunc id eq-ception
                           where eq-ception : (eq1 eq2 : x ≡ y) → eq1 ≡ eq2
                                 eq-ception refl refl = refl




proof-lift : ∀{a b r} → {A : Set a} → {_≈_ : Rel A r} → {eqr : IsEquivalence _≈_} → (B : factorize A _≈_ eqr → Set b)
                       → ((x : A) → ∥ B (factormap x) ∥) → (x* : factorize A _≈_ eqr) → ∥ B x* ∥
proof-lift {A = A} {_≈_} {eqr}B f x* = sametype (lift-unique (proj₁ ∘ f'*) id comp-same under (λ h → factorize (B (h x*)) (λ x y → ⊤) allRelEq)) (proj₂ (f'* x*))
                          where A/≈ = factorize A _≈_ eqr
                                f' : A → Σ A/≈ (λ z* → ∥ B z* ∥)
                                f' x = (factormap x , f x)
                                f'-cong : (x y : A) → x ≈ y → f' x ≡ f' y
                                f'-cong x y x≈y = Σ-≡-intro (tEq , isTrunc (subst (λ z* → ∥ B z* ∥) tEq (f x)) (f y))
                                               where tEq = factmap-cong {eqr = eqr} x y x≈y 
                                f'* : A/≈ → Σ A/≈ (λ z* → ∥ B z* ∥)
                                f'* = liftToFactor {eqr = eqr} f' f'-cong
                                comp-same : proj₁ ∘ f'* ∘ factormap ≡ id ∘ factormap
                                comp-same = ∀≡ (λ x → proj₁ ((f'* ∘ factormap) x)  =⟨ lift-cong f' f'-cong under (λ t → proj₁ (t x)) ⟩
                                                      proj₁ (f' x)                 =⟨ refl ⟩
                                                      factormap x □=)

-- this is still to do, but I'm too lazy right now, so I'm gonna just postulate it
postulate 
 proof-lift2 : ∀{a b r} → {A : Set a} → {_≈_ : Rel A r} → {eqr : IsEquivalence _≈_} → (B : factorize A _≈_ eqr → factorize A _≈_ eqr → Set b)
                       → ((x y : A) → ∥ B (factormap x) (factormap y) ∥) → (x* y* : factorize A _≈_ eqr) → ∥ B x* y* ∥ 
 proof-lift3 : ∀{a b r} → {A : Set a} → {_≈_ : Rel A r} → {eqr : IsEquivalence _≈_} → (B : factorize A _≈_ eqr → factorize A _≈_ eqr → factorize A _≈_ eqr → Set b)
                       → ((x y z : A) → ∥ B (factormap x) (factormap y) (factormap z) ∥) → (x* y* z* : factorize A _≈_ eqr) → ∥ B x* y* z* ∥ 
 
