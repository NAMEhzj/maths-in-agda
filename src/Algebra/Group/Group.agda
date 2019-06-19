--library=maths-library

open import Base.Equivalence hiding (_∘_)

module Algebra.Group.Group where

record Group {a} (A : Set a) : Set a where
         infixr 8 _∘_
         infix 9 _⁻¹
         field
           _∘_   : A → A → A
           e     : A
           _⁻¹   : A → A
           Assoc : (x y z : A) → (x ∘ y) ∘ z ≡ x ∘ (y ∘ z)
           LNeut : (x : A) → e ∘ x ≡ x
           RNeut : (x : A) → x ∘ e ≡ x
           LInv  : (x : A) → x ⁻¹ ∘ x ≡ e
           RInv  : (x : A) → x ∘ x ⁻¹ ≡ e
         
         


record Semigroup {a} (A : Set a) : Set a where
         field
           _∘_   : A → A → A
           Assoc : (x y z : A) → (x ∘ y) ∘ z ≡ x ∘ (y ∘ z) 


record Monoid {a} (A : Set a) : Set a where
         field
           _∘_   : A → A → A
           e     : A
           Assoc : (x y z : A) → (x ∘ y) ∘ z ≡ x ∘ (y ∘ z)
           LNeut : (x : A) → e ∘ x ≡ x
           RNeut : (x : A) → x ∘ e ≡ x




GroupToMonoid : ∀{a} → {A : Set a} → Group A → Monoid A
GroupToMonoid G = record { _∘_   = Group._∘_ G ;
                           e     = Group.e G ;
                           Assoc = Group.Assoc G ;
                           LNeut = Group.LNeut G ;
                           RNeut = Group.RNeut G }


MonoidToSemigroup : ∀{a} → {A : Set a} → Monoid A → Semigroup A
MonoidToSemigroup M = record { _∘_   = Monoid._∘_ M ;
                               Assoc = Monoid.Assoc M }


GroupToSemigroup : ∀{a} → {A : Set a} → Group A → Semigroup A
GroupToSemigroup G = record { _∘_   = Group._∘_ G ;
                              Assoc = Group.Assoc G }
