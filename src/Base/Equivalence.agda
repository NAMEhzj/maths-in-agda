--library=maths


module Base.Equivalence where


open import Relation.Binary.Core public
open import Function public
open import Data.Product public
open import Agda.Primitive
open import Data.Unit
open import Relation.Nullary
open import Data.Nat hiding (_⊔_)


-- I grant myself functional extensionality, makes things way easier and appearently it probably doesen't even lead to a contradiction
postulate ∀≡ : ∀{l k} → {A : Set l} → {B : A → Set k} →
               {f g : (a : A) → B a} → ((x : A) → f x ≡ g x) →
               f ≡ g


infixr 5 _⇔_

record _⇔_ {l k} (A : Set l) (B : Set k) : Set (l ⊔ k) where
   field to   : A → B
         from : B → A

infixr 3 _↔_

record _↔_ {l k} (A : Set l) (B : Set k) : Set (l ⊔ k) where
   field to   : A → B
         from : B → A
         from-to : ∀ a → from (to a) ≡ a
         to-from : ∀ b → to (from b) ≡ b



infixr 3 _=⟨_⟩_

_=⟨_⟩_ : ∀{l} {A : Set l} (x : A) {y z : A} → x ≡ y → y ≡ z → x ≡ z
_=⟨_⟩_  _ refl refl = refl

[_]and[_] : ∀{l₁ l₂} {A : Set l₁} {P : A → Set l₂} {x y : A} →
            x ≡ y → P y → P x
[_]and[_] refl px = px


=sym : ∀{l} → {A : Set l} {x y : A} → x ≡ y → y ≡ x
=sym refl = refl

≠sym : ∀{l} → {A : Set l} {x y : A} → ¬ x ≡ y → ¬ y ≡ x
≠sym x≠y y=x = x≠y (=sym y=x) 


infixr 5 _under_

_under_ : ∀{l k} → {A : Set l} → {B : Set k} → {x y : A} →
          x ≡ y → (f : A → B) → f x ≡ f y
_under_ refl f = refl



infixr 4 _□=

_□= : ∀{l} {A : Set l} → (x : A) → x ≡ x
_□= x = refl  



⇔sym : ∀{l k} {A : Set l} → {B : Set k} → A ⇔ B → B ⇔ A  
⇔sym p = record {to   = _⇔_.from p ;
                 from = _⇔_.to  p }

infixr 4 _□⇔

_□⇔ : ∀{l} (A : Set l) → A ⇔ A
_□⇔ A = record {to      = λ x → x;
                from    = λ x → x}

infixr 3 _⇔⟨_⟩_

_⇔⟨_⟩_ : ∀{l k m} (A : Set l) {B : Set k} → {C : Set m} → A ⇔ B → B ⇔ C → A ⇔ C
_⇔⟨_⟩_ A {B} {C} AisB BisC = record {to   = (_⇔_.to   BisC) ∘ (_⇔_.to   AisB);
                                     from = (_⇔_.from AisB) ∘ (_⇔_.from BisC) }




↔sym : ∀{l k} {A : Set l} → {B : Set k} → A ↔ B → B ↔ A  
↔sym p = record {to      = _↔_.from    p ;
                 from    = _↔_.to      p ;
                 from-to = _↔_.to-from p ;
                 to-from = _↔_.from-to p }

infixr 4 _□↔

_□↔ : ∀{l} (A : Set l) → A ↔ A
_□↔ A = record {to      = λ x → x;
                from    = λ x → x;
                from-to = λ a → refl;
                to-from = λ b → refl}

infixr 3 _↔⟨_⟩_

_↔⟨_⟩_ : ∀{l k m} (A : Set l) {B : Set k} → {C : Set m} → A ↔ B → B ↔ C → A ↔ C
_↔⟨_⟩_ A {B} {C} AisB BisC = record {to      = to₂   ∘ to₁   ;
                                     from    = from₁ ∘ from₂ ;
                                     from-to = λ a → (from₁ ∘ from₂ ∘ to₂ ∘ to₁) a =⟨ from-to₂ (to₁ a) under from₁ ⟩
                                                      from₁ (to₁ a)                =⟨ from-to₁ a ⟩
                                                      a □= ;
                                      to-from = λ c → (to₂ ∘ to₁ ∘ from₁ ∘ from₂) c =⟨ to-from₁ (from₂ c) under to₂ ⟩
                                                       to₂ (from₂ c)                =⟨ to-from₂ c ⟩
                                                       c □= } where
                                        to₁      = _↔_.to AisB
                                        to₂      = _↔_.to BisC
                                        from₁    = _↔_.from AisB
                                        from₂    = _↔_.from BisC
                                        from-to₁ = _↔_.from-to AisB
                                        from-to₂ = _↔_.from-to BisC
                                        to-from₁ = _↔_.to-from AisB
                                        to-from₂ = _↔_.to-from BisC




axiom-k : ∀{l} {A : Set l} → {x y : A} → {eq₁ eq₂ : x ≡ y} → eq₁ ≡ eq₂
axiom-k {eq₁ = refl} {refl} = refl


sametype : ∀{l} → {A B : Set l} → A ≡ B → A → B
sametype refl x = x


_≚_[_] : ∀{l} → {A : Set l} → {B : Set l} → A → B → A ≡ B → Set l
_≚_[_] {l} {A} {.A} x y refl = x ≡ y

subst : ∀{a b} → {A : Set a} → (B : A → Set b) → {x y : A} → x ≡ y → B x → B y
subst B refl r = r 


Σ-≡-intro :
  ∀ {α β}{A : Set α}{B : A → Set β}{a a' : A}{b : B a}{b' : B a'}
  → (Σ (a ≡ a') λ p → subst B p b ≡ b') → (a , b) ≡ (a' , b')
Σ-≡-intro (refl , refl) = refl


Σ-≡-elim :
  ∀ {α β}{A : Set α}{B : A → Set β}{a a' : A}{b : B a}{b' : B a'}
  → (a , b) ≡ (a' , b') → Σ (a ≡ a') λ p → subst B p b ≡ b'
Σ-≡-elim refl = refl , refl


×-≡-intro : ∀{α β} {A : Set α} {B : Set β} {a a' : A} {b b' : B} →
            a ≡ a' × b ≡ b' → (a , b) ≡ (a' , b')
×-≡-intro (refl , refl) = refl

×-≡-elim : ∀{α β} {A : Set α} {B : Set β} {a a' : A} {b b' : B} →
           (a , b) ≡ (a' , b') → a ≡ a' × b ≡ b'
×-≡-elim refl = refl , refl
