--library=maths


open import Agda.Primitive

open import Base.Equivalence
open import Base.PropTruncation
open import Data.Unit

module Base.Sets where


record 𝒫 {a} (A : Set a) {b} : Set (a ⊔ (lsuc b)) where
               field elem : A → Set b
                     unique : (x : A) → (p1 p2 : elem x) → p1 ≡ p2


open 𝒫


propSubset : ∀{l m} {A : Set l} → (P : (a : A) → Set m) → 𝒫 A {m}
elem (propSubset P)   = ∥ P ∥'
unique (propSubset P) x = isTrunc 



wholeSet : ∀{a} (A : Set a) → 𝒫 A {lzero}
elem (wholeSet A) x = ⊤
unique (wholeSet A) x tt tt = refl


infix 6 _∈_ 

_∈_ : ∀{a b} → {A : Set a} → A → 𝒫 A {b} → Set b 
_∈_ x S = elem S x


_⊆_ : ∀{a b c} → {A : Set a}  → 𝒫 A {b} → 𝒫 A {c} → Set (a ⊔ b ⊔ c)
_⊆_ {A = A} U₁ U₂ = (x : A) → x ∈ U₁ → x ∈ U₂


_⊇_ : ∀{a b c} → {A : Set a}  → 𝒫 A {b} → 𝒫 A {c} → Set (a ⊔ b ⊔ c)
_⊇_ U₁ U₂ = U₂ ⊆ U₁


_⋍_ : ∀{a b c} → {A : Set a}  → 𝒫 A {b} → 𝒫 A {c} → Set (a ⊔ b ⊔ c)
_⋍_ U₁ U₂ = U₁ ⊆ U₂ × U₁ ⊇ U₂


_□⊆ : ∀{a b} → {A : Set a} → (U : 𝒫 A {b}) → U ⊆ U
_□⊆ _ _ x∈U = x∈U

_⊆⟨_⟩_ : ∀{a b c d} → {A : Set a} → (U₁ : 𝒫 A {b}) → {U₂ : 𝒫 A {c}} → {U₃ : 𝒫 A {d}} → U₁ ⊆ U₂ → U₂ ⊆ U₃ → U₁ ⊆ U₃
_⊆⟨_⟩_ _ U₁⊆U₂ U₂⊆U₃ x x∈U₁ = U₂⊆U₃ x (U₁⊆U₂ x x∈U₁)

_□⋍ : ∀{a b} → {A : Set a} → (U : 𝒫 A {b}) → U ⋍ U
_□⋍ _ = (λ x x∈U → x∈U) , (λ x x∈U → x∈U) 

_⋍⟨_⟩_ : ∀{a b c d} → {A : Set a} → (U₁ : 𝒫 A {b}) → {U₂ : 𝒫 A {c}} → {U₃ : 𝒫 A {d}} → U₁ ⋍ U₂ → U₂ ⋍ U₃ → U₁ ⋍ U₃
_⋍⟨_⟩_ _ (U₁⊆U₂ , U₁⊇U₂) (U₂⊆U₃ , U₂⊇U₃) = (λ x x∈U₁ → U₂⊆U₃ x (U₁⊆U₂ x x∈U₁)) , (λ x x∈U₃ → U₁⊇U₂ x (U₂⊇U₃ x x∈U₃))



