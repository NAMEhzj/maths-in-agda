--library=maths


open import Agda.Primitive

open import Base.Equivalence
open import Base.PropTruncation

module Base.Sets where


record 𝒫 {a} (A : Set a) {b} : Set (a ⊔ (lsuc b)) where
               field U : Set b
                     i : U → A
                     injective : (x y : U) → i x ≡ i y → x ≡ y


open 𝒫


propSubset : ∀{l m} {A : Set l} → (P : (a : A) → Set m) → 𝒫 A {l ⊔ m}
U (propSubset {A = A} P) = Σ A ∥ P ∥'
i (propSubset P) (a , _) = a
injective (propSubset P) (a , eq₁) (b , eq₂) a=b with eq₁
...                               | eq rewrite a=b = Σ-≡-intro (refl , isTrunc eq eq₂)



wholeSet : ∀{a} (A : Set a) → 𝒫 A
U (wholeSet A) = A
i (wholeSet A) x = x
injective (wholeSet A) x .x refl = refl


infix 6 _∈_ 

_∈_ : ∀{a b} → {A : Set a} → A → 𝒫 A {b} → Set (a ⊔ b) 
_∈_ x S = Σ (U S) (λ u → i S u ≡ x)


propSubset-to∈ : ∀{l m} {A : Set l} {P : (a : A) → Set m} → {a : A} → P a → a ∈ (propSubset P)
propSubset-to∈ {a = a} Pa = (a , ∣ Pa ∣) , refl 

propSubset-from∈ : ∀{l m} {A : Set l} {P : (a : A) → Set m} → {a : A} → a ∈ (propSubset P) → ∥ P a ∥
propSubset-from∈  {A = A} {P} {a} ((.a , ∣Pa∣) , refl) = ∣Pa∣


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


