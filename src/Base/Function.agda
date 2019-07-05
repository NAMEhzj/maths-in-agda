open import Agda.Primitive 
open import Base.Equivalence

module Base.Function where

injective : ∀{l m} {A : Set l} {B : Set m} → (A → B) → Set (l ⊔ m)
injective {A = A} f = (x y : A) → f x ≡ f y → x ≡ y 

injectiveIsProp : ∀{l m} {A : Set l} {B : Set m} → (f : A → B) → (i1 i2 : injective f) → i1 ≡ i2
injectiveIsProp {A = A} f i1 i2 = ∀≡ (λ x → ∀≡ (λ y → ∀≡ λ _ → axiom-k))


surjective : ∀{l m} {A : Set l} {B : Set m} → (A → B) → Set (l ⊔ m)
surjective {A = A} {B} f = (w : B) → Σ A (λ x → f x ≡ w)


bijective : ∀{l m} {A : Set l} {B : Set m} → (A → B) → Set (l ⊔ m)
bijective f = injective f × surjective f

bijectiveIsProp : ∀{l m} {A : Set l} {B : Set m} → (f : A → B) → (b1 b2 : bijective f) → b1 ≡ b2
bijectiveIsProp {B = B} f (i1 , s1)  (i2 , s2) = ×-≡-intro (injectiveIsProp f i1 i2 , surj-eq) where
                                            pointWise-eq : (w : B) → s1 w ≡ s2 w
                                            pointWise-eq w = Σ-≡-intro (i1 x y fx=fy , axiom-k) where
                                               x = proj₁ (s1 w)
                                               y = proj₁ (s2 w)
                                               fx=fy : f x ≡ f y
                                               fx=fy = f x =⟨ proj₂ (s1 w) ⟩
                                                       w   =⟨ =sym (proj₂ (s2 w)) ⟩
                                                       f y □=
                                            surj-eq : s1 ≡ s2
                                            surj-eq = ∀≡ pointWise-eq

inverseOf : ∀{l m} {A : Set l} {B : Set m} → (A → B) → (B → A) → Set (l ⊔ m)
inverseOf f g = f ∘ g ≡ id × g ∘ f ≡ id

inverse-unique : ∀{l m} {A : Set l} {B : Set m} → (f : A → B) → (g1 g2 : B → A) → inverseOf f g1 → inverseOf f g2 → g1 ≡ g2
inverse-unique f g1 g2 g1inv g2inv = ∀≡ λ w → g1 w          =⟨ =sym (proj₂ g2inv) under (λ h → h (g1 w)) ⟩
                                              g2 (f (g1 w)) =⟨ proj₁ g1inv under (λ h → g2 (h w)) ⟩
                                              g2 w □=


invertible : ∀{l m} {A : Set l} {B : Set m} → (A → B) → Set (l ⊔ m)
invertible {A = A} {B} f = Σ (B → A) (inverseOf f)

invertibleIsProp : ∀{l m} {A : Set l} {B : Set m} → (f : A → B) → (in1 in2 : invertible f) → in1 ≡ in2
invertibleIsProp f in1 in2 = Σ-≡-intro (inverse-unique f (proj₁ in1) (proj₁ in2) (proj₂ in1) (proj₂ in2) , ×-≡-intro (axiom-k , axiom-k))


open _↔_

bijectiveIsInvertible : ∀{l m} {A : Set l} {B : Set m} → (f : A → B) → bijective f ↔ invertible f
to (bijectiveIsInvertible {A = A} {B} f) (inj , surj) = (g , (f∘g=id , g∘f=id)) where
                                      g : B → A
                                      g w = proj₁ (surj w)
                                      f∘g=id : f ∘ g ≡ id
                                      f∘g=id = ∀≡ λ w → f (g w) =⟨ proj₂ (surj w) ⟩
                                                        w       □=
                                      g∘f=id : g ∘ f ≡ id
                                      g∘f=id = ∀≡ λ x → inj (g (f x)) x
                                                           (f (g (f x)) =⟨ f∘g=id under (λ h → h (f x)) ⟩
                                                           f x □=)
                                      
from (bijectiveIsInvertible f) (g , (f∘g=id , g∘f=id)) = (inj , surj) where
                                     inj : injective f
                                     inj x y fx=fy = x       =⟨ =sym g∘f=id under (λ h → h x) ⟩
                                                     g (f x) =⟨ fx=fy under g ⟩
                                                     g (f y) =⟨ g∘f=id under (λ h → h y) ⟩
                                                     y □=
                                     surj : surjective f
                                     surj w = g w , f∘g=id under (λ h → h w)
to-from (bijectiveIsInvertible f) inv = invertibleIsProp f (to (bijectiveIsInvertible f) (from (bijectiveIsInvertible f) inv)) inv
from-to (bijectiveIsInvertible f) bij = bijectiveIsProp f (from (bijectiveIsInvertible f) (to (bijectiveIsInvertible f) bij)) bij
