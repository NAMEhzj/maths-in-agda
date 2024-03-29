{-# OPTIONS --allow-unsolved-metas #-}
open import Relation.Binary.Core
open import Relation.Unary as U
open import Relation.Nullary
open import Base.Equivalence
open import Data.Nat
open import Data.Fin hiding (_≤_ ; _<_ ; _+_) renaming (zero to fzero ; suc to fsuc)
open import Data.Empty
open import Data.Sum
open import Data.Product

module NatAndFin where



nothingSmallerThan0 : {n : ℕ} → n < zero → ⊥
nothingSmallerThan0 ()


n≤n : (n : ℕ) → n ≤ n
n≤n zero    = z≤n
n≤n (suc n) = s≤s (n≤n n)


eq-≤-cong : (k n m : ℕ) → k ≡ n → n ≤ m → k ≤ m
eq-≤-cong k .k m refl k≤m = k≤m


≤-eq-cong : (k n m : ℕ) → k ≡ n → m ≤ n → m ≤ k
≤-eq-cong k .k m refl m≤k = m≤k 

lessOrEqual : (i j : ℕ) → i ≤ j → i < j ⊎ i ≡ j
lessOrEqual zero zero    z≤n = inj₂ refl
lessOrEqual zero (suc j) z≤n = inj₁ (s≤s z≤n)
lessOrEqual (suc i) (suc j) (s≤s i≤j) with lessOrEqual i j i≤j
... | (inj₁ i<j)  = inj₁ (s≤s i<j)
... | (inj₂ refl) = inj₂ refl


biggerIsNotEqual : (i j : ℕ) → i < j → ¬ i ≡ j
biggerIsNotEqual zero zero ()
biggerIsNotEqual (suc i) zero ()
biggerIsNotEqual (zero) (suc i) _ ()
biggerIsNotEqual (suc i) (suc j) (s≤s i<j) i+1=j+1 = biggerIsNotEqual i j i<j (suc-inj i+1=j+1) 
                               where suc-inj : {a b : ℕ} → suc a ≡ suc b → a ≡ b
                                     suc-inj refl = refl



toℕ-backwards : {n : ℕ} → (i j : Fin n) → ¬ toℕ i ≡  toℕ j → ¬ i ≡ j
toℕ-backwards i j i'≠j' i=j = i'≠j' (i=j under toℕ)


toℕ-injective : {n : ℕ} → (i j : Fin n) → toℕ i ≡ toℕ j → i ≡ j
toℕ-injective fzero fzero refl        = refl
toℕ-injective fzero (fsuc j) ()
toℕ-injective (fsuc i) fzero () 
toℕ-injective (fsuc i) (fsuc j) i+1=j+1 = toℕ-injective i j (suc-inj i+1=j+1) under fsuc
                              where suc-inj : {a b : ℕ} → suc a ≡ suc b → a ≡ b
                                    suc-inj refl = refl
                                            


isInFin : (p n : ℕ) → n ≤ p ⊎ Σ (Fin n) (λ i → toℕ i ≡ p)
isInFin p    zero       = inj₁ z≤n
isInFin zero (suc n)    = inj₂ (fzero , refl)
isInFin (suc p) (suc n) with (isInFin p n)
... | (inj₁ n≤p)       = inj₁ (s≤s n≤p)
... | (inj₂ (i , i↦p)) = inj₂ (fsuc i , i↦p under suc)


fup : {n : ℕ} → Fin n → Fin (suc n)
fup fzero    = fzero
fup (fsuc i) = fsuc (fup i)

fdown : {n : ℕ} → (i : Fin (suc n)) → toℕ i < n → Fin n
fdown fzero (s≤s _)      = fzero
fdown (fsuc i) (s≤s i<n) = fsuc (fdown i i<n) 

-- vectors

emptyVec : ∀{l} {A : Set l} → Fin ℕ.zero → A
emptyVec ()


tail : ∀{l} {n : ℕ} {A : Set l} → (Fin (suc n) → A) → Fin n → A
tail as i = as (fsuc i)


consVec : ∀{l} {A : Set l} {n : ℕ} → A → ((Fin n) → A) → Fin (suc n) → A
consVec a as fzero   = a
consVec a as (fsuc i) = as i


appendVec : ∀{l} {A : Set l} {n : ℕ} → A → ((Fin n) → A) → Fin (suc n) → A
appendVec {n = zero} a _ fzero     = a
appendVec {n = zero} _ _ (fsuc i)   = ⊥-elim (stupid i)
                             where stupid : Fin zero → ⊥
                                   stupid ()
appendVec {n = suc n} a as fzero   = as fzero
appendVec {n = suc n} a as (fsuc i) = appendVec a (tail as) i


sortVec : ∀{l₁ l₂} {A : Set l₁} {n : ℕ} (P : A → Set l₂) → U.Decidable P → (Fin n → A) → (Fin n → A)
sortVec {n = zero} P decP xs = xs
sortVec {n = suc n} P decP xs with (decP (xs fzero))
... | (yes _) = consVec (xs fzero) (sortVec P decP (tail xs))
... | (no  _) = appendVec (xs fzero) (sortVec P decP (tail xs))


sortVecThreshold : ∀{l₁ l₂} {A : Set l₁} {n : ℕ} (P : A → Set l₂) → U.Decidable P → (Fin n → A) → ℕ
sortVecThreshold {n = zero} P decP xs = zero
sortVecThreshold {n = suc n} P decP xs with (decP (xs fzero))
... | (yes _) = suc (sortVecThreshold P decP (tail xs))
... | (no  _) = sortVecThreshold P decP (tail xs)

{-
underThreshold : ∀{l₁ l₂} {A : Set l₁} {n : ℕ} (P : A → Set l₂) → (decP : U.Decidable P) → (xs : (Fin n → A))
                              → (i : Fin n) → toℕ i < (sortVecThreshold P decP xs) → P (sortVec P decP xs i)
underThreshold {n = zero} P decP xs ()
underThreshold {n = suc zero} P decP xs fzero 1≤t with (decP (xs fzero))
... | (yes Px0) = Px0
... | (no  _  ) = ⊥-elim (1≰0 1≤t)
              where 1≰0 : (suc zero) ≤ zero → ⊥
                    1≰0 ()
underThreshold {n = suc (suc n)} P decP xs fzero 1≤t with (decP (xs fzero))
... | (yes Px0) = Px0
... | (no  _  ) = underThreshold P decP (tail xs) fzero 1≤t
underThreshold {n = suc n} P decP xs (fsuc i) i+2≤t with (decP (xs fzero))
... | (no  _)  = {!!}
... | (yes _) with i+2≤t 
...    | (s≤s i+1≤t') = underThreshold P decP (tail xs) i i+1≤t'
-}


concatVec : ∀{l} {A : Set l} {m n : ℕ} → (Fin m → A) × (Fin n → A) → (Fin (m + n) → A)
concatVec {m = zero} (xs , ys)  = ys
concatVec {m = suc m} (xs , ys) fzero   = xs fzero
concatVec {m = suc m} (xs , ys) (fsuc i) = (concatVec (tail xs , ys)) i


concat-prop-cong : ∀{l₁ l₂} {A : Set l₁} {m n : ℕ} → (xs : Fin m → A) → (ys : Fin n → A) → (P : A → Set l₂)
             → ((i : Fin m) → P (xs i)) → ((i : Fin n) → P (ys i)) → (i : Fin (m + n)) → P ((concatVec (xs , ys)) i)
concat-prop-cong {m = zero} xs ys P Pxs Pys i         = Pys i
concat-prop-cong {m = suc m} xs ys P Pxs Pys fzero    = Pxs fzero
concat-prop-cong {m = suc m} xs ys P Pxs Pys (fsuc i) = concat-prop-cong (tail xs) ys P (λ j → Pxs (fsuc j)) Pys i


 
splitVec : ∀{l} {A : Set l} {m n : ℕ} → (Fin (m + n) → A) → (Fin m → A) × (Fin n → A)
splitVec {m = zero} zs = ( emptyVec , zs )
splitVec {A = A} {m = suc m} zs with (splitVec {m = m} (λ i → zs (fsuc i)))
... | ( xs' , ys ) = ( xs , ys )
                   where xs : Fin (suc m) → A
                         xs fzero   = zs fzero
                         xs (fsuc i) = xs' i

splitPoint : ∀{l} {A : Set l} {m n : ℕ} → (i : Fin (m + (suc n))) → toℕ i ≡ m → (as : Fin (m + (suc n)) → A) → (proj₂ (splitVec {m = m} as)) fzero ≡ as i
splitPoint {m = zero}  fzero refl as = refl
splitPoint {m = zero} (fsuc i) ()
splitPoint {m = suc m} (fsuc i) i↦m as = splitPoint {m = m} i (shrink i↦m) (tail as)
         where shrink : {n m : ℕ} {i : Fin n} → toℕ (fsuc i) ≡ suc m → toℕ i ≡ m
               shrink {m = zero} {i = fzero} refl = refl
               shrink {m = suc m} {i = fsuc i} refl = refl
               shrink {m = zero} {i = fsuc i} ()
               shrink {m = suc m} {i = fzero} ()
splitPoint {m = suc m} fzero ()

split-concat-cong : ∀{l} {A : Set l} {m n : ℕ} (zs : Fin (m Data.Nat.+ n) → A) → (i : Fin (m Data.Nat.+ n)) → concatVec (splitVec {m = m} {n = n} zs) i ≡ zs i 
split-concat-cong {m = ℕ.zero} zs _ = refl
split-concat-cong {m = ℕ.suc m} zs fzero = refl
split-concat-cong {m = ℕ.suc m} zs (fsuc i) = split-concat-cong {m = m} (tail zs) i
 


+-suc-cong : (n m : ℕ) → n + (suc m) ≡ suc (n + m)
+-suc-cong zero m    = refl
+-suc-cong (suc n) m = (+-suc-cong n m) under suc

n-minus-fin : (n : ℕ) → (j : Fin n) → Σ ℕ (λ k → (toℕ j) + (suc k) ≡ n)
n-minus-fin (suc n) fzero    = (n , refl)
n-minus-fin (suc n) (fsuc j) with (n-minus-fin n j)
... | (k , j+k+1=n) = (k , j+k+1=n under suc)

sameFin : (n m : ℕ) → m ≡ n → Fin n → Fin m
sameFin n m refl i = i
