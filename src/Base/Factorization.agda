--library=maths

--from stdlib
open import Relation.Binary.Core
open import Data.Product
open import Function
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin ; zero ; suc)
open import Level using ( _⊔_ ) renaming (suc to lsuc)

--from maths
open import Base.Equivalence


module Base.Factorization where


postulate
-- a function mapping any set A with an equivalence relation ≈ to the factor set A/≈
  factorize : ∀{a r} → (A : Set a) → (R : Rel A r) → IsEquivalence R → Set (a ⊔ r)
-- a funtion from A to A/≈, mapping each point to its class
  factormap : ∀{a r} → {A : Set a} → {R : Rel A r} → {eqr : IsEquivalence R} → A → factorize A R eqr
-- the factormap maps related elements to the same class
  factmap-cong : ∀{a r} → {A : Set a} → {_≈_ : Rel A r} → {eqr : IsEquivalence _≈_} → (x y : A) → x ≈ y
                          → factormap {eqr = eqr} x ≡ factormap y
-- for any set C, a map f : A → C that maps related elements to the same value can be lifted to a map f' : A/≈ → C
  liftToFactor : ∀{a b r} → {A : Set a} → {_≈_ : Rel A r} → {eqr : IsEquivalence _≈_} → {B : Set b}
                    → (f : A → B) → ((x y : A) → x ≈ y → f x ≡ f y) → factorize A _≈_ eqr → B
-- let p be the projection from A to A/≈, then with f' as above the following holds: ∀ x ∈ A. f' (p x) = f x
  lift-cong : ∀{a b r} → {A : Set a} → {_≈_ : Rel A r} → {eqr : IsEquivalence _≈_} → {B : Set b} → (f : A → B)
                 → (f-cong : (x y : A) → x ≈ y → f x ≡ f y) → (liftToFactor {eqr = eqr} f f-cong) ∘ factormap ≡ f
-- uniqueness of the lift <=> factormap is epimorphism (surjective)
  lift-unique : ∀{a b r} → {A : Set a} → {_≈_ : Rel A r} → {eqr : IsEquivalence _≈_} → {B : Set b}
                 → (g* h* : factorize A _≈_ eqr → B) → g* ∘ factormap ≡ h* ∘ factormap → g* ≡ h*

lift-proof-indep : ∀{a b r} → {A : Set a} → {_≈_ : Rel A r} → {eqr : IsEquivalence _≈_} → {B : Set b} → (f g : A → B)
                        → {f-cong : (x y : A) → x ≈ y → f x ≡ f y} → {g-cong : (x y : A) → x ≈ y → g x ≡ g y} → f ≡ g → liftToFactor {eqr = eqr} f f-cong ≡ liftToFactor g g-cong

lift-proof-indep {eqr = eqr} f .f {c1} {c2} refl = lift-unique f1* f2*
                                                         (f1* ∘ factormap =⟨ lift-cong f c1 ⟩
                                                          f               =⟨ =sym (lift-cong f c2) ⟩
                                                          f2* ∘ factormap □=)
                                                 where f1* = liftToFactor {eqr = eqr} f c1
                                                       f2* = liftToFactor {eqr = eqr} f c2


liftToFactor2 : ∀{a b r} → {A : Set a} → {_≈_ : Rel A r} → {eqr : IsEquivalence _≈_} → {B : Set b}
                    → (f : A → A → B) → ((x y v w : A) → x ≈ y → v ≈ w → f x v ≡ f y w) → factorize A _≈_ eqr → factorize A _≈_ eqr → B
liftToFactor2 {A = A} {_≈_} {eqr} {B} f f-cong = liftToFactor f1 f1-cong
                      where f-congVar1 : (x : A) → (v w : A) → v ≈ w → f x v ≡ f x w
                            f-congVar1 x v w v≈w = f-cong x x v w (IsEquivalence.refl eqr) v≈w
                            f-congVar2 : (x y : A) → x ≈ y → (f x) ≡ (f y)
                            f-congVar2 x y x≈y = ∀≡ λ v → f-cong x y v v x≈y (IsEquivalence.refl eqr)
                            f1 : A → factorize A _≈_ eqr → B
                            f1 x = liftToFactor (f x) (f-congVar1 x)
                            f1-cong : (x y : A) → x ≈ y → f1 x ≡ f1 y
                            f1-cong x y x≈y = lift-unique (f1 x) (f1 y) ((f1 x) ∘ factormap =⟨ lift-cong (f x) (f-congVar1 x) ⟩
                                                                         f x                =⟨ f-congVar2 x y x≈y ⟩
                                                                         f y                =⟨ =sym (lift-cong (f y) (f-congVar1 y)) ⟩
                                                                         (f1 y) ∘ factormap □= )



lift2-cong :  ∀{a b r} → {A : Set a} → {_≈_ : Rel A r} → {eqr : IsEquivalence _≈_} → {B : Set b} → (f : A → A → B)
                 → (f-cong : (x y v w : A) → x ≈ y → v ≈ w → f x v ≡ f y w) → (x v : A) → liftToFactor2 {eqr = eqr} f f-cong (factormap x) (factormap v) ≡ f x v
lift2-cong {A = A} {_≈_} {eqr} {B} f f-cong x v = f*  x* v*  =⟨ refl ⟩
                                                  f1* x* v*  =⟨ (lift-cong f1 f1-cong) under (λ h → h x v*) ⟩
                                                  f1  x v*   =⟨ lift-cong (f x) (f-congVar1 x) under (λ h → h v)  ⟩
                                                  f x v □=
                     where f-congVar1 : (x : A) → (v w : A) → v ≈ w → f x v ≡ f x w
                           f-congVar1 x v w v≈w = f-cong x x v w (IsEquivalence.refl eqr) v≈w
                           f-congVar2 : (x y : A) → x ≈ y → (f x) ≡ (f y)
                           f-congVar2 x y x≈y = ∀≡ λ v → f-cong x y v v x≈y (IsEquivalence.refl eqr)
                           f1 : A → factorize A _≈_ eqr → B
                           f1 x = liftToFactor (f x) (f-congVar1 x)
                           f1-cong : (x y : A) → x ≈ y → f1 x ≡ f1 y
                           f1-cong x y x≈y = lift-unique (f1 x) (f1 y) ((f1 x) ∘ factormap =⟨ lift-cong (f x) (f-congVar1 x) ⟩
                                                                        f x                =⟨ f-congVar2 x y x≈y ⟩
                                                                        f y                =⟨ =sym (lift-cong (f y) (f-congVar1 y)) ⟩
                                                                        (f1 y) ∘ factormap □= )
                           f* = liftToFactor2 {eqr = eqr} f f-cong
                           f1* = liftToFactor {eqr = eqr} f1 f1-cong
                           x* = factormap {eqr = eqr} x
                           v* = factormap {eqr = eqr} v




liftToFactor3 : ∀{a b r} → {A : Set a} → {_≈_ : Rel A r} → {eqr : IsEquivalence _≈_} → {B : Set b} → 
                    (f : A → A → A → B) → ((x x' y y' z z' : A) → x ≈ x' → y ≈ y' → z ≈ z' → f x y z ≡ f x' y' z') →
                    factorize A _≈_ eqr → factorize A _≈_ eqr → factorize A _≈_ eqr → B
liftToFactor3 {A = A} {_≈_} {eqr} {B} f f-cong = liftToFactor2 f1 f1-cong
                      where f-congVar1 : (x y : A) → (z z' : A) → z ≈ z' → f x y z ≡ f x y z'
                            f-congVar1 x y z z' z≈z' = f-cong x x y y z z' (IsEquivalence.refl eqr) (IsEquivalence.refl eqr) z≈z'
                            f-congVar2 : (x x' y y' : A) → x ≈ x' → y ≈ y' → (f x y) ≡ (f x' y')
                            f-congVar2 x x' y y' x≈x' y≈y' = ∀≡ λ z → f-cong x x' y y' z z x≈x' y≈y' (IsEquivalence.refl eqr)
                            f1 : A → A → factorize A _≈_ eqr → B
                            f1 x y = liftToFactor (f x y) (f-congVar1 x y)
                            f1-cong : (x x' y y' : A) → x ≈ x' → y ≈ y' → f1 x y ≡ f1 x' y'
                            f1-cong x x' y y' x≈x' y≈y' = lift-unique (f1 x y) (f1 x' y')
                                                            ((f1 x y) ∘ factormap =⟨ lift-cong (f x y) (f-congVar1 x y) ⟩
                                                             f x y                =⟨ f-congVar2 x x' y y' x≈x' y≈y' ⟩
                                                             f x' y'              =⟨ =sym (lift-cong (f x' y') (f-congVar1 x' y')) ⟩
                                                             (f1 x' y') ∘ factormap □=)





open Relation.Binary.Core.IsEquivalence renaming (refl to refl')



{-
prodRel : ∀{k l} → {n : ℕ} → (As : Fin n → Set k) → (Rs : (i : Fin n) → Rel (As i) l) → Rel ((i : Fin n) → As i) l
prodRel {n = n} As Rs f g = (i : Fin n) → Rs i (f i) (g i)

prodEqr :  ∀{k l} → {n : ℕ} → (As : Fin n → Set k) → (Rs : (i : Fin n) → Rel (As i) l) →
           (Eqrs : (i : Fin n) → IsEquivalence (Rs i)) → IsEquivalence (prodRel As Rs)
refl' (prodEqr As Rs Eqrs) i = refl' (Eqrs i)
sym (prodEqr As Rs Eqrs) pf i = sym (Eqrs i) (pf i)
trans (prodEqr As Rs Eqrs) pf1 pf2 i = trans (Eqrs i) (pf1 i) (pf2 i)


liftToFactor2' : ∀{a b r} → {A : Set a} → {_≈_ : Rel A r} → {eqr : IsEquivalence _≈_} → {B : Set b}
                    → (f : A → A → B) → ((x y v w : A) → x ≈ y → v ≈ w → f x v ≡ f y w) → factorize A _≈_ eqr → factorize A _≈_ eqr → B
liftToFactor2' {a} {b} {r} {A} {_≈_} {eqr} {B} f f-cong x y = liftToFactor f2 f2-cong {!!}
                                            where AA : Fin 2 → Set a
                                                  AA _ = A
                                                  R2 = prodRel AA (λ _ → _≈_)
                                                  eqr2 = prodEqr AA (λ _ → _≈_) (λ i → eqr)
                                                  f2 : ((i : Fin 2) → AA i) → B
                                                  f2 vw = f (vw zero) (vw (suc zero))
                                                  f2-cong : (uv wz : (i : Fin 2) → AA i) → (R2 uv wz) → f2 uv ≡ f2 wz
                                                  f2-cong uv wz Ruvwz = f-cong (uv zero) (wz zero) (uv (suc zero)) (wz (suc zero))
                                                                        (Ruvwz zero) (Ruvwz (suc zero))
                                                  xy : ((i : Fin 2) → AA i)
                                                  xy zero       = x
                                                  xy (suc zero) = y
                                                                   
-}

-- the same functions as liftToFactor and lift-cong, instead of a constant set C, the target set can depend on the input, but only up to equivalence.
-- one should be able to show the existence of these two just from the simple case by setting C = Σ A/≈ B, but i got confused with all the equalities between equality types
-- so i gave up :/

{-
liftToFactor-dep : ∀{a b r} → {A : Set a} → {_≈_ : Rel A r} → {eqr : IsEquivalence _≈_} → (B : A → Set b) → (B-cong : (x y : A) → x ≈ y → B x ≡ B y) 
                    → (f : (x : A) → B x) → ((x y : A) → (x≈y : x ≈ y) → sametype (B-cong x y x≈y) (f x) ≡ f y) → (x* : factorize A _≈_ eqr) → liftToFactor B B-cong x*
liftToFactor-dep {A = A} {_≈_} {eqr} B B-cong f f-cong x* = {!!}
                                              where A/≈ = factorize A _≈_ eqr
                                                    B* = liftToFactor B B-cong
                                                    Bz=B*z* : (z : A) → B z ≡ B* (factormap z)
                                                    Bz=B*z* z = =sym (lift-cong B B-cong) under (λ g → g z)
                                                    f1 : A → Σ A/≈ B*
                                                    f1 x with (f x)
                                                    ...   | u = (factormap x , sametype (Bz=B*z* x) u)
                                                    f1-cong : (x y : A) → x ≈ y → f1 x ≡ f1 y
                                                    f1-cong x y x≈y with (f x) | (f y)
                                                    ...                | u | v = Σ-≡-intro (factmap-cong x y x≈y , {!!})
                                                    f2 : A/≈ → Σ A/≈ B*
                                                    f2 = {!!}
                                                                 

  lift-cong-dep : ∀{a b r} → {A : Set a} → {_≈_ : Rel A r} → {eqr : IsEquivalence _≈_} → {B : A → Set b} → {B-cong : (x y : A) → x ≈ y → B x ≡ B y}
                     → (f : (x : A) → B x) → (f-cong : (x y : A) → (x≈y : x ≈ y) → sametype (B-cong x y x≈y) (f x) ≡ f y) → (z : A)
                       → sametype (lift-cong B B-cong z) (liftToFactor-dep {eqr = eqr} B B-cong f f-cong (factormap z)) ≡ f z
  i didnt even manage to write down the signature for the uniqueness of the dependent lift :( oh well.... 

  lift-unique-dep : ∀{a b r} → {A : Set a} → {_≈_ : Rel A r} → {eqr : IsEquivalence _≈_} → {B : A → Set b} → {B-cong : (x y : A) → x ≈ y → B x ≡ B y}
                    → {f : (x : A) → B x} → {f-cong : (x y : A) → (x≈y : x ≈ y) → sametype (B-cong x y x≈y) (f x) ≡ f y} → (g* : (x* : factorise A _≈_ eqr) → liftToFactor B B-cong x*)
                    → ((z : A) → sametype ? (g* (factormap z)) ≡ f z) → (x* : factorise A _≈_ eqr) → sametype ? g* x* ≡ liftToFactor f f-cong x*
                                                                        
-}





