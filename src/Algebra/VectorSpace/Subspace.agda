--library=maths

open import Agda.Primitive
open import Relation.Binary.Core
open import Data.Sum.Base
open import Relation.Nullary
open import Algebra.Field.Field renaming (Field to FD)
open import Algebra.VectorSpace.Core renaming (VectorSpace to VS)
open import Data.List hiding (sum)
open import Data.Fin hiding (_+_) renaming (zero to fzero)
open import Data.Product hiding (map)
open import Data.Nat using (ℕ)
open import Base.Equivalence
open import Data.Empty
open import Base.PropTruncation
open import NatAndFin
open import Data.Unit

module Algebra.VectorSpace.Subspace {k l} {F : Set k} {F' : FD F} {V : Set l} (V' : VS F' V) where

open import Base.Sets public

import Algebra.Field.FieldProps F' as FP
open import Algebra.VectorSpace.Props1 V'

open VS V'

record Subspace {m} (U : 𝒫 V {m}) : Set (k ⊔ l ⊔ m) where
          field
           0∈U : zvect ∈ U
           sumClosed : (x y : V) → x ∈ U → y ∈ U → (x + y) ∈ U
           scaleClosed : (x : V) → (α : F) → x ∈ U → (α ∙ x) ∈ U
           
open Subspace


subspace-sum-cong : ∀{m n} → (U : 𝒫 V {m}) → (S : Subspace U) → (vs : Fin n → V) → ((i : Fin n) → (vs i) ∈ U) → sum vs ∈ U
subspace-sum-cong {m} {ℕ.zero} U S vs vs∈U  = 0∈U S
subspace-sum-cong {m} {ℕ.suc n} U S vs vs∈U = sumClosed S (vs fzero) (sum (λ i → vs (suc i))) (vs∈U fzero)
                                                        (subspace-sum-cong U S (λ i → vs (suc i)) λ i → vs∈U (suc i))

wholeSpace : Subspace (wholeSet V)
0∈U wholeSpace = tt
sumClosed wholeSpace x y tt tt = tt
scaleClosed wholeSpace x α tt = tt


zeroSpace : Subspace (singleton zvect)
0∈U zeroSpace = refl 
sumClosed zeroSpace x y x=0 y=0 = x + y     =⟨ y=0 under x +_ ⟩
                                  x + zvect =⟨ zeroRNeut x ⟩
                                  x         =⟨ x=0 ⟩
                                  zvect □=
scaleClosed zeroSpace x α x=0 = α ∙ x     =⟨ x=0 under α ∙_ ⟩
                                α ∙ zvect =⟨ scale-zvect α ⟩
                                zvect □=


generator : ∀{m n} → 𝒫 V {m} → (Fin n → V) → Set (k ⊔ l ⊔ m)
generator U vs = (w : V) → w ∈ U → Σ (linCombo vs) (λ αs → eval vs αs ≡ w)

basis : ∀{m n} → 𝒫 V {m} → (vs : Fin n → V) → Set (k ⊔ l ⊔ m)
basis U vs = linIndep vs × generator U vs


record linearProp {m} (P : V → Set m) : Set (k ⊔ l ⊔ m) where
         field
          P0 : P zvect
          sumClosed : (x y : V) → P x → P y → P (x + y)
          scaleClosed : (x : V) (α : F) → P x → P (α ∙ x)

propSubspace : ∀{m} (P : V → Set m) → linearProp P → Subspace (propSubset P)
0∈U (propSubspace P lP) = ∣ linearProp.P0 lP ∣
sumClosed (propSubspace P lP) x y = liftToTrunc2* (λ Px Py → ∣ linearProp.sumClosed lP x y Px Py ∣)
scaleClosed (propSubspace P lP) x α = liftToTrunc* (λ Px → ∣ linearProp.scaleClosed lP x α Px ∣)


{-
extract : ∀{m} (S : Subspace {m}) → VS F' (Subspace.U S)
extract S = record
              { zvect = zvect*
              ; _+_  = _+*_
              ; -_   = -*_
              ; _∙_  = _∙*_
              ; addComm = λ x y → Subspace.injective S (x +* y) (y +* x)
                                (i (x +* y) =⟨ proj₂ (Subspace.sumClosed S x y) ⟩
                                 i x + i y  =⟨ VS.addComm V' (i x) (i y) ⟩
                                 i y + i x  =⟨ =sym (proj₂ (Subspace.sumClosed S y x)) ⟩
                                 i (y +* x) □=)
              ; addAssoc  = λ x y z → Subspace.injective S (x +* (y +* z)) ((x +* y) +* z)
                                (i (x +* (y +* z)) =⟨ proj₂ (Subspace.sumClosed S x (y +* z)) ⟩
                                 i x + i (y +* z)  =⟨ proj₂ (Subspace.sumClosed S y z) under i x +_ ⟩
                                 i x + (i y + i z) =⟨ VS.addAssoc V' (i x) (i y) (i z) ⟩
                                 (i x + i y) + i z =⟨ =sym (proj₂ (Subspace.sumClosed S x y) under _+ i z) ⟩
                                 i (x +* y) + i z  =⟨ =sym (proj₂ (Subspace.sumClosed S (x +* y) z)) ⟩
                                 i ((x +* y) +* z) □=)
              ; zeroLNeut = λ x → Subspace.injective S (zvect* +* x) x
                                (i (zvect* +* x) =⟨ proj₂ (Subspace.sumClosed S zvect* x) ⟩
                                 i zvect* + i x  =⟨ proj₂ (Subspace.0∈U S) under _+ i x ⟩
                                 zvect + i x     =⟨ VS.zeroLNeut V' (i x) ⟩
                                 i x □=)
              ; zeroRNeut = λ x → Subspace.injective S (x +* zvect*) x
                                (i (x +* zvect*) =⟨ proj₂ (Subspace.sumClosed S x zvect*) ⟩
                                 i x + i zvect*  =⟨ proj₂ (Subspace.0∈U S) under i x +_ ⟩
                                 i x + zvect     =⟨ VS.zeroRNeut V' (i x) ⟩
                                 i x □=)
              ; addLInv    = λ x → Subspace.injective S ((-* x) +* x) zvect*
                                 (i ((-* x) +* x)           =⟨ proj₂ (Subspace.sumClosed S (-* x) x) ⟩
                                 i (-* x) + i x             =⟨ proj₂ (Subspace.scaleClosed S x (-' one)) under _+ i x ⟩
                                 (-' one) ∙ i x + i x       =⟨ =sym (VS.oneNeut V' (i x)) under (-' one) ∙ i x +_ ⟩
                                 (-' one) ∙ i x + one ∙ i x =⟨ =sym (VS.scaleRDist V' (-' one) one (i x)) ⟩
                                 ((-' one) +' one) ∙ i x    =⟨ FD.addLInv F' one under _∙ i x ⟩
                                 zero ∙ i x                 =⟨ zero-scale (i x) ⟩
                                 zvect                      =⟨ =sym (proj₂ (Subspace.0∈U S)) ⟩
                                 i zvect* □= )
              ; addRInv    = λ x → Subspace.injective S (x +* (-* x)) zvect*
                                 (i (x +* (-* x))           =⟨ proj₂ (Subspace.sumClosed S x (-* x)) ⟩
                                 i x + i (-* x)             =⟨ proj₂ (Subspace.scaleClosed S x (-' one)) under i x +_ ⟩
                                 i x + (-' one) ∙ i x       =⟨ =sym (VS.oneNeut V' (i x)) under _+ (-' one) ∙ i x ⟩
                                 one ∙ i x + (-' one) ∙ i x =⟨ =sym (VS.scaleRDist V' one (-' one) (i x)) ⟩
                                 (one +' (-' one)) ∙ i x    =⟨ FD.addRInv F' one under _∙ i x ⟩
                                 zero ∙ i x                 =⟨ zero-scale (i x) ⟩
                                 zvect                      =⟨ =sym (proj₂ (Subspace.0∈U S)) ⟩
                                 i zvect* □= )
              ; scaleLDist = λ α v w → Subspace.injective S (α ∙* (v +* w)) ((α ∙* v) +* (α ∙* w))
                                    (i (α ∙* (v +* w))      =⟨ proj₂ (Subspace.scaleClosed S (v +* w) α) ⟩
                                    α ∙ i (v +* w)          =⟨ proj₂ (Subspace.sumClosed S v w) under α ∙_ ⟩
                                    α ∙ (i v + i w)         =⟨ VS.scaleLDist V' α (i v) (i w) ⟩
                                    α ∙ i v + α ∙ i w       =⟨ =sym (proj₂ (Subspace.scaleClosed S v α)) under _+ α ∙ i w ⟩
                                    i (α ∙* v) + α ∙ i w    =⟨ =sym (proj₂ (Subspace.scaleClosed S w α)) under i (α ∙* v) +_ ⟩
                                    i (α ∙* v) + i (α ∙* w) =⟨ =sym (proj₂ (Subspace.sumClosed S (α ∙* v) (α ∙* w))) ⟩
                                    i ((α ∙* v) +* (α ∙* w)) □=)
              ; scaleRDist = λ α β v → Subspace.injective S ((α +' β) ∙* v) ((α ∙* v) +* (β ∙* v))
                                    (i ((α +' β) ∙* v)       =⟨ proj₂ (Subspace.scaleClosed S v (α +' β)) ⟩
                                    (α +' β) ∙ i v           =⟨ VS.scaleRDist V' α β (i v) ⟩
                                    α ∙ i v + β ∙ i v        =⟨ =sym (proj₂ (Subspace.scaleClosed S v α)) under _+ β ∙ i v ⟩
                                    i (α ∙* v) + β ∙ i v     =⟨ =sym (proj₂ (Subspace.scaleClosed S v β)) under i (α ∙* v) +_ ⟩
                                    i (α ∙* v) + i (β ∙* v)  =⟨ =sym (proj₂ (Subspace.sumClosed S (α ∙* v) (β ∙* v))) ⟩
                                    i ((α ∙* v) +* (β ∙* v)) □=)
              ; scaleMultAssoc = λ α β v → Subspace.injective S ((α * β) ∙* v) (α ∙* (β ∙* v))
                                    (i ((α * β) ∙* v) =⟨ proj₂ (Subspace.scaleClosed S v (α * β)) ⟩
                                     (α * β) ∙ i v    =⟨ VS.scaleMultAssoc V' α β (i v) ⟩
                                     α ∙ (β ∙ i v)    =⟨ =sym (proj₂ (Subspace.scaleClosed S v β)) under α ∙_ ⟩
                                     α ∙ i (β ∙* v)   =⟨ =sym (proj₂ (Subspace.scaleClosed S (β ∙* v) α)) ⟩
                                     i (α ∙* (β ∙* v)) □=)
              ; oneNeut = λ v → Subspace.injective S (one ∙* v) v
                               (i (one ∙* v) =⟨ proj₂ (Subspace.scaleClosed S v one) ⟩
                                one ∙ i v    =⟨ VS.oneNeut V' (i v) ⟩
                                i v □=)
              ; isZvect = zeroDec'
              } where _+*_ = λ x y → proj₁ (Subspace.sumClosed S x y)
                      _∙*_ = λ α x → proj₁ (Subspace.scaleClosed S x α)
                      -*_ = (-' one) ∙*_
                      i = Subspace.i S
                      zvect* = proj₁ (Subspace.0∈U S)
                      zeroDec' : (v : Subspace.U S) → v ≡ zvect* ⊎ ¬ v ≡ zvect*
                      zeroDec' v with (isZvect (i v))
                      ... | (inj₁ iv=0) = inj₁ (Subspace.injective S v zvect* (i v    =⟨ iv=0 ⟩
                                                                               zvect  =⟨ =sym (proj₂ (Subspace.0∈U S)) ⟩
                                                                               i zvect* □=))
                      ... | (inj₂ iv≠0) = inj₂ λ v=0 → iv≠0 (i v      =⟨ v=0 under i ⟩
                                                             i zvect* =⟨ proj₂ (Subspace.0∈U S) ⟩
                                                             zvect □=)


generator-include : ∀{ls₁ ls₂ n} → {U₁ : Subspace {ls₁}} → {U₂ : Subspace {ls₂}} → (bs : Fin n → V) → generator U₁ bs → ((i : Fin n) → (bs i) ∈ U₂) → U₁ ⊆ U₂
generator-include {ls₁} {ls₂} {n} {U₁} {U₂} bs bsGenU₁ bs∈U₂ v (x , ix=v) = ∈-eq-cong U₂ (=sym Σαsbs=v) (subspace-sum-cong U₂ (λ i → αs i ∙ bs i) αsbs∈U)
                                                              where v-in-bs*  = bsGenU₁ v (x , ix=v)
                                                                    αs        = proj₁ v-in-bs*
                                                                    Σαsbs=v   = proj₂ v-in-bs*
                                                                    αsbs∈U : (i : Fin n) → αs i ∙ bs i ∈ U₂
                                                                    αsbs∈U i = subspace-scale-cong U₂ (bs i) (αs i) (bs∈U₂ i)
-}
