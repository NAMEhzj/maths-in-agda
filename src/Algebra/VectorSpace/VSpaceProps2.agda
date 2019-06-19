--library=maths

open import Agda.Primitive
open import Relation.Binary.Core
open import Data.Sum.Base
open import Relation.Nullary
open import Algebra.Field.Field renaming (Field to FD)
open import Algebra.VectorSpace.VectorSpace renaming (VectorSpace to VS)
open import Data.List hiding (sum)
open import Data.Fin hiding (_+_) renaming (zero to fzero)
open import Data.Product hiding (map)
open import Data.Nat using (ℕ)
open import Base.Equivalence hiding (_∘_)
open import Data.Empty
open import Base.PropTruncation
open import NatAndFin

module Algebra.VectorSpace.VSpaceProps2 {k l₁ l₂} {F : Set k} {F' : FD F} {V : Set l₁} {W : Set l₂} (V' : VS F' V) (W' : VS F' W) where

import Algebra.Field.FieldProps F' as FP
import Algebra.VectorSpace.VSpaceProps V' as VP
import Algebra.VectorSpace.VSpaceProps W' as WP


_+'_ = FD._+_ F'
_*_ = FD._*_ F'
-'_ = FD.-_ F'
_⁻¹[_] = FD._⁻¹[_] F'
zero = FD.zero F'
one = FD.one F'
isZero = FD.isZero F'
_+_ = VS._+_ V'
_∙_ = VS._∙_ V'
negV = VS.-_ V'
zvectV = VS.zvect V'
isZvectV = VS.isZvect V'
_⊹_ = VS._+_ W'
_∘_ = VS._∙_ W'
negW = VS.-_ W'
zvectW = VS.zvect W'
isZvectW = VS.isZvect W'



infixr 6 _+'_
infixr 7 _*_
infix 8 -'_
infixr 9 _⁻¹[_]
infixr 7 _+_
infixr 9 _∙_
infixr 7 _⊹_
infixr 9 _∘_



record Homom (φ : V → W) : Set (k ⊔ l₁ ⊔ l₂) where
         field
          sumCong : (u v : V) → φ (u + v) ≡ φ u ⊹ φ v
          scaleCong : (v : V) → (α : F) → φ (α ∙ v) ≡ α ∘ φ v


module HomomProps (φ : V → W) (φ' : Homom φ) where


  sum-cong = Homom.sumCong φ'
  scale-cong = Homom.scaleCong φ'


  zero-image : φ zvectV ≡ zvectW
  zero-image = φ zvectV          =⟨ =sym (VP.zero-scale zvectV) under φ ⟩
             φ (zero ∙ zvectV) =⟨ Homom.scaleCong φ' zvectV zero ⟩
             zero ∘ φ zvectV   =⟨ WP.zero-scale (φ zvectV) ⟩
             zvectW □=


  neg-cong : (v : V) → φ (negV v) ≡ negW (φ v)
  neg-cong v = φ (negV v)       =⟨ =sym (VP.negOne-scale v) under φ ⟩
               φ ((-' one) ∙ v) =⟨ scale-cong v (-' one) ⟩
               (-' one) ∘ φ v   =⟨ WP.negOne-scale (φ v) ⟩
               negW (φ v) □=
  
  bigSum-cong : {n : ℕ} (vs : Fin n → V) → φ (VP.sum vs) ≡ WP.sum (λ i → φ (vs i)) 
  bigSum-cong {ℕ.zero} vs = zero-image
  bigSum-cong {ℕ.suc n} vs = φ ((vs fzero) + VP.sum (λ i → (vs (suc i))))    =⟨ sum-cong (vs fzero) (VP.sum (λ i → (vs (suc i)))) ⟩
                             φ (vs fzero) ⊹ φ (VP.sum (λ i → (vs (suc i))))  =⟨ bigSum-cong (λ i → vs (suc i)) under (φ (vs fzero) ⊹_) ⟩
                             φ (vs fzero) ⊹ WP.sum (λ i → (φ (vs (suc i)))) □=


  image : WP.Subspace
  image = WP.propSubspace (λ w → Σ V (λ v → φ v ≡ w))
                       (record { P0          = (zvectV , zero-image) ;
                                 sumClosed   = sumClosed' ;
                                 scaleClosed = scaleClosed' })
                                   where sumClosed' : (w z : W) → Σ V (λ u → φ u ≡ w) → Σ V (λ v → φ v ≡ z) → Σ V (λ u+v → φ u+v ≡ w ⊹ z) 
                                         sumClosed' w z (u , refl) (v , refl) = ( u + v , Homom.sumCong φ' u v )
                                         scaleClosed' : (α : F) → (w : W) → Σ V (λ v → φ v ≡ w) → Σ V (λ αv → φ αv ≡ α ∘ w)
                                         scaleClosed' α w (v , refl) = ( α ∙ v , Homom.scaleCong φ' v α )

  kernel : VP.Subspace
  kernel = VP.propSubspace (λ v → φ v ≡ zvectW)
                      (record { P0          = zero-image ;
                                sumClosed   = λ u v φu=0 φv=0 → φ (u + v)       =⟨ Homom.sumCong φ' u v ⟩
                                                                   φ u ⊹ φ v    =⟨ φu=0 under _⊹ φ v ⟩
                                                                   zvectW ⊹ φ v =⟨ VS.zeroLNeut W' (φ v) ⟩
                                                                   φ v          =⟨ φv=0 ⟩
                                                                   zvectW □= ;
                                scaleClosed = λ α v φv=0 → φ (α ∙ v)  =⟨ Homom.scaleCong φ' v α ⟩
                                                           α ∘ φ v    =⟨ φv=0 under α ∘_ ⟩
                                                           α ∘ zvectW =⟨ WP.scale-zvect α ⟩
                                                           zvectW □= })
                                  where sumClosed' : (u v : V) → φ u ≡ zvectW → φ v ≡ zvectW → φ (u + v) ≡ zvectW
                                        sumClosed' u v φu=0 φv=0 = φ (u + v)    =⟨ Homom.sumCong φ' u v ⟩
                                                                   φ u ⊹ φ v    =⟨ φu=0 under _⊹ φ v ⟩
                                                                   zvectW ⊹ φ v =⟨ VS.zeroLNeut W' (φ v) ⟩
                                                                   φ v          =⟨ φv=0 ⟩
                                                                   zvectW □=




  {-  
  dimensionFormula : {dk di : ℕ} → VP.dimEq dk kernel → WP.dimEq di image → VP.dimEq (dk Data.Nat.+ di) VP.wholeSpace
  dimensionFormula {dk} {di} (vs , (vs∈K , (livs , genvs))) (ws , (ws∈I , (liws , genws))) = (xs , ((λ i → (xs i , refl)) , (lixs , genxs)))
                                where ws' : Fin di → V
                                      ws' i = proj₁ ∣ proj₂ (proj₁ (ws∈I i)) ∣⁻¹
                                      φws'=ws : (i : Fin di) → φ (ws' i) ≡ ws i
                                      φws'=ws i = φ (ws' i)              =⟨ proj₂ ∣ proj₂ (proj₁ (ws∈I i)) ∣⁻¹ ⟩
                                                  proj₁ (proj₁ (ws∈I i)) =⟨ proj₂ (ws∈I i) ⟩
                                                  ws i □=
                                      φvs=0 : (i : Fin dk) → φ (vs i) ≡ zvectW
                                      φvs=0 i = φ (vs i)                   =⟨ =sym (proj₂ (vs∈K i)) under φ ⟩
                                                φ (proj₁ (proj₁ (vs∈K i))) =⟨ ∣ proj₂ (proj₁ (vs∈K i)) ∣⁻¹ ⟩
                                                zvectW □=
                                      xs    = concatVec (vs , ws')
                                      lixs  : VP.linIndep xs
                                      lixs αs αsxs=0 i = αs i                       =⟨ =sym (split-concat-cong {m = dk} αs i) ⟩
                                                         (concatVec (αs₁ , αs₂)) i  =⟨ concat-prop-cong αs₁ αs₂ (_≡ zero) αs₁=0 αs₂=0 i ⟩
                                                         zero □= 
                                         where αs₁,αs₂ = splitVec {m = dk} {n = di} αs
                                               αs₁ = proj₁ αs₁,αs₂
                                               αs₂ = proj₂ αs₁,αs₂
                                               αs₁vs+αs₂ws'=αsxs : VP.eval vs αs₁ + VP.eval ws' αs₂ ≡ VP.eval xs αs
                                               αs₁vs+αs₂ws'=αsxs = VP.eval vs αs₁ + VP.eval ws' αs₂    =⟨ =sym (VP.sum-concat-cong (λ j → αs₁ j ∙ vs j) (λ j → αs₂ j ∙ ws' j)) ⟩
                                                         VP.sum (concatVec ((λ j → (αs₁ j) ∙ (vs j)) , (λ j → (αs₂ j) ∙ (ws' j))))
                                                                                                       =⟨ VP.sum-same (λ j → (VP.concat-combo vs ws' αs₁ αs₂ j)) ⟩
                                                         VP.eval xs (concatVec (αs₁ , αs₂))            =⟨ VP.sum-same (λ j → (split-concat-cong {m = dk} αs j) under _∙ (xs j)) ⟩
                                                         VP.eval xs αs □=
                                               αs₂ws = WP.eval ws αs₂
                                               αs₂ws=0 : αs₂ws ≡ zvectW
                                               αs₂ws=0 = WP.sum (λ j → (αs₂ j) ∘ (ws j))           =⟨ WP.sum-same (λ j → =sym (φws'=ws j) under (αs₂ j) ∘_) ⟩
                                                         WP.sum (λ j → (αs₂ j) ∘ φ (ws' j))        =⟨ WP.sum-same (λ j → =sym (scale-cong (ws' j) (αs₂ j))) ⟩
                                                         WP.sum (λ j → φ ((αs₂ j) ∙ (ws' j)))      =⟨ =sym (bigSum-cong (λ j → αs₂ j ∙ ws' j)) ⟩
                                                         φ (VP.eval ws' αs₂)                       =⟨ =sym (VS.zeroLNeut W' (φ (VP.eval ws' αs₂))) ⟩
                                                         zvectW ⊹ φ (VP.eval ws' αs₂)              =⟨ =sym (WP.sum-zero {dk}) under _⊹ φ (VP.eval ws' αs₂) ⟩
                                                         WP.sum {dk} (λ i → zvectW) ⊹ φ (VP.eval ws' αs₂)      =⟨ WP.sum-same (λ j → =sym (WP.scale-zvect (αs₁ j))) under _⊹ φ (VP.eval ws' αs₂) ⟩
                                                         WP.sum (λ i → αs₁ i ∘ zvectW) ⊹ φ (VP.eval ws' αs₂)   =⟨ WP.sum-same (λ j → =sym (φvs=0 j) under (αs₁ j) ∘_) under _⊹ φ (VP.eval ws' αs₂) ⟩
                                                         WP.sum (λ i → αs₁ i ∘ φ (vs i)) ⊹ φ (VP.eval ws' αs₂) =⟨ WP.sum-same (λ j → =sym (scale-cong (vs j) (αs₁ j))) under _⊹ φ (VP.eval ws' αs₂) ⟩
                                                         WP.sum (λ i → φ (αs₁ i ∙ vs i)) ⊹ φ (VP.eval ws' αs₂) =⟨ =sym (bigSum-cong (λ j → αs₁ j ∙ vs j )) under _⊹ φ (VP.eval ws' αs₂) ⟩
                                                         φ (VP.eval vs αs₁) ⊹ φ (VP.eval ws' αs₂)              =⟨ =sym (sum-cong (VP.eval vs αs₁) (VP.eval ws' αs₂)) ⟩
                                                         φ (VP.eval vs αs₁ + VP.eval ws' αs₂)                  =⟨ αs₁vs+αs₂ws'=αsxs under φ ⟩
                                                         φ (VP.eval xs αs)                                     =⟨ αsxs=0 under φ ⟩
                                                         φ zvectV                                              =⟨ zero-image ⟩
                                                         zvectW □=
                                               αs₂=0 = liws αs₂ αs₂ws=0
                                               αs₁vs=0 : VP.eval vs αs₁ ≡ zvectV
                                               αs₁vs=0 = VP.eval vs αs₁                                 =⟨ =sym (VS.zeroRNeut V' (VP.eval vs αs₁)) ⟩
                                                         VP.eval vs αs₁ + zvectV                        =⟨ =sym (VP.sum-zero {di}) under VP.eval vs αs₁ +_ ⟩
                                                         VP.eval vs αs₁ + VP.sum {di} (λ j → zvectV)    =⟨ VP.sum-same (λ j → =sym (VP.zero-scale (ws' j))) under VP.eval vs αs₁ +_ ⟩
                                                         VP.eval vs αs₁ + VP.sum (λ j → zero ∙ (ws' j)) =⟨ (VP.sum-same (λ j → =sym (αs₂=0 j) under _∙ (ws' j)) under VP.eval vs αs₁ +_) ⟩
                                                         VP.eval vs αs₁ + VP.eval ws' αs₂               =⟨ αs₁vs+αs₂ws'=αsxs ⟩
                                                         VP.eval xs αs                                  =⟨ αsxs=0 ⟩
                                                         zvectV □=
                                               αs₁=0 = livs αs₁ αs₁vs=0
                                      genxs : VP.generator VP.wholeSpace xs
                                      genxs v _ = (αs , αsxs=v)
                                         where genφv = genws (φ v) ((φ v , ∣ v , refl ∣) , refl)
                                               αs₂ = proj₁ genφv
                                               αs₂zs=φv = proj₂ genφv
                                               v' = VP.eval ws' αs₂
                                               v'' = v + negV v'
                                               φv''=0 : φ v'' ≡ zvectW
                                               φv''=0 = φ (v + negV v')                                 =⟨ sum-cong v (negV v') ⟩
                                                        φ v ⊹ φ (negV v')                               =⟨ neg-cong v' under φ v ⊹_ ⟩
                                                        φ v ⊹ negW (φ (VP.eval ws' αs₂))                =⟨ bigSum-cong (λ i → αs₂ i ∙ ws' i) under (λ t → φ v ⊹ negW t) ⟩
                                                        φ v ⊹ negW (WP.sum (λ i → φ (αs₂ i ∙ ws' i)))   =⟨ WP.sum-same (λ i → scale-cong (ws' i) (αs₂ i)) under (λ t → φ v ⊹ negW t) ⟩
                                                        φ v ⊹ negW (WP.sum (λ i → (αs₂ i) ∘ φ (ws' i))) =⟨ WP.sum-same (λ i → (φws'=ws i) under (αs₂ i) ∘_ ) under (λ t → φ v ⊹ negW t) ⟩
                                                        φ v ⊹ negW (WP.eval ws αs₂)                     =⟨ αs₂zs=φv under (λ t → φ v ⊹ negW t) ⟩
                                                        φ v ⊹ negW (φ v)                                =⟨ VS.addRInv W' (φ v) ⟩
                                                        zvectW □=
                                               genv'' = genvs v'' ((v'' , ∣ φv''=0 ∣) , refl)
                                               αs₁ = proj₁ genv''
                                               αs₁vs=v'' = proj₂ genv''
                                               αs = concatVec (αs₁ , αs₂)
                                               αsxs=v : VP.eval xs αs ≡ v
                                               αsxs=v = VP.eval xs αs                                                             =⟨ =sym (VP.sum-same (λ j → (VP.concat-combo vs ws' αs₁ αs₂ j))) ⟩
                                                        VP.sum (concatVec ((λ j → (αs₁ j) ∙ (vs j)) , (λ j → (αs₂ j) ∙ (ws' j)))) =⟨ VP.sum-concat-cong (λ i → αs₁ i ∙ vs i) (λ i → αs₂ i ∙ ws' i) ⟩
                                                        VP.eval vs αs₁ + VP.eval ws' αs₂                                          =⟨ αs₁vs=v'' under _+ VP.eval ws' αs₂ ⟩
                                                        (v + negV v') + v'                                                        =⟨ =sym (VS.addAssoc V' v (negV v') v') ⟩
                                                        v + (negV v' + v')                                                        =⟨ VS.addLInv V' v' under v +_ ⟩
                                                        v + zvectV                                                                =⟨ VS.zeroRNeut V' v ⟩
                                                        v □= 
   -}                                            
   

