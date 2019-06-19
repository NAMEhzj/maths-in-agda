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
open import Base.Equivalence
open import Data.Empty
open import Base.PropTruncation
open import NatAndFin


module Algebra.VectorSpace.VSpaceProps {k l} {F : Set k} {F' : FD F} {V : Set l} (V' : VS F' V) where


import Algebra.Field.FieldProps F' as FP



isZero = FD.isZero F'
open VS V'



zero-scale : (v : V) → zero ∙ v ≡ zvect
zero-scale v = zero ∙ v                   =⟨ =sym (VS.zeroRNeut V' (zero ∙ v)) ⟩
               zero ∙ v + zvect           =⟨ =sym (VS.addRInv V' v) under (λ t → zero ∙ v + t) ⟩
               zero ∙ v + (v + - v)       =⟨ VS.addAssoc V' (zero ∙ v) v (- v) ⟩
               (zero ∙ v + v) + - v       =⟨ =sym (VS.oneNeut V' v) under (λ t → (zero ∙ v + t) + - v) ⟩
               (zero ∙ v + one ∙ v) + - v =⟨ =sym (VS.scaleRDist V' zero one v) under (λ t → t + - v) ⟩
               (zero +' one) ∙ v + - v    =⟨ (FD.zeroLNeut F' one) under (λ t → t ∙ v + - v) ⟩
               one ∙ v + - v              =⟨ VS.oneNeut V' v under (λ t → t + - v) ⟩
               v + - v                    =⟨ VS.addRInv V' v ⟩
               zvect □= 



negOne-scale : (v : V) → (-' one) ∙ v ≡ - v
negOne-scale v = (-' one) ∙ v                    =⟨ =sym (VS.zeroRNeut V' ((-' one) ∙ v)) ⟩
                 (-' one) ∙ v + zvect            =⟨ =sym (VS.addRInv V' v) under (λ t → (-' one) ∙ v + t) ⟩
                 (-' one) ∙ v + (v + - v)        =⟨ VS.addAssoc V' ((-' one) ∙ v) v (- v) ⟩
                 ((-' one) ∙ v + v) + - v        =⟨ =sym (VS.oneNeut V' v) under (λ t → ((-' one) ∙ v + t) + - v) ⟩
                 ((-' one) ∙ v + one ∙ v) + - v  =⟨ =sym (VS.scaleRDist V' (-' one) one v) under (λ t → t + - v) ⟩
                 ((-' one) +' one) ∙ v + - v     =⟨ (FD.addLInv F' one) under (λ t → t ∙ v + - v) ⟩
                 zero ∙ v + - v                  =⟨ (zero-scale v) under (λ t → t + - v) ⟩
                 zvect + - v                     =⟨ VS.zeroLNeut V' (- v) ⟩
                 - v □=





scale-zvect : (α : F) → α ∙ zvect ≡ zvect
scale-zvect α = α ∙ zvect                             =⟨ =sym (VS.zeroRNeut V' (α ∙ zvect)) ⟩
                α ∙ zvect + zvect                     =⟨ =sym (VS.addRInv V' (α ∙ zvect)) under (λ t → α ∙ zvect + t) ⟩
                α ∙ zvect + (α ∙ zvect + - α ∙ zvect) =⟨ VS.addAssoc V' (α ∙ zvect) (α ∙ zvect) (- α ∙ zvect) ⟩
               (α ∙ zvect + α ∙ zvect) + - α ∙ zvect  =⟨ =sym (VS.scaleLDist V' α zvect zvect) under (λ t → t + - α ∙ zvect) ⟩
                α ∙ (zvect + zvect) + - α ∙ zvect     =⟨ (VS.zeroLNeut V' zvect) under (λ t → α ∙ t + - α ∙ zvect) ⟩
                α ∙ zvect + - α ∙ zvect               =⟨ VS.addRInv V' (α ∙ zvect) ⟩
               zvect □=



sum : {n : ℕ} → (vs : Fin n → V) → V
sum {ℕ.zero} _   = zvect
sum {ℕ.suc n} vs = (vs fzero) + sum (tail vs)

sumF = FP.sum

sumF-dist : {n : ℕ} → (αs : Fin n → F) → (v : V) → (sumF αs) ∙ v ≡ sum (λ i → (αs i) ∙ v)
sumF-dist {ℕ.zero}  _  v = zero-scale v
sumF-dist {ℕ.suc n} αs v = ((αs fzero) +' sumF (tail αs)) ∙ v  =⟨ VS.scaleRDist V' (αs fzero) (sumF (tail αs)) v ⟩
                           (αs fzero) ∙ v + sumF (tail αs) ∙ v =⟨ sumF-dist (tail αs) v under (λ t → (αs fzero) ∙ v + t) ⟩
                           (αs fzero) ∙ v + sum (λ i → αs (suc i) ∙ v) □=


sum-dist : {n : ℕ} → (α : F) → (vs : Fin n → V) → α ∙ (sum vs) ≡ sum (λ i → α ∙ (vs i))
sum-dist {ℕ.zero}  α _  = scale-zvect α
sum-dist {ℕ.suc n} α vs = α ∙ ((vs fzero) + sum (tail vs))    =⟨ VS.scaleLDist V' α (vs fzero) (sum (tail vs)) ⟩
                          α ∙ (vs fzero) + α ∙ sum (tail vs)  =⟨ sum-dist α (tail vs) under (λ t → α ∙ (vs fzero) + t) ⟩
                          α ∙ (vs fzero) + sum (λ i → α ∙ (vs (suc i))) □=


sum-zero : {n : ℕ} → sum {n} (λ i → zvect) ≡ zvect
sum-zero {ℕ.zero}  = refl
sum-zero {ℕ.suc n} = zvect + sum {n} (λ i → zvect)  =⟨ VS.zeroLNeut V' (sum {n} (λ i → zvect)) ⟩
                     sum {n} (λ i → zvect)          =⟨ sum-zero {n} ⟩
                     zvect □=



sum-same : {n : ℕ} → {vs : Fin n → V} → {ws : Fin n → V} → ((i : Fin n) → vs i ≡ ws i) → sum vs ≡ sum ws
sum-same {ℕ.zero}            _     = refl
sum-same {ℕ.suc n} {vs} {ws} vs=ws = vs fzero + sum (tail vs) =⟨ (vs=ws fzero) under (λ t → t + sum (tail vs)) ⟩
                                     ws fzero + sum (tail vs) =⟨ sum-same (λ i → vs=ws (suc i)) under (λ t → ws fzero + t)⟩
                                     ws fzero + sum (tail ws) □=



sum-join : {n : ℕ} → (vs : Fin n → V) → (ws : Fin n → V) → sum vs + sum ws ≡ sum (λ i → (vs i) + (ws i))
sum-join {ℕ.zero}  vs ws = zvect + zvect =⟨ VS.zeroLNeut V' zvect ⟩ zvect □= 
sum-join {ℕ.suc n} vs ws = (v₁ + vsum) + (w₁ + wsum)  =⟨ =sym (VS.addAssoc V' v₁ vsum (w₁ + wsum)) ⟩
                            v₁ + (vsum + (w₁ + wsum)) =⟨ (VS.addAssoc V' vsum w₁ wsum) under (λ t → v₁ + t) ⟩
                            v₁ + ((vsum + w₁) + wsum) =⟨ (VS.addComm V' vsum w₁) under (λ t → v₁ + (t + wsum)) ⟩
                            v₁ + ((w₁ + vsum) + wsum) =⟨ =sym (VS.addAssoc V' w₁ vsum wsum) under (λ t → v₁ + t) ⟩
                            v₁ + (w₁ + (vsum + wsum)) =⟨ VS.addAssoc V' v₁ w₁ (vsum + wsum) ⟩
                           (v₁ + w₁) + (vsum + wsum)  =⟨ sum-join (tail vs) (tail ws) under (λ t → (v₁ + w₁) + t) ⟩
                           (v₁ + w₁) + sum (λ i → (vs (suc i)) + (ws (suc i))) □=
                                where v₁ = vs fzero
                                      vsum = sum (tail vs)
                                      w₁ = ws fzero
                                      wsum = sum (tail ws)


sum-swap : {n m : ℕ} → (vss : Fin n → Fin m → V) → sum (λ i → sum (vss i)) ≡ sum (λ j → sum (λ i → vss i j))
sum-swap {ℕ.zero} {m} vss = =sym (sum-zero {m})
sum-swap {ℕ.suc n}    vss = sum (vss fzero) + sum (λ i → sum (vss (suc i)))           =⟨ sum-swap (λ i j → vss (suc i) j) under (λ t → sum (vss fzero) + t) ⟩
                            sum (vss fzero) + sum (λ j → sum (λ i → vss (suc i) j ))  =⟨ sum-join (vss fzero) (λ j → sum (λ i → vss (suc i) j)) ⟩
                            sum (λ j → (vss fzero j) + sum (λ i → vss (suc i) j))     □=



sum-concat-cong : {m n : ℕ} → (vs : Fin m → V) → (ws : Fin n → V) → sum (concatVec (vs , ws)) ≡ sum vs + sum ws
sum-concat-cong {ℕ.zero} vs ws  = =sym (VS.zeroLNeut V' (sum ws))
sum-concat-cong {ℕ.suc m} vs ws = vs fzero + sum (concatVec (tail vs , ws )) =⟨ sum-concat-cong (tail vs) ws under vs fzero +_ ⟩
                                  vs fzero + (sum (tail vs) + sum ws)        =⟨ VS.addAssoc V' (vs fzero) (sum (tail vs)) (sum ws) ⟩
                                  sum vs + sum ws □=


concat-combo : {m n : ℕ} → (us : Fin m → V) → (vs : Fin n → V) → (αs : Fin m → F) → (βs : Fin n → F) → (i : Fin (m Data.Nat.+ n)) 
                      → concatVec ((λ j → αs j ∙ us j)  ,  λ j → βs j ∙ vs j) i ≡ concatVec (αs , βs) i ∙ concatVec (us , vs) i
concat-combo {ℕ.zero} us vs αs βs i = refl
concat-combo {ℕ.suc m} us vs αs βs fzero = refl
concat-combo {ℕ.suc m} us vs αs βs (suc i) = concat-combo {m} (tail us) vs (tail αs) βs i
                                                                                                    



linCombo : {n : ℕ} → (Fin n → V) → Set k
linCombo {n} _ = Fin n → F 

eval : {n : ℕ} → (vs : Fin n → V) → linCombo vs → V
eval {n} vs αs = sum (λ i → (αs i) ∙ (vs i))

linIndep : {n : ℕ} (vs : Fin n → V) → Set (k ⊔ l) 
linIndep {n} vs = (αs : linCombo vs) → eval vs αs ≡ zvect → (i : Fin n) → αs i ≡ zero 


remove-linIndep-cong : {n : ℕ} → (vs : Fin (ℕ.suc n) → V) → linIndep vs → linIndep (λ i → vs (suc i))
remove-linIndep-cong {n} vs livs αs Σαsvs'=0 i = βs=0 (suc i)
                                       where βs : Fin (ℕ.suc n) → F
                                             βs fzero = zero
                                             βs (suc j) = αs j
                                             βs=0 : (i : Fin (ℕ.suc n)) → βs i ≡ zero
                                             βs=0 = livs βs (zero ∙ (vs fzero) + eval (λ i → vs (suc i)) αs =⟨ zero-scale (vs fzero) under _+ eval (λ i → vs (suc i)) αs ⟩
                                                             zvect + eval (λ i → vs (suc i)) αs             =⟨ VS.zeroLNeut V' (eval (λ i → vs (suc i)) αs) ⟩
                                                             eval (λ i → vs (suc i)) αs                     =⟨ Σαsvs'=0 ⟩
                                                             zvect □=)



record Subspace {m} : Set (k ⊔ l ⊔ (lsuc m)) where
        coinductive
        field
         U : Set m
         i : U → V
         injective : (x y : U) → i x ≡ i y → x ≡ y
         0∈U : Σ U (λ x → i x ≡ zvect)
         sumClosed : (x y : U) → Σ U (λ z → i z ≡ i x + i y)
         scaleClosed : (x : U) → (α : F) → Σ U (λ z → i z ≡ α ∙ (i x))



_∈_ : ∀{m} → V → Subspace {m} → Set (l ⊔ m)
v ∈ U' = Σ U (λ x → i x ≡ v)
              where U = Subspace.U U'
                    i = Subspace.i U'

infix 3 _∈_

∈-eq-cong : ∀{m} (U : Subspace {m}) → {x y : V} → x ≡ y → y ∈ U → x ∈ U
∈-eq-cong _ refl x∈U = x∈U


subspace-plus-cong : ∀{m} → (U : Subspace {m}) → (v w : V) → v ∈ U → w ∈ U → (v + w) ∈ U
subspace-plus-cong U v w (x , ix=v) (y , iy=w) = z , (i z        =⟨ iz=ix+iy ⟩
                                                      i x + i y  =⟨ ix=v under _+ i y ⟩
                                                      v + i y    =⟨ iy=w under  v +_ ⟩
                                                      v + w □=)
                             where z* = Subspace.sumClosed U x y
                                   z = proj₁ z*
                                   iz=ix+iy = proj₂ z*
                                   i = Subspace.i U


subspace-scale-cong : ∀{m} → (U : Subspace {m}) → (v : V) → (α : F) → v ∈ U → α ∙ v ∈ U
subspace-scale-cong U v α (x , ix=v) = z , (i z       =⟨ iz=α∙ix ⟩
                                            α ∙ (i x) =⟨ ix=v under α ∙_ ⟩
                                            α ∙ v □=)
                            where z* = Subspace.scaleClosed U x α
                                  z = proj₁ z*
                                  iz=α∙ix = proj₂ z*
                                  i = Subspace.i U


subspace-sum-cong : ∀{m n} → (U : Subspace {m}) → (vs : Fin n → V) → ((i : Fin n) → vs i ∈ U) → sum vs ∈ U
subspace-sum-cong {m} {ℕ.zero} U vs vs∈U  = Subspace.0∈U U
subspace-sum-cong {m} {ℕ.suc n} U vs vs∈U = subspace-plus-cong U (vs fzero) (sum (λ i → vs (suc i))) (vs∈U fzero)
                                                        (subspace-sum-cong U (λ i → vs (suc i)) λ i → vs∈U (suc i))



wholeSpace : Subspace {l}
Subspace.U wholeSpace = V
Subspace.i wholeSpace x = x
Subspace.injective wholeSpace x y refl =  refl
Subspace.0∈U wholeSpace = (zvect , refl)
Subspace.sumClosed wholeSpace x y = ( x + y , refl)
Subspace.scaleClosed wholeSpace x α = ( α ∙ x , refl)

{-
wholeSpace = record
               { U = V ;
                 i = λ x → x ;
                 injective = inj;
                 0∈U = (zvect , refl) ;
                 sumClosed   = λ x y → (x + y , refl) ;
                 scaleClosed = λ x α → (α ∙ x , refl) }
                  where inj : (x y : V) → x ≡ y → x ≡ y
                        inj x y refl = refl
-}

_⊆_ : ∀{m n} → Subspace {m} → Subspace {n} → Set (l ⊔ m ⊔ n)
U₁ ⊆ U₂ = (v : V) → v ∈ U₁ → v ∈ U₂ 

_≃_ : ∀{m n} → Subspace {m} → Subspace {n} → Set (l ⊔ m ⊔ n)
U₁ ≃ U₂ = U₁ ⊆ U₂ × U₂ ⊆ U₁


generator : ∀{m n} → Subspace {m} → (Fin n → V) → Set (k ⊔ l ⊔ m)
generator U vs = (w : V) → w ∈ U → Σ (linCombo vs) (λ αs → eval vs αs ≡ w)


basis : ∀{m n} → Subspace {m} → (vs : Fin n → V) → Set (k ⊔ l ⊔ m)
basis U vs = linIndep vs × generator U vs



record LinearProp {m} (P : V → Set m) : Set (k ⊔ l ⊔ (lsuc m)) where
         field
          P0 : P zvect
          sumClosed : (v w : V) → P v → P w → P (v + w)
          scaleClosed :  (α : F) → (v : V) → P v → P (α ∙ v)




propSubspace : ∀{m} → (P : V → Set m) → LinearProp P → Subspace
propSubspace P LP = record { U = Σ V ∥P∥ ;
                             i = proj₁ ;
                             injective = inj ;
                             0∈U = (zvect , ∣ LinearProp.P0 LP ∣) , refl ;
                             sumClosed = λ v* w* → ((proj₁ v* + proj₁ w* , sumClosed' v* w*) , refl ) ;
                             scaleClosed = λ v* α → ((α ∙ proj₁ v* , scaleClosed' α v*) , refl) }
                                   where ∥P∥ = λ x → ∥ P x ∥
                                         sumClosed-base : (v w : V) → P v → P w → ∥ P (v + w) ∥
                                         sumClosed-base v w Pv Pw = ∣ LinearProp.sumClosed LP v w Pv Pw ∣
                                         sumClosed' : (v* w* : Σ V ∥P∥) → ∥ P ((proj₁ v*) + (proj₁ w*)) ∥
                                         sumClosed' (v , Pv) (w , Pw) = liftToTrunc2* (sumClosed-base v w) Pv Pw
                                         scaleClosed-base : (α : F) → (v : V) → P v → ∥ P (α ∙  v) ∥
                                         scaleClosed-base α v Pv = ∣ LinearProp.scaleClosed LP α v Pv ∣
                                         scaleClosed' : (α : F) → (v* : Σ V ∥P∥) → ∥ P (α ∙ (proj₁ v*)) ∥
                                         scaleClosed' α (v , Pv) = liftToTrunc* (scaleClosed-base α v) Pv
                                         inj : (x y : Σ V ∥P∥) → proj₁ x ≡ proj₁ y → x ≡ y
                                         inj (x , px) (y , py) refl with (isTrunc px py)
                                         ... | refl = refl



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
                                                                    
                                                                    
                                                      

pointChangeF : {n : ℕ} → (Fin n → F) → (F → F) → Fin n → Fin n → F
pointChangeF αs f i j with (i ≟ j)
...                    | yes (i=j) = f (αs j)
...                    |  no (i≠j) = αs j


rowChangeF : {n m : ℕ} → (Fin n → Fin m → F) → (Fin m → F → F) → Fin n → Fin n → Fin m → F
rowChangeF αss f p i j with (p ≟ i)
...                    | yes (p=i) = f j (αss i j)
...                    |  no (p≠i) = αss i j




pointChangeF-ignore : {n : ℕ} → (αs : Fin n → F) → (f : F → F) → (p i : Fin n) → ¬ p ≡ i → pointChangeF αs f p i ≡ αs i
pointChangeF-ignore αs f p i p≠i with (p ≟ i)
... | yes p=i = ⊥-elim (p≠i p=i)  
... | no _    = refl

pointChangeF-see : {n : ℕ} → (αs : Fin n → F) → (f : F → F) → (p i : Fin n) → p ≡ i → pointChangeF αs f p i ≡ f (αs i)
pointChangeF-see αs f p i p=i with (p ≟ i)
... | yes _  = refl
... | no p≠i = ⊥-elim (p≠i p=i)


rowChangeF-ignore : {n m : ℕ} → (αss : Fin n → Fin m → F) → {f : Fin m → F → F} → (p i : Fin n) → ¬ p ≡ i → (j : Fin m) → rowChangeF αss f p i j ≡ αss i j
rowChangeF-ignore αss p i p≠i j with (p ≟ i)
... | yes p=i = ⊥-elim (p≠i p=i)  
... | no _    = refl

rowChangeF-see : {n m : ℕ} → (αss : Fin n → Fin m → F) → (f : Fin m → F → F) → (p i : Fin n) → p ≡ i → (j : Fin m) → rowChangeF αss f p i j ≡ f j (αss i j)
rowChangeF-see αs f p i p=i j with (p ≟ i)
... | yes _  = refl
... | no p≠i = ⊥-elim (p≠i p=i)



pointChangeV : {n : ℕ} → (Fin n → V) → (V → V) → Fin n → Fin n → V
pointChangeV vs f p i with (p ≟ i)
...                    | yes (p=i) = f (vs i)
...                    |  no (p≠i) = vs i


pointChangeV-same : {n : ℕ} → (xs ys : Fin n → V) → ((i : Fin n) → xs i ≡ ys i) → (f : V → V) → (p i : Fin n) → pointChangeV xs f p i ≡ pointChangeV ys f p i
pointChangeV-same xs ys xs=ys f p i with (p ≟ i)
... | yes p=i = f (xs i) =⟨ (xs=ys i) under f ⟩
                f (ys i) □= 
... | no  p≠i = xs=ys i



pointChange-cong : {n : ℕ} → (xs : Fin n → V) → (βs : Fin n → F) → (α : F) → (p : Fin n) → (i : Fin n) → (βs i) ∙ (pointChangeV xs (α ∙_ ) p i)  ≡ (pointChangeF βs (α *_) p i) ∙ (xs i)
pointChange-cong xs βs α p i with (p ≟ i)
... | yes p=i = (βs i) ∙ α ∙ (xs i)   =⟨ =sym (VS.scaleMultAssoc V' (βs i) α (xs i)) ⟩
                ((βs i) * α) ∙ (xs i) =⟨ FD.multComm F' (βs i) α under (λ t → t ∙ (xs i)) ⟩
                (α * (βs i)) ∙ (xs i) □=
... | no  p≠i = refl



scalePt-LIndep-cong : {n : ℕ} → (xs : Fin n → V) → linIndep xs → (α : F) → (¬ α ≡ zero) → (p : Fin n) →  linIndep (pointChangeV xs (α ∙_) p)
scalePt-LIndep-cong {n} xs lixs α α≠0 p βs βsαxs=0 = helper (lixs (pointChangeF βs (α *_) p)
                                                              (eval xs (pointChangeF βs (α *_) p) =⟨ =sym (sum-same (pointChange-cong xs βs α p)) ⟩
                                                               eval (pointChangeV xs (α ∙_) p) βs =⟨ βsαxs=0 ⟩
                                                               zvect □=))                                                               
                     where helper : ((i : Fin n) → (pointChangeF βs (α *_) p) i ≡ zero) → (q' : Fin n) → βs q' ≡ zero
                           helper βsα=0 q' with (p ≟ q')
                           ... | yes p=q' = FP.onezero-split α (βs q') (α * (βs q')                =⟨ =sym (pointChangeF-see βs (α *_) p q' p=q') ⟩
                                                                       pointChangeF βs (α *_) p q' =⟨ βsα=0 q' ⟩
                                                                       zero □=) α≠0
                           ... | no  p≠q' = βs q'                        =⟨ =sym (pointChangeF-ignore βs (α *_ ) p q' p≠q') ⟩
                                            pointChangeF βs (α *_) p q'  =⟨ βsα=0 q' ⟩
                                            zero □=



pointAddV-split : {n : ℕ} → (xs : Fin n → V) → (y : V) → (αs : Fin n → F) → (p : Fin n) → eval (pointChangeV xs (y +_) p) αs ≡ (αs p) ∙ y + eval xs αs
pointAddV-split xs y αs fzero   = (αs fzero) ∙ (y + xs fzero) + rest                 =⟨ VS.scaleLDist V' (αs fzero) y (xs fzero) under (λ t → t + rest)⟩
                                  ((αs fzero) ∙ y + (αs fzero) ∙ (xs fzero)) + rest  =⟨ =sym (VS.addAssoc V' ((αs fzero) ∙ y) ((αs fzero) ∙ (xs fzero)) rest) ⟩
                                  (αs fzero) ∙ y + (αs fzero) ∙ (xs fzero) + rest   □=
                                            where rest = eval (λ i → xs (suc i)) (λ i → αs (suc i))
pointAddV-split {ℕ.suc n} xs y αs (suc p) =
               fstTerm + eval (λ i → (pointChangeV xs (y +_) (suc p)) (suc i)) (λ i → αs (suc i))  =⟨ sum-same (λ i → (helper i) under (λ t → αs (suc i) ∙ t)) under (λ t → fstTerm + t) ⟩
               fstTerm + eval (pointChangeV (λ i → xs (suc i)) (y +_) p) (λ i → αs (suc i))        =⟨ (pointAddV-split (λ i → xs (suc i)) y (λ i → αs (suc i)) p) under (λ t → fstTerm + t)⟩
               fstTerm + (αs (suc p) ∙ y + rest)                                                   =⟨ VS.addAssoc V' fstTerm (αs (suc p) ∙ y) rest ⟩
              (fstTerm + αs (suc p) ∙ y) + rest                                                    =⟨ VS.addComm V' fstTerm (αs (suc p) ∙ y) under (λ t → t + rest) ⟩
              (αs (suc p) ∙ y + fstTerm) + rest                                                    =⟨ =sym (VS.addAssoc V' (αs (suc p) ∙ y) fstTerm rest) ⟩
               αs (suc p) ∙ y + (fstTerm + rest)   □=
                                            where fstTerm = (αs fzero) ∙ (xs fzero)
                                                  rest    = eval (λ i → xs (suc i)) (λ i → αs (suc i))
                                                  helper : (i : Fin n) → pointChangeV xs (y +_) (suc p) (suc i) ≡ pointChangeV (λ j → xs (suc j)) (y +_) p i
                                                  helper i with (p ≟ i)
                                                  ... | yes p=i = refl
                                                  ... | no  p≠i = refl


pointAddF-split : {n : ℕ} → (αs : Fin n → F) → (β : F) → (xs : Fin n → V) → (p : Fin n) → eval xs (pointChangeF αs (β +'_) p) ≡ β ∙ (xs p) + eval xs αs
pointAddF-split αs β xs fzero   = (β +' αs fzero) ∙ (xs fzero) + rest                 =⟨ VS.scaleRDist V' β (αs fzero) (xs fzero) under (λ t → t + rest)⟩
                                  (β ∙ (xs fzero) + (αs fzero) ∙ (xs fzero)) + rest  =⟨ =sym (VS.addAssoc V' (β ∙ (xs fzero)) ((αs fzero) ∙ (xs fzero)) rest) ⟩
                                   β ∙ (xs fzero) + (αs fzero) ∙ (xs fzero) + rest   □=
                                          where rest = eval (λ i → xs (suc i)) (λ i → αs (suc i))
pointAddF-split {ℕ.suc n} αs β xs (suc p) = 
               fstTerm + eval (λ i → xs (suc i)) (λ i → (pointChangeF αs (β +'_) (suc p)) (suc i)) =⟨ sum-same (λ i → (helper i) under (λ t → t ∙ xs (suc i))) under (λ t → fstTerm + t) ⟩
               fstTerm + eval (λ i → xs (suc i)) (pointChangeF (λ i → αs (suc i)) (β +'_) p)       =⟨ (pointAddF-split (λ i → αs (suc i)) β (λ i → xs (suc i)) p) under (λ t → fstTerm + t)⟩
               fstTerm + (β ∙ xs (suc p) + rest)                                                   =⟨ VS.addAssoc V' fstTerm (β ∙ xs (suc p)) rest ⟩
              (fstTerm + β ∙ xs (suc p)) + rest                                                    =⟨ VS.addComm V' fstTerm (β ∙ xs (suc p)) under (λ t → t + rest) ⟩
              (β ∙ xs (suc p) + fstTerm) + rest                                                    =⟨ =sym (VS.addAssoc V' (β ∙ xs (suc p)) fstTerm rest) ⟩
               β ∙ xs (suc p) + (fstTerm + rest)   □=
                                            where fstTerm = (αs fzero) ∙ (xs fzero)
                                                  rest    = eval (λ i → xs (suc i)) (λ i → αs (suc i))
                                                  helper : (i : Fin n) → pointChangeF αs (β +'_) (suc p) (suc i) ≡ pointChangeF (λ j → αs (suc j)) (β +'_) p i
                                                  helper i with (p ≟ i)
                                                  ... | yes p=i = refl
                                                  ... | no  p≠i = refl




addVect-LIndep-cong : {n : ℕ} → (xs : Fin n → V) → linIndep xs → (p q : Fin n) → ¬ p ≡ q → linIndep (pointChangeV xs (xs p +_) q)
addVect-LIndep-cong {n} xs lixs p q p≠q αs αsys=0 = helper (lixs (pointChangeF αs (αs q +'_) p)
                                                                 (eval xs (pointChangeF αs (αs q +'_) p) =⟨ pointAddF-split αs (αs q) xs p ⟩
                                                                 (αs q) ∙ (xs p) + eval xs αs            =⟨ =sym (pointAddV-split xs (xs p) αs q) ⟩
                                                                 eval (pointChangeV xs (xs p +_) q) αs   =⟨ αsys=0 ⟩
                                                                 zvect □=))
                     where helper : ((i : Fin n) → (pointChangeF αs (αs q +'_) p) i ≡ zero) → (j : Fin n) → αs j ≡ zero
                           helper βs=0 j with (p ≟ j)
                           ... | yes p=j = αs j                            =⟨ =sym (FD.zeroLNeut F' (αs j)) ⟩
                                           zero +' αs j                    =⟨ =sym αsq=0 under (λ t → t +' αs j) ⟩
                                           αs q +' αs j                    =⟨ =sym (pointChangeF-see αs (αs q +'_) p j p=j) ⟩
                                           pointChangeF αs (αs q +'_) p j  =⟨ βs=0 j ⟩
                                           zero □=
                                           where αsq=0 : αs q ≡ zero
                                                 αsq=0 = αs q                            =⟨ =sym (pointChangeF-ignore αs (αs q +'_) p q p≠q) ⟩
                                                         pointChangeF αs (αs q +'_) p q  =⟨ βs=0 q ⟩
                                                         zero □=                                                         
                           ... | no  p≠j = αs j                            =⟨ =sym (pointChangeF-ignore αs (αs q +'_ ) p j p≠j) ⟩
                                           pointChangeF αs (αs q +'_) p j  =⟨ βs=0 j ⟩
                                           zero □=



data RowOperation (n : ℕ) : Set k where
              Id : RowOperation n
              Scale : (α : F) → ¬ α ≡ zero →  Fin n → RowOperation n → RowOperation n
              Add : (p q : Fin n) → ¬ p ≡ q → RowOperation n → RowOperation n


opOnVecs : {n : ℕ} → RowOperation n → (Fin n → V) → Fin n → V
opOnVecs Id xs = xs
opOnVecs (Scale α _ p subOp) xs = pointChangeV (opOnVecs subOp xs) (α ∙_) p
opOnVecs (Add p q _ subOp) xs   = pointChangeV xs' (xs' p +_) q
                                       where xs' = opOnVecs subOp xs


opOnScalars : {n m : ℕ} → RowOperation n → (Fin n → Fin m → F) → Fin n → Fin m → F
opOnScalars Id βss = βss
opOnScalars (Scale α _ p subOp) βss = rowChangeF (opOnScalars subOp βss) (λ j → α *_) p
opOnScalars (Add p q _ subOp) βss   = rowChangeF βss' (λ j → (βss' p j) +'_) q
                                         where βss' = opOnScalars subOp βss


rowOp-LIndep-cong : {n : ℕ} → (xs : Fin n → V) → (ro : RowOperation n) → linIndep xs → linIndep (opOnVecs ro xs)
rowOp-LIndep-cong {n} xs Id lixs = lixs
rowOp-LIndep-cong {n} xs (Scale α α≠0 p subOp) lixs = scalePt-LIndep-cong xs' lixs' α α≠0 p
                                               where xs'   = opOnVecs subOp xs
                                                     lixs' = rowOp-LIndep-cong xs subOp lixs
rowOp-LIndep-cong {n} xs (Add p q p≠q subOp) lixs   = addVect-LIndep-cong xs' lixs' p q p≠q
                                               where xs'   = opOnVecs subOp xs
                                                     lixs' = rowOp-LIndep-cong xs subOp lixs



rowScaleF-eval-cong : {n m : ℕ} → (xs : Fin m → V) → (αss : Fin n → Fin m → F) → (β : F) → (p i : Fin n) →  eval xs (rowChangeF αss (λ j → β *_) p i) ≡ pointChangeV (λ i' → eval xs (αss i')) (β ∙_) p i
rowScaleF-eval-cong xs αss β p i with (p ≟ i)
... | yes p=i = sum (λ j → (β * αss i j) ∙ (xs j))  =⟨ sum-same (λ j → VS.scaleMultAssoc V' β (αss i j) (xs j)) ⟩
                sum (λ j → β ∙ (αss i j ∙ (xs j)))  =⟨ =sym (sum-dist β (λ j → (αss i j) ∙ (xs j))) ⟩
                β ∙ sum (λ j → (αss i j) ∙ (xs j)) □=
... | no  p≠i = refl


rowAddF-eval-cong : {n m : ℕ} → (xs : Fin m → V) → (αss : Fin n → Fin m → F) → (p q i : Fin n) → eval xs (rowChangeF αss (λ j → (αss p j) +'_) q i) ≡ pointChangeV (λ i' → eval xs (αss i')) (eval xs (αss p) +_) q i
rowAddF-eval-cong xs αss p q i with (q ≟ i)
... | yes q=i = sum (λ j → ((αss p j) +' (αss i j)) ∙ (xs j))                    =⟨ sum-same (λ j → VS.scaleRDist V' (αss p j) (αss i j) (xs j)) ⟩
                sum (λ j → (αss p j) ∙ (xs j) + (αss i j) ∙ (xs j))              =⟨ =sym (sum-join (λ j → (αss p j) ∙ (xs j)) λ j → (αss i j) ∙ (xs j)) ⟩
                sum (λ j → (αss p j) ∙ (xs j)) + sum (λ j → (αss i j) ∙ (xs j)) □=
... | no  q≠i = refl



rowOp-Equation-cong : {n m : ℕ} → (xs : Fin m → V) → (αss : Fin n → Fin m → F) → (ys : Fin n → V)
                          → (ro : RowOperation n) → ((i : Fin n) → eval xs (αss i) ≡ ys i) → (i : Fin n) → eval xs (opOnScalars ro αss i) ≡ opOnVecs ro ys i
rowOp-Equation-cong _ _ _ Id αsxs=y                                 = αsxs=y
rowOp-Equation-cong {n} {m} xs αss ys (Scale β _ p subOp)  αsxs=y i =
                                        eval xs (rowChangeF αss' (λ j → β *_) p i)          =⟨ rowScaleF-eval-cong xs αss' β p i ⟩
                                        pointChangeV (λ i' → eval xs (αss' i')) (β ∙_) p i  =⟨ pointChangeV-same (λ i' → eval xs (αss' i')) ys' αsxs=y' (β ∙_) p i ⟩
                                        pointChangeV ys' (β ∙_) p i □=
                                             where ys'     = opOnVecs subOp ys
                                                   αss'    = opOnScalars subOp αss
                                                   αsxs=y' = rowOp-Equation-cong {n} {m} xs αss ys subOp αsxs=y 
rowOp-Equation-cong {n} {m} xs αss ys (Add p q _ subOp)    αsxs=y i =
                                        eval xs (rowChangeF αss' (λ j → (αss' p j) +'_) q i)               =⟨ rowAddF-eval-cong xs αss' p q i ⟩
                                        pointChangeV (λ i' → eval xs (αss' i')) (eval xs (αss' p) +_) q i  =⟨ pointChangeV-same (λ i' → eval xs (αss' i')) ys' αsxs=y' (eval xs (αss' p) +_) q i ⟩
                                        pointChangeV ys' (eval xs (αss' p) +_) q i                         =⟨ (αsxs=y' p) under (λ t → pointChangeV ys' (t +_) q i) ⟩
                                        pointChangeV ys' (ys' p +_) q i □=
                                             where ys'     = opOnVecs subOp ys
                                                   αss'    = opOnScalars subOp αss
                                                   αsxs=y' = rowOp-Equation-cong {n} {m} xs αss ys subOp αsxs=y 


rowSwap : {n : ℕ} → (p q : Fin n) → RowOperation n
rowSwap p q with p ≟ q
... | yes p=q = Id
... | no  p≠q = Scale (-' one) n1≠0 p
                (Add p q p≠q 
                (Scale (-' one) n1≠0 p
                (Add q p (≠sym p≠q)
                (Scale (-' one) n1≠0 p
                (Add p q p≠q Id)))))
                   where n1≠0 = FP.neg-nonzero (FD.one≠zero F')

rowSwap-scalars-p-to-q : {n m : ℕ} → (αss : Fin n → Fin m → F) → (p q : Fin n) → (j : Fin m) → opOnScalars (rowSwap p q) αss p j ≡ αss q j
                                                                                             × opOnScalars (rowSwap p q) αss q j ≡ αss p j
                                                                                             × ((i : Fin n) → ¬ i ≡ p → ¬ i ≡ q → opOnScalars (rowSwap p q) αss i j ≡ αss i j)
rowSwap-scalars-p-to-q {n} αss p q j with p ≟ q
... | yes p=q = (αss p j =⟨ p=q under (λ t → αss t j) ⟩ αss q j □=) ,
                (αss q j =⟨ (=sym p=q) under (λ t → αss t j) ⟩ αss p j □=) ,
                λ i i≠p i≠q → refl
... | no  p≠q = let n1≠0  = FP.neg-nonzero (FD.one≠zero F')
                    step1 = Add p q p≠q           Id
                    step2 = Scale (-' one) n1≠0 p step1
                    step3 = Add q p (≠sym p≠q)    step2
                    step4 = Scale (-' one) n1≠0 p step3
                    step5 = Add p q p≠q           step4
                    step6 = Scale (-' one) n1≠0 p step5                                   
                    αss1 = opOnScalars step1 αss
                    αss2 = opOnScalars step2 αss
                    αss3 = opOnScalars step3 αss
                    αss4 = opOnScalars step4 αss
                    αss5 = opOnScalars step5 αss
                    αss6 = opOnScalars step6 αss
                    side : (i : Fin n) → ¬ i ≡ p → ¬ i ≡ q → αss6 i j ≡ αss i j
                    side i i≠p i≠q = αss6 i j  =⟨ rowChangeF-ignore αss5 p i (≠sym i≠p) j ⟩
                                     αss5 i j  =⟨ rowChangeF-ignore αss4 q i (≠sym i≠q) j ⟩
                                     αss4 i j  =⟨ rowChangeF-ignore αss3 p i (≠sym i≠p) j ⟩
                                     αss3 i j  =⟨ rowChangeF-ignore αss2 p i (≠sym i≠p) j ⟩
                                     αss2 i j  =⟨ rowChangeF-ignore αss1 p i (≠sym i≠p) j ⟩
                                     αss1 i j  =⟨ rowChangeF-ignore αss  q i (≠sym i≠q) j ⟩
                                     αss i j  □=
                    a = αss p j
                    b = αss q j
                    p1 : αss1 p j ≡ a
                    p1 = rowChangeF-ignore αss q p (≠sym p≠q) j
                    q1 : αss1 q j ≡ a +' b
                    q1 = rowChangeF-see αss (λ j' x → (αss p j') +' x) q q refl j
                    p2 : αss2 p j ≡ -' a
                    p2 = αss2 p j              =⟨ rowChangeF-see αss1 (λ j' → -' one *_) p p refl j ⟩
                         (-' one) * (αss1 p j) =⟨ FP.negOne-Lmult (αss1 p j) ⟩
                         -' (αss1 p j)         =⟨ p1 under -'_ ⟩
                         -' a    □=
                    q2 : αss2 q j ≡ a +' b
                    q2 = αss2 q j =⟨ rowChangeF-ignore αss1 p q p≠q j ⟩
                         αss1 q j =⟨ q1 ⟩
                         a +' b  □=
                    p3 : αss3 p j ≡ b
                    p3 = αss3 p j =⟨ rowChangeF-see αss2 (λ j' → (αss2 q j') +'_) p p refl j ⟩
                         (αss2 q j) +' (αss2 p j) =⟨ p2 under (αss2 q j +'_) ⟩
                         (αss2 q j) +' -' a       =⟨ q2 under (_+' -' a) ⟩
                         (a +' b) +' -' a         =⟨ FD.addComm F' a b under (_+' -' a) ⟩
                         (b +' a) +' -' a         =⟨ =sym (FD.addAssoc F' b a (-' a)) ⟩
                         b +' (a +' -' a)         =⟨ FD.addRInv F' a under (b +'_) ⟩
                         b +' zero                =⟨ FD.zeroRNeut F' b ⟩
                         b □=
                    q3 : αss3 q j ≡ a +' b
                    q3 = αss3 q j =⟨ rowChangeF-ignore αss2 p q p≠q j ⟩
                         αss2 q j =⟨ q2 ⟩
                         a +' b □=
                    p4 : αss4 p j ≡ -' b
                    p4 = αss4 p j              =⟨ rowChangeF-see αss3 (λ j' → -' one *_) p p refl j ⟩
                         (-' one) * (αss3 p j) =⟨ FP.negOne-Lmult (αss3 p j) ⟩
                         -' αss3 p j           =⟨ p3 under -'_ ⟩
                         -' b □=
                    q4 : αss4 q j ≡ a +' b
                    q4 = αss4 q j =⟨ rowChangeF-ignore αss3 p q p≠q j ⟩
                         αss3 q j =⟨ q3 ⟩
                         a +' b □=
                    p5 : αss5 p j ≡ -' b
                    p5 = αss5 p j =⟨ rowChangeF-ignore αss4 q p (≠sym p≠q) j ⟩
                         αss4 p j =⟨ p4 ⟩
                         -' b □=
                    q5 : αss5 q j ≡ a
                    q5 = αss5 q j             =⟨ rowChangeF-see αss4 (λ j' → (αss4 p j') +'_) q q refl j ⟩
                         αss4 p j +' αss4 q j =⟨ p4 under (_+' αss4 q j) ⟩
                         -' b +' αss4 q j     =⟨ q4 under ( -' b +'_) ⟩
                         -' b +' (a +' b)     =⟨ FD.addComm F' a b under (-' b +'_) ⟩
                         -' b +' (b +' a)     =⟨ FD.addAssoc F' (-' b) b a ⟩
                         (-' b +' b) +' a     =⟨ FD.addLInv F' b under (_+' a) ⟩
                         zero +' a            =⟨ FD.zeroLNeut F' a ⟩
                         a  □=
                    p6 : αss6 p j ≡ b
                    p6 = αss6 p j              =⟨ rowChangeF-see αss5 (λ j' → (-' one) *_) p p refl j ⟩
                         (-' one) * (αss5 p j) =⟨ FP.negOne-Lmult (αss5 p j) ⟩
                         -' (αss5 p j)         =⟨ p5 under -'_ ⟩
                         -' (-' b)             =⟨ FP.doubleNeg b ⟩
                         b □=
                    q6 : αss6 q j ≡ a
                    q6 = αss6 q j =⟨ rowChangeF-ignore αss5 p q p≠q j ⟩
                         αss5 q j =⟨ q5 ⟩
                         a □=
                 in (p6 , q6 , side)
 


zvect-not-linIndep : {n : ℕ} → (vs : Fin n → V) → (i : Fin n) → vs i ≡ zvect → ¬ linIndep vs
zvect-not-linIndep {n} vs i vsi=0 livs = FD.one≠zero F' (one  =⟨ =sym αsi=1 ⟩
                                                         αs i =⟨ livs αs αsvs=0 i ⟩
                                                         zero □=)
                              where αs : Fin n → F
                                    αs j with j ≟ i
                                    ... | (yes j=i) = one
                                    ... | (no  j≠i) = zero
                                    αsi=1 : αs i ≡ one
                                    αsi=1 with i ≟ i
                                    ... | (yes _) = refl
                                    ... | (no i≠i)  = ⊥-elim (i≠i refl)
                                    αsvsi=0 : (j : Fin n) → (αs j) ∙ (vs j) ≡ zvect
                                    αsvsi=0 j with j ≟ i
                                    ... | (yes refl) = one ∙ (vs i) =⟨ (vsi=0 under one ∙_) ⟩
                                                       one ∙ zvect  =⟨ scale-zvect one ⟩
                                                       zvect □=
                                    ... | (no  _)    = zero-scale (vs j)
                                    αsvs=0 : eval vs αs ≡ zvect
                                    αsvs=0 = eval vs αs =⟨ sum-same αsvsi=0 ⟩
                                             sum {n} (λ i → zvect) =⟨ sum-zero {n} ⟩
                                             zvect □=






allZeroFrom : {n : ℕ} → ℕ → (Fin n → F) → Set k
allZeroFrom {n} i αs = (j : Fin n) → (ℕ.suc i) Data.Nat.≤ (toℕ j) → αs j ≡ zero


allZeroFrom-extend : {n : ℕ} → (p : ℕ) → (αs : Fin n → F) → (q : Fin n) → toℕ q ≡ ℕ.suc p → allZeroFrom (ℕ.suc p) αs → αs q ≡ zero → allZeroFrom p αs
allZeroFrom-extend p αs q q↦p+1 0fromp+1 αq=0 j p+2≤j with lessOrEqual (ℕ.suc p) (toℕ j) p+2≤j  
... | (inj₁ p+1≤j) = 0fromp+1 j p+1≤j
... | (inj₂ j↦p+1) = αs j =⟨ toℕ-injective j q j'=q' under αs ⟩
                     αs q =⟨ αq=0 ⟩
                     zero □=
               where j'=q' : toℕ j ≡ toℕ q
                     j'=q' = toℕ j   =⟨ =sym j↦p+1 ⟩
                             ℕ.suc p =⟨ =sym q↦p+1 ⟩
                             toℕ q □=

mostZero : {n : ℕ} → (Fin (ℕ.suc n) → F) → Set k
mostZero {n} αs = (j : Fin n) → αs (suc j) ≡ zero




elimCol1 : {n m : ℕ} → (vs : Fin (ℕ.suc n) → V) → (ws : Fin (ℕ.suc m) → V) → (αss : Fin (ℕ.suc n) → Fin (ℕ.suc m) → F) → ((i : Fin (ℕ.suc n)) → eval ws (αss i) ≡ vs i) → ¬ (αss fzero fzero ≡ zero)
                                 → linIndep vs → Σ ((Fin (ℕ.suc n) → V) × (Fin (ℕ.suc n) → Fin (ℕ.suc m) → F))
                                      (λ vwα → ((i : Fin (ℕ.suc n)) → eval ws ((proj₂ vwα) i) ≡ (proj₁ vwα) i) × mostZero (λ i → (proj₂ vwα) i fzero) × linIndep (proj₁ vwα))
elimCol1 {n} vs ws αss Σαsws=v α00≠0 livs = elimCol1rec vs ws αss Σαsws=v α00≠0 livs n (λ j n<j → ⊥-elim (tautology j n<j)) where
                    maxfin : (n : ℕ) → Fin (ℕ.suc n)
                    maxfin ℕ.zero    = fzero
                    maxfin (ℕ.suc n) = suc (maxfin n)
                    tautology : {n : ℕ} → (j : Fin (ℕ.suc n)) → n Data.Nat.< (toℕ j) → ⊥
                    tautology {ℕ.zero} fzero ()
                    tautology {ℕ.zero} (suc j) _ = stupid j
                                    where stupid : Fin ℕ.zero → ⊥
                                          stupid ()
                    tautology {ℕ.suc n} (suc j) (Data.Nat.s≤s pf) = tautology j pf
                    tautology {ℕ.suc n} fzero ()
                    elimCol1rec : {n m : ℕ} → (vs : Fin (ℕ.suc n) → V) → (ws : Fin (ℕ.suc m) → V) → (αss : Fin (ℕ.suc n) → Fin (ℕ.suc m) → F) → ((i : Fin (ℕ.suc n)) → eval ws (αss i) ≡ vs i) → ¬ (αss fzero fzero ≡ zero)
                                    → linIndep vs → (p : ℕ) → allZeroFrom p (λ i → αss i fzero) → Σ ((Fin (ℕ.suc n) → V) × (Fin (ℕ.suc n) → Fin (ℕ.suc m) → F))
                                      (λ vwα → ((i : Fin (ℕ.suc n)) → eval ws ((proj₂ vwα) i) ≡ (proj₁ vwα) i) × mostZero (λ i → (proj₂ vwα) i fzero) × linIndep (proj₁ vwα))
                    elimCol1rec {n} {m} vs ws αss Σαsws=v α00≠0 livs ℕ.zero  0from1 = (vs , αss) , (Σαsws=v , mostα0 , livs)
                                                  where mostα0 : mostZero (λ i → αss i fzero)
                                                        mostα0 i = 0from1 (suc i) (Data.Nat.s≤s Data.Nat.z≤n)
                    elimCol1rec {n} {m} vs ws αss Σαsws=v α00≠0 livs (ℕ.suc p) 0fromp+1 with (isInFin (ℕ.suc p) (ℕ.suc n))
                    ... | (inj₁ n+1≤p+1) = elimCol1rec vs ws αss Σαsws=v α00≠0 livs p (λ j p<j → ⊥-elim (finTooBig {ℕ.suc n} j (≤-trans n+1≤p+1 p<j)))
                                                     where ≤-trans : {a b c : ℕ} → a Data.Nat.≤ b → b Data.Nat.≤ c → a Data.Nat.≤ c
                                                           ≤-trans Data.Nat.z≤n _ = Data.Nat.z≤n
                                                           ≤-trans (Data.Nat.s≤s a≤b) (Data.Nat.s≤s b≤c) = Data.Nat.s≤s (≤-trans a≤b b≤c)
                                                           finTooBig : {n : ℕ} → (j : Fin n) → n Data.Nat.≤ toℕ j → ⊥
                                                           finTooBig fzero ()
                                                           finTooBig (suc j) (Data.Nat.s≤s pf) = finTooBig j pf
                    ... | (inj₂ (q , q↦p+1)) with isZero (αss q fzero)
                    ...        | (inj₁ αq=0) = elimCol1rec vs ws αss Σαsws=v α00≠0 livs p (allZeroFrom-extend p (λ i → αss i fzero) q q↦p+1 0fromp+1 αq=0)
                    ...        | (inj₂ αq≠0) = elimCol1rec vs' ws αss' Σαsws=v' α'00≠0 livs' p (allZeroFrom-extend p (λ i → αss' i fzero) q q↦p+1 0fromp' α'q=0)
                                       where 0≠suc : {n : ℕ} → ¬ ℕ.zero ≡ ℕ.suc n
                                             0≠suc ()
                                             0≠q : ¬ fzero ≡ q
                                             0≠q 0=q = 0≠suc (ℕ.zero           =⟨ refl ⟩
                                                             toℕ (fzero {n})   =⟨ 0=q under toℕ ⟩
                                                             toℕ q             =⟨ q↦p+1 ⟩
                                                             ℕ.suc p □=)
                                             α0 = αss fzero fzero
                                             αq = αss q fzero
                                             αq⁻¹ = αq ⁻¹[ αq≠0 ]
                                             n1   = -' one
                                             prod≠0 : ¬ (n1 * α0) * αq⁻¹ ≡ zero
                                             prod≠0 = FP.nonzero-split (n1 * α0) αq⁻¹
                                                                         (FP.nonzero-split n1 α0 (FP.neg-nonzero (FD.one≠zero F')) α00≠0)
                                                            (FP.inv-nonzero αq≠0)
                                             scaleOp = Scale ((n1 * α0) * αq⁻¹) prod≠0 q Id
                                             elimOp = Add fzero q 0≠q scaleOp
                                             vs' = opOnVecs elimOp vs
                                             αss' = opOnScalars elimOp αss
                                             Σαsws=v' = rowOp-Equation-cong ws αss vs elimOp Σαsws=v
                                             livs' = rowOp-LIndep-cong vs elimOp livs
                                             α'00≠0 : ¬ αss' fzero fzero ≡ zero
                                             α'00≠0 α'00=0 = α00≠0 (αss fzero fzero                     =⟨ =sym (rowChangeF-ignore αss q fzero (≠sym 0≠q) fzero) ⟩
                                                                    opOnScalars scaleOp αss fzero fzero =⟨ =sym (rowChangeF-ignore (opOnScalars scaleOp αss) q fzero (≠sym 0≠q) fzero) ⟩
                                                                    αss' fzero fzero                    =⟨ α'00=0 ⟩
                                                                    zero □=)
                                             α'q=0 : αss' q fzero ≡ zero
                                             α'q=0 = αss' q fzero                                                               =⟨ rowChangeF-see (opOnScalars scaleOp αss)
                                                                                                                                 (λ j → ((opOnScalars scaleOp αss) fzero j) +'_) q q refl fzero ⟩
                                                     (opOnScalars scaleOp αss) fzero fzero +' (opOnScalars scaleOp αss) q fzero =⟨ (rowChangeF-ignore αss q fzero (≠sym 0≠q) fzero)
                                                                                                                                         under _+' (opOnScalars scaleOp αss) q fzero ⟩
                                                     α0 +' (opOnScalars scaleOp αss) q fzero                                    =⟨ (rowChangeF-see αss (λ j → ((n1 * α0) * αq⁻¹) *_) q q refl fzero under α0 +'_) ⟩
                                                     α0 +' ((n1 * α0) * αq⁻¹) * αq  =⟨ =sym (FD.multAssoc F' (n1 * α0) αq⁻¹ αq) under α0 +'_ ⟩
                                                     α0 +' (n1 * α0) * (αq⁻¹ * αq)  =⟨ FD.multLInv F' αq αq≠0 under (λ t → α0 +' (n1 * α0) * t) ⟩
                                                     α0 +' (n1 * α0) * one          =⟨ FD.oneRNeut F' (n1 * α0) under α0 +'_ ⟩
                                                     α0 +' n1 * α0                  =⟨ =sym (FD.oneLNeut F' α0) under _+' n1 * α0 ⟩
                                                     one * α0 +' n1 * α0            =⟨ =sym (FD.RDist F' one n1 α0) ⟩
                                                     (one +' n1) * α0               =⟨ FD.addRInv F' one under _* α0 ⟩
                                                     zero * α0                      =⟨ FP.zero-LAbsorb α0 ⟩
                                                     zero □=
                                             0fromp' : allZeroFrom (ℕ.suc p) (λ i → αss' i fzero)
                                             0fromp' j p+2≤j = αss' j fzero =⟨ rowChangeF-ignore (opOnScalars scaleOp αss) q j (≠sym j≠q) fzero ⟩
                                                               opOnScalars scaleOp αss j fzero =⟨ rowChangeF-ignore αss q j (≠sym j≠q) fzero ⟩
                                                               αss  j fzero                    =⟨ 0fromp+1 j p+2≤j ⟩
                                                               zero □=
                                                                where p+1≠j' = biggerIsNotEqual (ℕ.suc p) (toℕ j) p+2≤j
                                                                      j≠q : ¬ j ≡ q
                                                                      j≠q j=q = p+1≠j' (ℕ.suc p =⟨ =sym q↦p+1 ⟩
                                                                                        toℕ q   =⟨ =sym j=q under toℕ ⟩
                                                                                        toℕ j □=)
                    



makeFirstNonzero : {n m : ℕ} → (vs : Fin (ℕ.suc n) → V) → (ws : Fin (ℕ.suc m) → V) → (αss : Fin (ℕ.suc n) → Fin (ℕ.suc m) → F) → ((i : Fin (ℕ.suc n)) → eval ws (αss i) ≡ vs i)
                                → Σ (Fin (ℕ.suc n)) (λ i → ¬ αss i fzero ≡ zero) → linIndep vs → Σ ((Fin (ℕ.suc n) → V) × (Fin (ℕ.suc n) → Fin (ℕ.suc m) → F))
                                      (λ vwα → ((i : Fin (ℕ.suc n)) → eval ws ((proj₂ vwα) i) ≡ (proj₁ vwα) i) × ¬ (proj₂ vwα) fzero fzero ≡ zero × linIndep (proj₁ vwα))
makeFirstNonzero vs ws αss Σαsws=v (p , αp≠0) livs = (vs' , αss') , (Σαsws=v' , α'0≠0 , livs')
                                       where rswap = rowSwap fzero p
                                             vs' = opOnVecs rswap vs
                                             αss' = opOnScalars rswap αss
                                             Σαsws=v' = rowOp-Equation-cong ws αss vs rswap Σαsws=v
                                             livs' = rowOp-LIndep-cong vs rswap livs
                                             α'0≠0 : ¬ αss' fzero fzero ≡ zero
                                             α'0≠0 α'0=0 = αp≠0 (αss p fzero       =⟨ =sym (proj₁ (rowSwap-scalars-p-to-q αss fzero p fzero)) ⟩
                                                                 αss' fzero fzero  =⟨ α'0=0 ⟩
                                                                 zero □=)


allZero : {n : ℕ} → (Fin n → F) → Set k
allZero {n} αs = (j : Fin n) → αs j ≡ zero


areAllZero : {n : ℕ} → (αs : Fin n → F) → (allZero αs) ⊎ (Σ (Fin n) (λ j → ¬ αs j ≡ zero)) 
areAllZero {ℕ.zero}  αs = inj₁ contradiction
                         where contradiction : (j : Fin ℕ.zero) → αs j ≡ zero
                               contradiction ()
areAllZero {ℕ.suc n} αs with (isZero (αs fzero)) 
...                     | (inj₂ α0≠0) = inj₂ (fzero , α0≠0)
...                     | (inj₁ α0=0) with (areAllZero (λ j → αs (suc j)))
...                                    | (inj₁ αs'=0) = inj₁ αs=0
                                                where αs=0 : allZero αs
                                                      αs=0 fzero   = α0=0
                                                      αs=0 (suc j) = αs'=0 j
...                                    | (inj₂ αi≠0*) = inj₂ (suc i , αi≠0)
                                                 where i    = proj₁ αi≠0*
                                                       αi≠0 = proj₂ αi≠0*






evenSmaller : {n m : ℕ} → (ℕ.suc m) Data.Nat.≤ n → m Data.Nat.≤ n
evenSmaller (Data.Nat.s≤s Data.Nat.z≤n)      = Data.Nat.z≤n
evenSmaller (Data.Nat.s≤s (Data.Nat.s≤s pf)) = Data.Nat.s≤s (evenSmaller (Data.Nat.s≤s pf))


too-many-linIndep : {n m : ℕ} → (vs : Fin n → V) → (ws : Fin m → V) → (αss : Fin n → Fin m → F) → ((i : Fin n) → eval ws (αss i) ≡ vs i) → m Data.Nat.< n → ¬ linIndep vs
too-many-linIndep {ℕ.zero}  {ℕ.zero}  vs ws αss Σαsws=v 0<0   livs = nothingSmallerThan0 0<0 
too-many-linIndep {ℕ.zero}  {ℕ.suc m} vs ws αss Σαsws=v m<0   livs = nothingSmallerThan0 m<0
too-many-linIndep {ℕ.suc n} {ℕ.zero}  vs ws αss Σαsws=v 0<sn  livs = zvect-not-linIndep vs fzero vs0=0 livs
                                                     where vs0=0 = vs fzero            =⟨ =sym (Σαsws=v fzero) ⟩
                                                                   eval ws (αss fzero) =⟨ refl ⟩
                                                                   zvect □=
too-many-linIndep {ℕ.suc n} {ℕ.suc m} vs ws αss Σαsws=v (Data.Nat.s≤s m<n) livs with (areAllZero (λ i → αss i fzero))
... | (inj₁ αssi0=0) = too-many-linIndep vs (λ j → ws (suc j)) (λ i j → αss i (suc j)) Σαs'ws=v (evenSmaller (Data.Nat.s≤s m<n)) livs
                           where Σαs'ws=v = λ i → eval (λ j → ws (suc j)) (λ j → αss i (suc j))      =⟨ refl ⟩
                                                  sum (λ j → (αss i (suc j)) ∙ (ws (suc j)))         =⟨ =sym (VS.zeroLNeut V' (sum (λ j → (αss i (suc j)) ∙ (ws (suc j))))) ⟩
                                                  zvect + sum (λ j → (αss i (suc j)) ∙ (ws (suc j)))                      =⟨ =sym (zero-scale (ws fzero)) under _+ (sum (λ j → (αss i (suc j)) ∙ (ws (suc j)))) ⟩
                                                  zero ∙ (ws fzero) + sum (λ j → (αss i (suc j)) ∙ (ws (suc j)))          =⟨ =sym (αssi0=0 i) under (λ t → t ∙ (ws fzero) + (sum (λ j → (αss i (suc j)) ∙ (ws (suc j))))) ⟩
                                                  (αss i fzero) ∙ (ws fzero) + sum (λ j → (αss i (suc j)) ∙ (ws (suc j))) =⟨ refl ⟩
                                                  eval ws (αss i)                                                         =⟨ Σαsws=v i ⟩
                                                  vs i □=
... | (inj₂ q,αq≠0)       = too-many-linIndep vs* ws* αss* Σαsws=v* m<n (remove-linIndep-cong vs'' livs'')
                 where afterSwap = makeFirstNonzero vs ws αss Σαsws=v q,αq≠0 livs
                       vs'       = proj₁ (proj₁ afterSwap)
                       αss'      = proj₂ (proj₁ afterSwap)
                       Σαsws=v'  = proj₁ (proj₂ afterSwap)
                       α'0≠0     = proj₁ (proj₂ (proj₂ afterSwap))
                       livs'     = proj₂ (proj₂ (proj₂ afterSwap))
                       afterElim = elimCol1 vs' ws αss' Σαsws=v' α'0≠0 livs'
                       vs''      = proj₁ (proj₁ afterElim)
                       αss''     = proj₂ (proj₁ afterElim)
                       Σαsws=v'' = proj₁ (proj₂ afterElim)
                       αi0=0     = proj₁ (proj₂ (proj₂ afterElim))
                       livs''    = proj₂ (proj₂ (proj₂ afterElim))
                       ws* = (λ j → ws (suc j))
                       vs* = (λ i → vs'' (suc i))
                       αss* = (λ i j → αss'' (suc i) (suc j))
                       Σαsws=v* : (i : Fin n) → eval ws* (αss* i) ≡ vs* i
                       Σαsws=v* i = eval ws* (αss* i)                                       =⟨ =sym (VS.zeroLNeut V' (eval ws* (αss* i))) ⟩
                                    zvect + eval ws* (αss* i)                               =⟨ =sym (zero-scale (ws fzero)) under _+ eval ws* (αss* i) ⟩
                                    zero ∙ (ws fzero) + eval  ws* (αss* i)                  =⟨ =sym (αi0=0 i) under (λ t → t ∙ (ws fzero) + eval ws* (αss* i)) ⟩
                                    (αss'' (suc i) fzero) ∙ (ws fzero) + eval ws* (αss* i)  =⟨ refl ⟩
                                    eval ws (αss'' (suc i))                                 =⟨ Σαsws=v'' (suc i) ⟩
                                    vs'' (suc i) □=




dimAtLeast : ∀{m} ℕ → Subspace {m} → Set (k ⊔ l ⊔ m)
dimAtLeast n U = Σ (Fin n → V) (λ xs → ((i : Fin n) → xs i ∈ U) × linIndep xs)


dimAtMost : ∀{m} ℕ → Subspace {m} → Set (k ⊔ l ⊔ m)
dimAtMost n U = Σ (Fin n → V) (λ xs → ((i : Fin n) → xs i ∈ U) × generator U xs)



dimEq : ∀{m} ℕ → Subspace {m} → Set (k ⊔ l ⊔ m)
dimEq n U = Σ (Fin n → V) (λ xs → ((i : Fin n) → xs i ∈ U) × basis U xs)



minimalGenerator : ∀{m} (n : ℕ) → (U : Subspace {m}) → (ys : Fin n → V) → generator U ys → (xs : Fin n → V)
                          → ((i : Fin n) → xs i ∈ U) → linIndep xs → linIndep ys
minimalGenerator ℕ.zero _ _ _ _ _ _ _ _ ()
minimalGenerator (ℕ.suc n) U ys genys xs xs∈U lixs αs αsys=0 with (areAllZero αs)
... | (inj₁ αs=0)   = αs=0
... | (inj₂ (i , αi≠0)) = ⊥-elim (too-many-linIndep xs ys' βss' βss'ys'=xs i'+r<n+1 lixs)
                            where i' = toℕ i
                                  r = proj₁ (n-minus-fin (ℕ.suc n) i)
                                  i'+r+1=n+1 : i' Data.Nat.+ (ℕ.suc r) ≡ (ℕ.suc n) 
                                  i'+r+1=n+1 = proj₂ (n-minus-fin (ℕ.suc n) i)
                                  sameType : ∀{lvl} {A : Set lvl} → (n m : ℕ) → m ≡ n → (Fin n → A) → Fin m → A
                                  sameType n .n refl xs = xs
                                  αs* = sameType (ℕ.suc n) (i' Data.Nat.+ (ℕ.suc r)) i'+r+1=n+1 αs
                                  i* = sameFin (ℕ.suc n) (i' Data.Nat.+ (ℕ.suc r)) i'+r+1=n+1 i
                                  sameFinAndType : ∀{lvl} {A : Set lvl} → (n  m : ℕ) → (m=n : m ≡ n) → (as : Fin n → A) → (j : Fin n)
                                                     → (sameType n m m=n as) (sameFin n m m=n j) ≡ as j
                                  sameFinAndType n m refl as j = refl
                                  sameFin-toℕ : (n m : ℕ) → (m=n : m ≡ n) → (j : Fin n) → toℕ (sameFin n m m=n j) ≡ toℕ j
                                  sameFin-toℕ n .n refl fzero   = refl
                                  sameFin-toℕ (ℕ.suc n) m refl (suc j) = sameFin-toℕ n n refl j under ℕ.suc
                                  cutAti : ∀{lvl} {A : Set lvl} → (Fin (ℕ.suc n) → A) → (Fin i' → A) × (Fin (ℕ.suc r) → A)
                                  cutAti as = splitVec {m = i'} (sameType (ℕ.suc n) (i' Data.Nat.+ (ℕ.suc r)) i'+r+1=n+1 as)
                                  pullInFronti : ∀{lvl} {A : Set lvl} → (Fin (ℕ.suc n) → A) → (Fin (ℕ.suc (i' Data.Nat.+ r)) → A)
                                  pullInFronti as fzero with (cutAti as)
                                  ... | (as₁ , as₂)  = as₂ fzero
                                  pullInFronti as (suc i) with (cutAti as)
                                  ... | (as₁ , as₂)  = concatVec (as₁ , tail as₂) i
                                  ys₁₂ = cutAti ys
                                  ys₁ = proj₁ ys₁₂
                                  ys₂ = proj₂ ys₁₂
                                  αs₁₂ = cutAti αs
                                  αs₁ = proj₁ αs₁₂
                                  αs₂ = proj₂ αs₁₂
                                  ys' : Fin (i' Data.Nat.+ r) → V
                                  ys' = concatVec (ys₁ , tail ys₂)
                                  αs' : Fin (i' Data.Nat.+ r) → F
                                  αs' = concatVec (αs₁ , tail αs₂)
                                  eval-cong : (βs : Fin (ℕ.suc n) → F) → (vs : Fin (ℕ.suc n) → V) → eval (pullInFronti vs) (pullInFronti βs) ≡ eval vs βs
                                  eval-cong βs vs = let (βs₁ , βs₂) = cutAti βs
                                                        (vs₁ , vs₂) = cutAti vs
                                                     in (βs₂ fzero) ∙ (vs₂ fzero) + eval (concatVec (vs₁ , tail vs₂)) (concatVec (βs₁ , tail βs₂))
                                                                  =⟨ =sym (sum-same (λ j → concat-combo vs₁ (tail vs₂) βs₁ (tail βs₂) j)) under (βs₂ fzero) ∙ (vs₂ fzero) +_ ⟩
                                                        (βs₂ fzero) ∙ (vs₂ fzero) + sum (concatVec ((λ j → (βs₁ j) ∙ (vs₁ j)) , (λ j → (βs₂ (suc j)) ∙ (vs₂ (suc j)))))
                                                                  =⟨ sum-concat-cong (λ j → (βs₁ j) ∙ (vs₁ j)) (λ j → (βs₂ (suc j)) ∙ (vs₂ (suc j))) under (βs₂ fzero) ∙ (vs₂ fzero) +_ ⟩
                                                        (βs₂ fzero) ∙ (vs₂ fzero) + (sum (λ j → (βs₁ j) ∙ (vs₁ j)) + sum (λ j → (βs₂ (suc j)) ∙ (vs₂ (suc j))))
                                                                  =⟨ VS.addAssoc V' ((βs₂ fzero) ∙ (vs₂ fzero)) (sum (λ j → (βs₁ j) ∙ (vs₁ j))) (sum (λ j → (βs₂ (suc j)) ∙ (vs₂ (suc j)))) ⟩
                                                        ((βs₂ fzero) ∙ (vs₂ fzero) + sum (λ j → (βs₁ j) ∙ (vs₁ j))) + sum (λ j → (βs₂ (suc j)) ∙ (vs₂ (suc j)))
                                                                  =⟨ VS.addComm V' ((βs₂ fzero) ∙ (vs₂ fzero)) (sum (λ j → (βs₁ j) ∙ (vs₁ j))) under _+ sum (λ j → (βs₂ (suc j)) ∙ (vs₂ (suc j))) ⟩
                                                        (sum (λ j → (βs₁ j) ∙ (vs₁ j)) + (βs₂ fzero) ∙ (vs₂ fzero)) + sum (λ j → (βs₂ (suc j)) ∙ (vs₂ (suc j)))
                                                                  =⟨ =sym (VS.addAssoc V' (sum (λ j → (βs₁ j) ∙ (vs₁ j))) ((βs₂ fzero) ∙ (vs₂ fzero)) (sum (λ j → (βs₂ (suc j)) ∙ (vs₂ (suc j))))) ⟩
                                                        sum (λ j → (βs₁ j) ∙ (vs₁ j)) + (sum (λ j → (βs₂ j) ∙ (vs₂ j)))
                                                                  =⟨ =sym (sum-concat-cong (λ j → (βs₁ j) ∙ (vs₁ j)) λ j → (βs₂ j) ∙ (vs₂ j)) ⟩
                                                        sum (concatVec ((λ j → (βs₁ j) ∙ (vs₁ j)) , (λ j → (βs₂ j) ∙ (vs₂ j))))
                                                                  =⟨ sum-same (λ j → concat-combo vs₁ vs₂ βs₁ βs₂ j) ⟩ 
                                                        eval (concatVec (vs₁ , vs₂)) (concatVec (βs₁ , βs₂))
                                                                  =⟨ sum-same (λ j → split-concat-cong {m = i'} βs' j under _∙ (concatVec (vs₁ , vs₂) j)) ⟩
                                                        eval (concatVec (vs₁ , vs₂)) (sameType (ℕ.suc n) (i' Data.Nat.+ (ℕ.suc r)) i'+r+1=n+1 βs)
                                                                  =⟨ sum-same (λ j → split-concat-cong {m = i'} vs' j under (βs' j ∙_)) ⟩
                                                        eval vs' βs'
                                                                  =⟨ same-eval (ℕ.suc n) (i' Data.Nat.+ (ℕ.suc r)) i'+r+1=n+1 βs vs ⟩        
                                                        eval vs βs □=
                                                          where βs' = sameType (ℕ.suc n) (i' Data.Nat.+ (ℕ.suc r)) i'+r+1=n+1 βs
                                                                vs' = sameType (ℕ.suc n) (i' Data.Nat.+ (ℕ.suc r)) i'+r+1=n+1 vs
                                                                same-eval : (n m : ℕ) → (m=n : m ≡ n) → (γs : Fin n → F) → (ws : Fin n → V)
                                                                         → eval (sameType n m m=n ws) (sameType n m m=n γs) ≡ eval ws γs
                                                                same-eval n m refl γs ws = refl
                                  αs'0≠0 : ¬ (αs₂ fzero ≡ zero)
                                  αs'0≠0 αs₂=0 = αi≠0 (αs i      =⟨ =sym ( sameFinAndType (ℕ.suc n) (i' Data.Nat.+ (ℕ.suc r)) i'+r+1=n+1 αs i) ⟩
                                                       αs* i*    =⟨ =sym (splitPoint {m = i'} i* (sameFin-toℕ (ℕ.suc n) (i' Data.Nat.+ (ℕ.suc r)) i'+r+1=n+1 i) αs*) ⟩
                                                       αs₂ fzero =⟨ αs₂=0 ⟩
                                                       zero □=)
                                  i'+r<n+1 : (i' Data.Nat.+ r) Data.Nat.< (ℕ.suc n)
                                  i'+r<n+1 = eq-≤-cong (ℕ.suc (i' Data.Nat.+ r)) (ℕ.suc n) (ℕ.suc n)
                                                           (ℕ.suc (i' Data.Nat.+ r) =⟨ =sym (+-suc-cong i' r) ⟩
                                                            i' Data.Nat.+ (ℕ.suc r) =⟨ i'+r+1=n+1 ⟩
                                                            ℕ.suc n □=) (n≤n (ℕ.suc n))
                                  βss : Fin (ℕ.suc n) → Fin (ℕ.suc n) → F
                                  βss i = proj₁ (genys (xs i) (xs∈U i))
                                  βss* : Fin (ℕ.suc n) → Fin (ℕ.suc (i' Data.Nat.+ r)) → F
                                  βss* j = pullInFronti (βss j)
                                  αs'0⁻¹ = -' (αs₂ fzero) ⁻¹[ αs'0≠0 ]
                                  βss' : Fin (ℕ.suc n) → Fin (i' Data.Nat.+ r) → F
                                  βss' i j = ((βss* i fzero) * αs'0⁻¹) * (αs' j) +' (βss* i (suc j))
                                  βss'ys'=xs : (i : Fin (ℕ.suc n)) → eval ys' (βss' i) ≡ xs i
                                  βss'ys'=xs i = sum (λ j → (((βss* i fzero) * αs'0⁻¹) * (αs' j) +' (βss* i (suc j))) ∙ (ys' j))
                                                              =⟨ sum-same (λ j → VS.scaleRDist V' (((βss* i fzero) * αs'0⁻¹) * (αs' j)) (βss* i (suc j)) (ys' j)) ⟩
                                                 sum (λ j → (((βss* i fzero) * αs'0⁻¹) * (αs' j)) ∙ (ys' j) + (βss* i (suc j)) ∙ (ys' j))
                                                              =⟨ =sym (sum-join (λ j → (((βss* i fzero) * αs'0⁻¹) * (αs' j)) ∙ (ys' j)) (λ j → (βss* i (suc j)) ∙ (ys' j))) ⟩
                                                 sum (λ j → (((βss* i fzero) * αs'0⁻¹) * (αs' j)) ∙ (ys' j)) + eval ys' (tail (βss* i))
                                                              =⟨ sum-same (λ j → VS.scaleMultAssoc V' ((βss* i fzero) * αs'0⁻¹) (αs' j) (ys' j)) under _+ eval ys' (tail (βss* i)) ⟩
                                                 sum (λ j → ((βss* i fzero) * αs'0⁻¹) ∙ (αs' j) ∙ (ys' j)) + eval ys' (tail (βss* i))
                                                              =⟨ =sym (sum-dist ((βss* i fzero) * αs'0⁻¹) (λ j → (αs' j) ∙ (ys' j))) under _+ eval ys' (tail (βss* i)) ⟩
                                                 ((βss* i fzero) * αs'0⁻¹) ∙ eval ys' αs' + eval ys' (tail (βss* i))
                                                              =⟨ =sym (VS.zeroLNeut V' (eval ys' αs')) under (λ t → ((βss* i fzero) * αs'0⁻¹) ∙ t + eval ys' (tail (βss* i))) ⟩
                                                 ((βss* i fzero) * αs'0⁻¹) ∙ (zvect + eval ys' αs') + eval ys' (tail (βss* i))
                                                              =⟨ =sym (VS.addLInv V' ((αs₂ fzero) ∙ (ys₂ fzero))) under (λ t → ((βss* i fzero) * αs'0⁻¹) ∙ (t + eval ys' αs') + eval ys' (tail (βss* i))) ⟩
                                                 ((βss* i fzero) * αs'0⁻¹) ∙ ((- (αs₂ fzero) ∙ (ys₂ fzero) + (αs₂ fzero) ∙ (ys₂ fzero)) + eval ys' αs') + eval ys' (tail (βss* i))
                                                              =⟨ =sym (VS.addAssoc V' (- (αs₂ fzero) ∙ (ys₂ fzero)) ((αs₂ fzero) ∙ (ys₂ fzero)) (eval ys' αs'))
                                                                                      under (λ t → ((βss* i fzero) * αs'0⁻¹) ∙ t + eval ys' (tail (βss* i))) ⟩
                                                 ((βss* i fzero) * αs'0⁻¹) ∙ (- (αs₂ fzero) ∙ (ys₂ fzero) + ((αs₂ fzero) ∙ (ys₂ fzero) + eval ys' αs')) + eval ys' (tail (βss* i))
                                                              =⟨ eval-cong αs ys under (λ t → ((βss* i fzero) * αs'0⁻¹) ∙ (- (αs₂ fzero) ∙ (ys₂ fzero) + t) + eval ys' (tail (βss* i))) ⟩
                                                 ((βss* i fzero) * αs'0⁻¹) ∙ (- (αs₂ fzero) ∙ (ys₂ fzero) + eval ys αs) + eval ys' (tail (βss* i))
                                                              =⟨ αsys=0 under (λ t → ((βss* i fzero) * αs'0⁻¹) ∙ (- (αs₂ fzero) ∙ (ys₂ fzero) + t) + eval ys' (tail (βss* i))) ⟩
                                                 ((βss* i fzero) * αs'0⁻¹) ∙ (- (αs₂ fzero) ∙ (ys₂ fzero) + zvect) + eval ys' (tail (βss* i))
                                                              =⟨ VS.zeroRNeut V' (- (αs₂ fzero) ∙ (ys₂ fzero)) under (λ t → ((βss* i fzero) * αs'0⁻¹) ∙ t + eval ys' (tail (βss* i)))  ⟩
                                                 ((βss* i fzero) * αs'0⁻¹) ∙ (- (αs₂ fzero) ∙ (ys₂ fzero)) + eval ys' (tail (βss* i))
                                                              =⟨ =sym (negOne-scale ((αs₂ fzero) ∙ (ys₂ fzero))) under (λ t → ((βss* i fzero) * αs'0⁻¹) ∙ t + eval ys' (tail (βss* i))) ⟩
                                                 ((βss* i fzero) * αs'0⁻¹) ∙ (-' one) ∙ (αs₂ fzero) ∙ (ys₂ fzero) + eval ys' (tail (βss* i))
                                                              =⟨ =sym (VS.scaleMultAssoc V' ((βss* i fzero) * αs'0⁻¹) (-' one) ((αs₂ fzero) ∙ (ys₂ fzero))) under _+ eval ys' (tail (βss* i)) ⟩
                                                 (((βss* i fzero) * αs'0⁻¹) * (-' one)) ∙ (αs₂ fzero) ∙ (ys₂ fzero) + eval ys' (tail (βss* i))
                                                              =⟨ =sym (FD.multAssoc F' (βss* i fzero) αs'0⁻¹ (-' one)) under (λ t → t ∙ (αs₂ fzero) ∙ (ys₂ fzero) + eval ys' (tail (βss* i))) ⟩
                                                 ((βss* i fzero) * (αs'0⁻¹ * (-' one))) ∙ (αs₂ fzero) ∙ (ys₂ fzero) + eval ys' (tail (βss* i))
                                                              =⟨ =sym (VS.scaleMultAssoc V' ((βss* i fzero) * (αs'0⁻¹ * (-' one))) (αs₂ fzero) (ys₂ fzero)) under _+ eval ys' (tail (βss* i)) ⟩
                                                 (((βss* i fzero) * (αs'0⁻¹ * (-' one))) * (αs₂ fzero)) ∙ (ys₂ fzero) + eval ys' (tail (βss* i))
                                                              =⟨ =sym (FD.multAssoc F' (βss* i fzero) (αs'0⁻¹ * (-' one)) (αs₂ fzero)) under (λ t → t ∙ (ys₂ fzero) + eval ys' (tail (βss* i))) ⟩
                                                 ((βss* i fzero) * ((αs'0⁻¹ * (-' one)) * (αs₂ fzero))) ∙ (ys₂ fzero) + eval ys' (tail (βss* i))
                                                              =⟨ FP.negOne-Rmult-n ((αs₂ fzero) ⁻¹[ αs'0≠0 ]) under (λ t →  ((βss* i fzero) * (t * (αs₂ fzero))) ∙ (ys₂ fzero) + eval ys' (tail (βss* i))) ⟩
                                                 ((βss* i fzero) * (((αs₂ fzero) ⁻¹[ αs'0≠0 ]) * (αs₂ fzero))) ∙ (ys₂ fzero) + eval ys' (tail (βss* i))
                                                              =⟨ FD.multLInv F' (αs₂ fzero) αs'0≠0 under (λ t → ((βss* i fzero) * t) ∙ (ys₂ fzero) + eval ys' (tail (βss* i))) ⟩
                                                 ((βss* i fzero) * one) ∙ (ys₂ fzero) + eval ys' (tail (βss* i))
                                                              =⟨ FD.oneRNeut F' (βss* i fzero) under (λ t → t ∙ (ys₂ fzero) + eval ys' (tail (βss* i))) ⟩
                                                 (βss* i fzero) ∙ (ys₂ fzero) + eval ys' (tail (βss* i))
                                                              =⟨ eval-cong (βss i) ys ⟩
                                                 eval ys (βss i) =⟨ proj₂ (genys (xs i) (xs∈U i)) ⟩
                                                 xs i □=


dimSandwich : ∀{m} (n : ℕ) → (U : Subspace {m}) → dimAtLeast n U → dimAtMost n U → dimEq n U
dimSandwich n U (xs , (xs∈U , lixs)) (ys , (ys∈U , genys)) = (ys , (ys∈U , (liys , genys)))
                                      where liys = minimalGenerator n U ys genys xs xs∈U lixs
                                                          



bilinear : (V → V → F) → Set (k ⊔ l)
bilinear q = leftAdd × rightAdd × leftScale × rightScale
     where ⟨_,_⟩ = q
           leftAdd    = (u v w : V) → ⟨ u + v , w ⟩ ≡ ⟨ u , w ⟩ +' ⟨ v , w ⟩
           rightAdd   = (u v w : V) → ⟨ u , v + w ⟩ ≡ ⟨ u , v ⟩ +' ⟨ u , w ⟩
           leftScale  = (v w : V) → (α : F) → ⟨ α ∙ v , w ⟩ ≡ α * ⟨ v , w ⟩
           rightScale = (v w : V) → (α : F) → ⟨ v , α ∙ w ⟩ ≡ α * ⟨ v , w ⟩

symmetric : (V → V → F) → Set (k ⊔ l)
symmetric q = (v w : V) →  q v w ≡ q w v


