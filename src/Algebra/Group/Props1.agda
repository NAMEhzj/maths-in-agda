--library=maths

open import Base.Equivalence hiding (_∘_)
open import Algebra.Group.Core

module Algebra.Group.Props1 {l} (G : Set l) (G' : Group G) where

open Group G'

LNeut-unique : (a : G) → (b : G) → a ∘ b ≡ b → a ≡ e
LNeut-unique a b aLN = a              =⟨ =sym (RNeut a) ⟩
                       a ∘ e          =⟨ =sym (RInv b) under a ∘_ ⟩
                       a ∘ (b ∘ b ⁻¹) =⟨ =sym (Assoc a b (b ⁻¹)) ⟩
                       (a ∘ b) ∘ b ⁻¹ =⟨ aLN under _∘ b ⁻¹ ⟩
                       b ∘ b ⁻¹       =⟨ RInv b ⟩ 
                       e □=

RNeut-unique : (a : G) → (b : G) → b ∘ a ≡ b → a ≡ e
RNeut-unique a b aRN = a              =⟨ =sym (LNeut a) ⟩
                       e ∘ a          =⟨ =sym (LInv b) under _∘ a ⟩
                       (b ⁻¹ ∘ b) ∘ a =⟨ Assoc (b ⁻¹) b a ⟩
                       b ⁻¹ ∘ (b ∘ a) =⟨ aRN under b ⁻¹ ∘_ ⟩
                       b ⁻¹ ∘ b       =⟨ LInv b ⟩ 
                       e □=


LInv-unique : (a b : G) → a ∘ b ≡ e → a ≡ b ⁻¹
LInv-unique a b ab=e = a              =⟨ =sym (RNeut a) ⟩
                       a ∘ e          =⟨ =sym (RInv b) under a ∘_ ⟩
                       a ∘ (b ∘ b ⁻¹) =⟨ =sym (Assoc a b (b ⁻¹)) ⟩
                       (a ∘ b) ∘ b ⁻¹ =⟨ ab=e under _∘ b ⁻¹ ⟩
                       e ∘ b ⁻¹       =⟨ LNeut (b ⁻¹) ⟩
                       b ⁻¹ □=



RInv-unique : (a b : G) → a ∘ b ≡ e → b ≡ a ⁻¹
RInv-unique a b ab=e = b              =⟨ =sym (LNeut b) ⟩
                       e ∘ b          =⟨ =sym (LInv a) under _∘ b ⟩
                       (a ⁻¹ ∘ a) ∘ b =⟨ Assoc (a ⁻¹) a b ⟩
                       a ⁻¹ ∘ (a ∘ b) =⟨ ab=e under a ⁻¹ ∘_ ⟩
                       a ⁻¹ ∘ e       =⟨ RNeut (a ⁻¹) ⟩
                       a ⁻¹ □=

neutInv : e ⁻¹ ≡ e
neutInv = =sym (LInv-unique e e (LNeut e))

doubleInv : (a : G) → (a ⁻¹) ⁻¹ ≡ a
doubleInv a = =sym (LInv-unique a (a ⁻¹) (RInv a))


∘-inv : (a b : G) → (a ∘ b) ⁻¹ ≡ (b ⁻¹) ∘ (a ⁻¹)
∘-inv a b = =sym (RInv-unique (a ∘ b) (b ⁻¹ ∘ a ⁻¹) ((a ∘ b) ∘ (b ⁻¹ ∘ a ⁻¹) =⟨ =sym (Assoc (a ∘ b) (b ⁻¹) (a ⁻¹)) ⟩
                                                     ((a ∘ b) ∘ b ⁻¹) ∘ a ⁻¹ =⟨ Assoc a b (b ⁻¹) under _∘ a ⁻¹ ⟩
                                                     (a ∘ (b ∘ b ⁻¹)) ∘ a ⁻¹ =⟨ RInv b under (λ t → (a ∘ t) ∘ a ⁻¹) ⟩
                                                     (a ∘ e) ∘ a ⁻¹          =⟨ RNeut a under _∘ a ⁻¹ ⟩
                                                     a ∘ a ⁻¹                =⟨ RInv a ⟩
                                                     e                       □=))
