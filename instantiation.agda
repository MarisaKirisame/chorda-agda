{-# OPTIONS --safe #-}

-- Witnesses, checked under --safe, that every postulate in core.agda
-- except funext is satisfiable with Var = Constructor = ℕ. funext is
-- independent of Agda's core type theory and remains an axiom.

open import Data.Nat
open import Data.Nat.Properties using (_≟_)
open import Data.Sum
open import Data.Sum.Properties using (inj₁-injective; inj₂-injective)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable

open import interface

-- ℕ ≅ ℕ ⊎ ℕ by the even/odd split.
to2 : ℕ -> ℕ ⊎ ℕ
to2 zero = inj₁ zero
to2 (suc zero) = inj₂ zero
to2 (suc (suc n)) with to2 n
... | inj₁ m = inj₁ (suc m)
... | inj₂ m = inj₂ (suc m)

from2 : ℕ ⊎ ℕ -> ℕ
from2 (inj₁ zero) = zero
from2 (inj₁ (suc m)) = suc (suc (from2 (inj₁ m)))
from2 (inj₂ zero) = suc zero
from2 (inj₂ (suc m)) = suc (suc (from2 (inj₂ m)))

fromto2 : (n : ℕ) -> from2 (to2 n) ≡ n
fromto2 zero = refl
fromto2 (suc zero) = refl
fromto2 (suc (suc n)) with to2 n in eq
... | inj₁ m = cong (λ k -> suc (suc k)) (trans (cong from2 (sym eq)) (fromto2 n))
... | inj₂ m = cong (λ k -> suc (suc k)) (trans (cong from2 (sym eq)) (fromto2 n))

tofrom2 : (b : ℕ ⊎ ℕ) -> to2 (from2 b) ≡ b
tofrom2 (inj₁ zero) = refl
tofrom2 (inj₁ (suc m)) with to2 (from2 (inj₁ m)) | tofrom2 (inj₁ m)
... | inj₁ m' | ih = cong (λ z -> inj₁ (suc z)) (inj₁-injective ih)
... | inj₂ m' | ()
tofrom2 (inj₂ zero) = refl
tofrom2 (inj₂ (suc m)) with to2 (from2 (inj₂ m)) | tofrom2 (inj₂ m)
... | inj₂ m' | ih = cong (λ z -> inj₂ (suc z)) (inj₂-injective ih)
... | inj₁ m' | ()

Constructorℕ : Set
Constructorℕ = ℕ

Varℕ : Set
Varℕ = ℕ

Cleftℕ : ℕ ≅ (ℕ ⊎ ℕ)
Cleftℕ = record
    { to = to2
    ; from = from2
    ; fromto = λ {a} -> fromto2 a
    ; tofrom = λ {b} -> tofrom2 b
    }

_≟vℕ_ : (x y : ℕ) -> Dec (x ≡ y)
_≟vℕ_ = _≟_

Freshℕ : ℕ -> ℕ
Freshℕ n = n

Freshℕ-inj : {x y : ℕ} -> Freshℕ x ≡ Freshℕ y -> x ≡ y
Freshℕ-inj eq = eq

ℕ-interface : VarInterface
ℕ-interface = record
    { Constructor = Constructorℕ
    ; Var = Varℕ
    ; Cleft = Cleftℕ
    ; _≟v_ = _≟vℕ_
    ; Fresh = Freshℕ
    ; Fresh-inj = Freshℕ-inj
    }
