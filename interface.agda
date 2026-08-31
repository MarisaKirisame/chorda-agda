{-# OPTIONS --safe #-}

-- The hypotheses the development is generic over. Modules take these as
-- parameters, so the whole development checks under --safe: every
-- theorem holds for any funext and any structure satisfying
-- VarInterface (instantiation.agda witnesses one, with Var = ℕ).

open import Data.Nat
open import Data.Sum
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable

open import iso public

Funext : Set₁
Funext = {A B : Set} -> {f g : A -> B} -> ((x : A) -> f x ≡ g x) -> f ≡ g

record VarInterface : Set₁ where
    field
        Constructor : Set
        Var : Set
        Cleft : Var ≅ (Var ⊎ Var)
        _≟v_ : (x y : Var) -> Dec (x ≡ y)
        Fresh : ℕ -> Var
        Fresh-inj : {x y : ℕ} -> Fresh x ≡ Fresh y -> x ≡ y
