{-# OPTIONS --safe #-}

open import Relation.Binary.PropositionalEquality

record _≅_ (A B : Set) : Set where
    field
        to : A -> B
        from : B -> A
        fromto : ∀{a} -> from (to a) ≡ a
        tofrom : ∀{b} -> to (from b) ≡ b
