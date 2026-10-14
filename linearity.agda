{-# OPTIONS --safe #-}

open import interface

module linearity (funext : Funext) (VI : VarInterface) where

open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; sym; trans; cong; subst)

open import core funext VI
open import existence funext VI using (equiv-constructor)
open import linearity-base funext VI public using (Linear)
open import linearity-base funext VI using (linearize; reflect-linear; pointwiseShape-substitution)
open import linearity-matching funext VI using (linear-match)

-- The one-sided linear-unification property underlying composition.
-- The term a may be nonlinear. Only b and the term being instantiated, p,
-- must be linear. This formulation uses core's independently factored pair
-- of most-general substitutions directly.
--
-- Related result: Thiemann, Hofbauer, Le Huitouze, and Waldmann, FSCD 2026,
-- Lemma 10, "Unification Involving Linear Terms".
-- https://doi.org/10.4230/LIPIcs.FSCD.2026.32
--
-- Proof: freshen the leaves of s₁[p]. Linearity of p lifts this to a
-- shape-preserving change of s₁; linearity of b completes another unifier.
-- Most-generality factors that change through s₁. Since constructor shape
-- was preserved, the linear instance witnesses linearity of s₁[p] itself.
mgu-linear : ∀ {a b s₁ s₂}
    -> s₁ , s₂ mgu a , b
    -> Linear b
    -> (p : Pattern) -> Linear p
    -> Linear (s₁ [ p ])
mgu-linear {a} {b} {s₁} {s₂} (MGU (Unify unifies) most) linear-b p linear-p
    with linearize (s₁ [ p ])
... | q , shape-q , linear-q with linear-match {p = p} linear-p s₁ q shape-q
... | t₁ , matches-p , images
    with linear-match {p = b} linear-b s₂ (t₁ [ a ])
        (subst (λ old -> equiv-constructor old (t₁ [ a ])) unifies
            (pointwiseShape-substitution images a))
... | t₂ , matches-b , _ with most t₁ t₂ (Unify (sym matches-b))
... | Prec factor factors , _ =
    reflect-linear factor (s₁ [ p ])
        (subst (equiv-constructor (s₁ [ p ])) (sym instance-q) shape-q)
        (subst Linear (sym instance-q) linear-q)
    where
    instance-q : factor [ s₁ [ p ] ] ≡ q
    instance-q = trans (sym (∘-eq factor s₁ p))
        (trans (cong (λ s -> s [ p ]) (sym factors)) matches-p)

-- Each variable occurs at most once in the left-hand side. No restriction
-- is imposed on how often a variable occurs in the right-hand side.
LeftLinear : Rule -> Set
LeftLinear (lhs ↦ rhs [ f ]) = Linear lhs

∘r-linear : ∀ {r₁ r₂ r}
    -> r₁ ∘r r₂ ≡ r
    -> LeftLinear r₁
    -> LeftLinear r₂
    -> LeftLinear r
∘r-linear (Comp {p1 = lhs} _ _ _ _ mgu) linear₁ linear₂ =
    mgu-linear mgu linear₂ lhs linear₁
