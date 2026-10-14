{-# OPTIONS --safe #-}

open import interface

module linearity-base (funext : Funext) (VI : VarInterface) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import core funext VI
open import existence funext VI using
  (equiv-constructor; equiv-constructors; ECX; ECK;
   equiv-constructor-trans; equiv-constructors-trans; X-inj;
   L-inj; R-inj; L-R-disjoint)

-- Occurrences retain their position, so two uses of a variable are distinct.
mutual
  data Occ (x : Var) : Pattern → Set where
    here : Occ x (X x)
    under : ∀ {k n ps} → Occs x ps → Occ x (K k n ps)

  data Occs (x : Var) : ∀ {n} → Vec Pattern n → Set where
    head : ∀ {n p} {ps : Vec Pattern n} → Occ x p → Occs x (p ∷ ps)
    tail : ∀ {n p} {ps : Vec Pattern n} → Occs x ps → Occs x (p ∷ ps)

Disjoint : ∀ {n} → Pattern → Vec Pattern n → Set
Disjoint p ps = ∀ {x} → Occ x p → Occs x ps → ⊥

-- Linearity means precisely that each variable occurs at most once.
mutual
  Linear : Pattern → Set
  Linear (X x) = ⊤
  Linear (K k n ps) = Linears ps

  Linears : ∀ {n} → Vec Pattern n → Set
  Linears [] = ⊤
  Linears (p ∷ ps) = Linear p × Linears ps × Disjoint p ps

mutual
  pointwiseShape-substitution : ∀ {s t} →
    (∀ x → equiv-constructor (s x) (t x)) →
    (p : Pattern) → equiv-constructor (s [ p ]) (t [ p ])
  pointwiseShape-substitution e (X x) = e x
  pointwiseShape-substitution e (K k n ps) =
    ECK (pointwiseShapes-substitution e ps)

  pointwiseShapes-substitution : ∀ {s t n} →
    (∀ x → equiv-constructor (s x) (t x)) →
    (ps : Vec Pattern n) → equiv-constructors (subs s ps) (subs t ps)
  pointwiseShapes-substitution e [] = tt
  pointwiseShapes-substitution e (p ∷ ps) =
    pointwiseShape-substitution e p , pointwiseShapes-substitution e ps

rename : (Var → Var) → Sub
rename f x = X (f x)

mutual
  rename-shape : (f : Var → Var) (p : Pattern) →
    equiv-constructor p (rename f [ p ])
  rename-shape f (X x) = ECX
  rename-shape f (K k n ps) = ECK (renames-shape f ps)

  renames-shape : ∀ {n} (f : Var → Var) (ps : Vec Pattern n) →
    equiv-constructors ps (subs (rename f) ps)
  renames-shape f [] = tt
  renames-shape f (p ∷ ps) = rename-shape f p , renames-shape f ps

mutual
  rename-occ : ∀ {x} (f : Var → Var) (p : Pattern) →
    Occ x (rename f [ p ]) → Σ Var (λ y → f y ≡ x × Occ y p)
  rename-occ f (X y) here = y , refl , here
  rename-occ f (K k n ps) (under o) with renames-occ f ps o
  ... | y , e , o′ = y , e , under o′

  renames-occ : ∀ {x n} (f : Var → Var) (ps : Vec Pattern n) →
    Occs x (subs (rename f) ps) → Σ Var (λ y → f y ≡ x × Occs y ps)
  renames-occ f (p ∷ ps) (head o) with rename-occ f p o
  ... | y , e , o′ = y , e , head o′
  renames-occ f (p ∷ ps) (tail o) with renames-occ f ps o
  ... | y , e , o′ = y , e , tail o′

rename-disjoint : ∀ {n} (f : Var → Var) →
  (∀ {x y} → f x ≡ f y → x ≡ y) →
  (p : Pattern) (ps : Vec Pattern n) → Disjoint p ps →
  Disjoint (rename f [ p ]) (subs (rename f) ps)
rename-disjoint f inj p ps d o os
  with rename-occ f p o | renames-occ f ps os
... | x , e , ox | y , e′ , oy =
  d ox (subst (λ z → Occs z ps) (sym (inj (trans e (sym e′)))) oy)

mutual
  rename-linear : (f : Var → Var) →
    (∀ {x y} → f x ≡ f y → x ≡ y) →
    (p : Pattern) → Linear p → Linear (rename f [ p ])
  rename-linear f inj (X x) l = tt
  rename-linear f inj (K k n ps) l = renames-linear f inj ps l

  renames-linear : ∀ {n} (f : Var → Var) →
    (∀ {x y} → f x ≡ f y → x ≡ y) →
    (ps : Vec Pattern n) → Linears ps → Linears (subs (rename f) ps)
  renames-linear f inj [] l = tt
  renames-linear f inj (p ∷ ps) (l , ls , d) =
    rename-linear f inj p l , renames-linear f inj ps ls ,
    rename-disjoint f inj p ps d

left-right-disjoint : ∀ {n} (p : Pattern) (ps : Vec Pattern n) →
  Disjoint (rename L [ p ]) (subs (rename R) ps)
left-right-disjoint p ps o os with rename-occ L p o | renames-occ R ps os
... | x , e , ox | y , e′ , oy = L-R-disjoint (trans e (sym e′))

-- Give every leaf a different variable, without changing constructors.
mutual
  linearize : (p : Pattern) →
    Σ Pattern (λ q → equiv-constructor p q × Linear q)
  linearize (X x) = X (Fresh zero) , ECX , tt
  linearize (K k n ps) with linearizes ps
  ... | qs , e , l = K k n qs , ECK e , l

  linearizes : ∀ {n} (ps : Vec Pattern n) →
    Σ (Vec Pattern n) (λ qs → equiv-constructors ps qs × Linears qs)
  linearizes [] = [] , tt , tt
  linearizes (p ∷ ps) with linearize p | linearizes ps
  ... | q , e , l | qs , es , ls =
    (rename L [ q ] ∷ subs (rename R) qs) ,
    (equiv-constructor-trans e (rename-shape L q) ,
     equiv-constructors-trans es (renames-shape R qs)) ,
    rename-linear L L-inj q l , renames-linear R R-inj qs ls ,
    left-right-disjoint q qs

shape-variable : ∀ {x p} → equiv-constructor (X x) p →
  Σ Var (λ y → p ≡ X y)
shape-variable ECX = _ , refl

mutual
  shape-occ : ∀ {x} (s : Sub) (p : Pattern) →
    equiv-constructor p (s [ p ]) → Occ x p →
    Σ Var (λ y → s x ≡ X y × Occ y (s [ p ]))
  shape-occ s (X x) e here with shape-variable e
  ... | y , eq = y , eq , subst (Occ y) (sym eq) here
  shape-occ s (K k n ps) (ECK es) (under o) with shapes-occ s ps es o
  ... | y , e , o′ = y , e , under o′

  shapes-occ : ∀ {x n} (s : Sub) (ps : Vec Pattern n) →
    equiv-constructors ps (subs s ps) → Occs x ps →
    Σ Var (λ y → s x ≡ X y × Occs y (subs s ps))
  shapes-occ s (p ∷ ps) (e , es) (head o) with shape-occ s p e o
  ... | y , eq , o′ = y , eq , head o′
  shapes-occ s (p ∷ ps) (e , es) (tail o) with shapes-occ s ps es o
  ... | y , eq , o′ = y , eq , tail o′

reflect-disjoint : ∀ {n} (s : Sub) (p : Pattern) (ps : Vec Pattern n) →
  equiv-constructor p (s [ p ]) → equiv-constructors ps (subs s ps) →
  Disjoint (s [ p ]) (subs s ps) → Disjoint p ps
reflect-disjoint s p ps e es d o os with shape-occ s p e o | shapes-occ s ps es os
... | x , eq , ox | y , eq′ , oy =
  d ox (subst (λ z → Occs z (subs s ps)) (sym (X-inj (trans (sym eq) eq′))) oy)

-- A shape-preserving instance cannot remove a repeated variable.
mutual
  reflect-linear : (s : Sub) (p : Pattern) →
    equiv-constructor p (s [ p ]) → Linear (s [ p ]) → Linear p
  reflect-linear s (X x) e l = tt
  reflect-linear s (K k n ps) (ECK es) l = reflect-linears s ps es l

  reflect-linears : ∀ {n} (s : Sub) (ps : Vec Pattern n) →
    equiv-constructors ps (subs s ps) → Linears (subs s ps) → Linears ps
  reflect-linears s [] e l = tt
  reflect-linears s (p ∷ ps) (e , es) (l , ls , d) =
    reflect-linear s p e l , reflect-linears s ps es ls ,
    reflect-disjoint s p ps e es d
