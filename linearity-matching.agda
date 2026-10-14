{-# OPTIONS --safe #-}

open import interface

module linearity-matching (funext : Funext) (VI : VarInterface) where

open import Data.Empty using (⊥-elim)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Data.Vec using (Vec; []; _∷_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; trans)
open import Relation.Nullary.Decidable using (Dec; yes; no)

open import core funext VI
open import existence funext VI
  using (equiv-constructor; equiv-constructors; ECX; ECK)
open import linearity-base funext VI
  using (Occ; Occs; here; under; head; tail; Linear; Linears; Disjoint)

mutual
  occurs? : (x : Var) → (p : Pattern) → Dec (Occ x p)
  occurs? x (X y) with x ≟v y
  ... | yes refl = yes here
  ... | no neq = no (λ { here → neq refl })
  occurs? x (K k n ps) with occurs-in? x ps
  ... | yes occ = yes (under occ)
  ... | no absent = no (λ { (under occ) → absent occ })

  occurs-in? : ∀ {n} → (x : Var) → (ps : Vec Pattern n) → Dec (Occs x ps)
  occurs-in? x [] = no (λ ())
  occurs-in? x (p ∷ ps) with occurs? x p
  ... | yes occ = yes (head occ)
  ... | no absent with occurs-in? x ps
  ...   | yes occ = yes (tail occ)
  ...   | no absent-tail = no (λ { (head occ) → absent occ
                                ; (tail occ) → absent-tail occ })

mutual
  shape-refl : (p : Pattern) → equiv-constructor p p
  shape-refl (X x) = ECX
  shape-refl (K k n ps) = ECK (shapes-refl ps)

  shapes-refl : ∀ {n} → (ps : Vec Pattern n) → equiv-constructors ps ps
  shapes-refl [] = tt
  shapes-refl (p ∷ ps) = shape-refl p , shapes-refl ps

-- A substitution only depends on its values at occurring variables.
mutual
  subst-agrees : ∀ {s t} → (p : Pattern)
    → (∀ {x} → Occ x p → s x ≡ t x) → s [ p ] ≡ t [ p ]
  subst-agrees (X x) agree = agree here
  subst-agrees (K k n ps) agree =
    cong (K k n) (substs-agree ps (λ occ → agree (under occ)))

  substs-agree : ∀ {s t n} → (ps : Vec Pattern n)
    → (∀ {x} → Occs x ps → s x ≡ t x) → subs s ps ≡ subs t ps
  substs-agree [] agree = refl
  substs-agree (p ∷ ps) agree = cong₂ _∷_
    (subst-agrees p (λ occ → agree (head occ)))
    (substs-agree ps (λ occ → agree (tail occ)))

update : Sub → Var → Pattern → Sub
update s x q y with y ≟v x
... | yes _ = q
... | no _ = s y

update-here : (s : Sub) → (x : Var) → (q : Pattern) → update s x q x ≡ q
update-here s x q with x ≟v x
... | yes _ = refl
... | no neq = ⊥-elim (neq refl)

update-shape : (s : Sub) → (x : Var) → (q : Pattern)
  → equiv-constructor (s x) q
  → (y : Var) → equiv-constructor (s y) (update s x q y)
update-shape s x q shape y with y ≟v x
... | yes refl = shape
... | no _ = shape-refl (s y)

-- Merge independently obtained matches; linearity makes their supports disjoint.
merge : Pattern → Sub → Sub → Sub
merge p s t x with occurs? x p
... | yes _ = s x
... | no _ = t x

merge-left : (p : Pattern) → (s t : Sub)
  → ∀ {x} → Occ x p → merge p s t x ≡ s x
merge-left p s t {x} occ with occurs? x p
... | yes _ = refl
... | no absent = ⊥-elim (absent occ)

merge-right : ∀ {n} → (p : Pattern) → (ps : Vec Pattern n)
  → Disjoint p ps → (s t : Sub)
  → ∀ {x} → Occs x ps → merge p s t x ≡ t x
merge-right p ps disjoint s t {x} occ with occurs? x p
... | yes occurs = ⊥-elim (disjoint occurs occ)
... | no _ = refl

merge-shape : (p : Pattern) → (s t u : Sub)
  → ((x : Var) → equiv-constructor (s x) (t x))
  → ((x : Var) → equiv-constructor (s x) (u x))
  → (x : Var) → equiv-constructor (s x) (merge p t u x)
merge-shape p s t u st su x with occurs? x p
... | yes _ = st x
... | no _ = su x

mutual
  -- A linear pattern matches any relabelling of the leaves of one of its
  -- instances. Every substitution image retains its constructor skeleton.
  linear-match : ∀ {p} → Linear p → (s : Sub) → (q : Pattern)
    → equiv-constructor (s [ p ]) q
    → Σ Sub (λ t → t [ p ] ≡ q × ((x : Var) → equiv-constructor (s x) (t x)))
  linear-match {X x} linear s q shape =
    update s x q , update-here s x q , update-shape s x q shape
  linear-match {K k n ps} linear s (K .k .n qs) (ECK shapes)
    with linear-matches linear s qs shapes
  ... | t , matched , same-shapes = t , cong (K k n) matched , same-shapes

  linear-matches : ∀ {n} {ps : Vec Pattern n} → Linears ps
    → (s : Sub) → (qs : Vec Pattern n) → equiv-constructors (subs s ps) qs
    → Σ Sub (λ t → subs t ps ≡ qs × ((x : Var) → equiv-constructor (s x) (t x)))
  linear-matches {ps = []} linear s [] shapes = s , refl , λ x → shape-refl (s x)
  linear-matches {ps = p ∷ ps} (lp , lps , disjoint) s (q ∷ qs) (shape , shapes)
    with linear-match {p = p} lp s q shape | linear-matches {ps = ps} lps s qs shapes
  ... | t , matched-head , st | u , matched-tail , su =
    merge p t u , cong₂ _∷_
      (trans (subst-agrees p (merge-left p t u)) matched-head)
      (trans (substs-agree ps (merge-right p ps disjoint t u)) matched-tail) ,
      merge-shape p s t u st su
