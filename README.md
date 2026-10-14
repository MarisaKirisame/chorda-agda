# Mechanization for Incremental Live Programming via Shortcut Memoization

This directory contains the Agda mechanization of the theorems in "Incremental Live Programming via Shortcut Memoization". To check the proofs, an installation of [Agda](https://wiki.portal.chalmers.se/agda/pmwiki.php?n=Main.Download) is required. The proofs are known to load cleanly under Agda `2.7.0.1` with agda-stdlib `2.1.1`.

Once installed, `agda --safe all.agda` in the top-level directory will cause Agda to check all the proofs. Every module is `--safe`: the development uses no postulates, rewrite rules, or termination pragmas.

## Contents

- [core.agda](./core.agda) contains definitions 2.1 - 2.5 and 2.8
- [compatibility.agda](compatibility.agda) contains Theorem 2.6 (Compatibility of Rule Composition)
- [existence.agda](./existence.agda) contains Theorem 2.7 (Shortcut Existence)
- [validity.agda](./validity.agda) contains Theorem 2.9 (Shortcut Validity)
- [linearity.agda](./linearity.agda) proves that composition preserves left-linearity
- [linearity-base.agda](./linearity-base.agda) defines variable occurrences and linear patterns, with shape-preserving linearization and reflection lemmas
- [linearity-matching.agda](./linearity-matching.agda) proves shape-preserving matching for linear patterns
- [interface.agda](./interface.agda) contains the assumptions the development is parameterized over
- [instantiation.agda](./instantiation.agda) contains a concrete model of those assumptions

## Assumptions

Every module takes two parameters, declared in `interface.agda`:

- `Funext`: function extensionality, a standard axiom which is not provable in the core type theory of Agda.
- `VarInterface`: `Constructor : Set`, so that the development is generic over sets of constructors, and `Var : Set` with a few properties, such as decidability of equality, an injection from the naturals, and a bijection between `Var` and `Var + Var`. We wish to remain generic over infinite sets of variables, but these assumptions are satisfiable: `instantiation.agda` constructs `ℕ-interface`, a model with `Var = ℕ`, itself checked under `--safe`.

Each theorem therefore holds for every model of `VarInterface`, assuming function extensionality. To use a theorem at a concrete instance, apply its module: `open import existence fe ℕ-interface`, given a proof `fe : Funext`.

## Linearity of composition

`Linear p` means that each variable occurs at most once in `p`. A rule is
`LeftLinear` when its left-hand side is linear; its right-hand side may duplicate
or discard variables. The theorem `∘r-linear` proves that every composition of
two left-linear rules is left-linear, using the existing composition and MGU
definitions without additional assumptions.

The supporting theorem `mgu-linear` says that, for an MGU pair `(s₁, s₂)` of
`a` and a linear `b`, applying `s₁` to any linear pattern preserves linearity.
This is the pair-substitution counterpart of Lemma 10 in
[Thiemann et al., FSCD 2026](https://doi.org/10.4230/LIPIcs.FSCD.2026.32).
The proof here uses shape-preserving linearization and matching, then the MGU
factorization property; it works directly with the two independently factored
substitutions in `core.agda`. The final step needs shape preservation because
an arbitrary substitution can erase repeated variables by replacing them with
ground terms. All supporting lemmas are checked by `all.agda`.
