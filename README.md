# HoTT in Idris

This repository will contain a formalization of some of the content in the Homotopy Type Theory textbook in Idris.
Of course, univalence is inconsistent with the brand of pattern-matching that Idris has (which implies the uniqueness of identity proofs, axiom K, etc.), so we will have to be careful never to match on `Refl`.
According to [Pattern-Matching without K](https://dl.acm.org/doi/10.1145/2692915.2628139), this is only an issue when pattern-matching on `Refl` produces a unification problem shaped like `x = x`, but just to be safe, we will use eliminators (i.e. J) throughout instead.

* TypeTheory: Chapter 1
* Homotopy: Chapter 2 - Sections 2.1 to 2.4
* TypeFormers: Chapter 2 - Sections 2.5 to 2.15
* FunExt: Sections 2.9, 4.9, and 6.3 (TODO)
* SetsLogic: Chapter 3
* Equivalence: Second half of Section 2.4; Chapter 4

## Program holes

These are places where the type has been declared with no implementation given, or filled in with `believe_me`.

### Axioms

* FunExt.fun_refl

### Higher inductive types

* FunExt.Interval: seg, seg_comp
* SetsLogic.Squash: squash

### Partially-completed proofs

* Homotopy.EckmannHilton
* TypeFormers.ap_uniq (will not do)
* SetsLogic.ACqinvCP
* SetsLogic.contrFamilyCentre: fg

## TODOs

Some of these have been partially begun and show up as program holes in the above.

* Section 2.1: Theorem 2.1.6 (EckmannHilton)
* Sections 2.10, 2.12, 2.13
* Section 3.8: Lemma 3.8.2 (ACqinvCP)
* Section 3.11: Lemma 3.11.9 (ii)/Exercise 3.20 (contrFamilyCentre)
* Section 4.3: Theorem 4.3.2
* Section 4.4: Corollary 4.4.6

These I do not plan on ever doing.

* Section 2.11: Theorems 2.11.3 to 2.11.5
* Section 2.14
* Section 2.15: Equations 2.15.9 to 2.15.11
* Sections 4.1 to 4.2, 4.6, 4.8
* Section 4.7: Theorems 4.7.1 to 4.7.4
* Section 4.9: Definition 4.9.1 to Theorem 4.9.4

## Bonus content
* PLFI: [Programming Language Foundations in Agda](https://plfa.github.io/), but in Idris. This only contains some of the sections I find interesting.
