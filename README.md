# HoTT in Idris

This repository will contain a formalization of some of the content in the Homotopy Type Theory textbook in Idris.
Of course, univalence is inconsistent with the brand of pattern-matching that Idris has (which implies the uniqueness of identity proofs, axiom K, etc.), so we will have to be careful never to match on `Refl`.

* TypeTheory: Chapter 1
* Homotopy: Chapter 2 - Sections 2.1 to 2.4
* TypeFormers: Chapter 2 - Sections 2.5 to 2.11
* FunExt: Sections 2.9, 4.9, and 6.3 (TODO)
* Equivalence: Second half of Section 2.4; Chapter 4 (TODO)

## Program holes

### Axioms

* FunExt.fun_refl

### Higher inductive types

* FunExt.Interval: seg, seg_comp
* SetsLogic.Squash: squash

### Partially-completed proofs

* Homotopy.EckmannHilton
* TypeFormers.ap_inv: ap_comp, ap_uniq
* SetsLogic.ACqinvCP
* SetsLogic.contrFamilyCentre: fg

## TODOs

Some of these have been partially begun and show up as program holes in the above.

* Section 2.1: Theorem 2.1.6 (EckmannHilton)
* Section 2.11: Theorem 2.11.1 (ap_inv)
* Section 2.11: Theorems 2.11.3 to 2.11.5
* Sections 2.10, 2.12 to 2.15
* Section 3.8: Lemma 3.8.2 (ACqinvCP)
* Section 3.11: Lemma 3.11.9 (ii)/Exercise 3.20 (contrFamilyCentre)

## Bonus content
* PLFI: [Programming Language Foundations in Agda](https://plfa.github.io/), but in Idris. This only contains some of the sections I find interesting.
