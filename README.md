# HoTT in Idris

This repository will contain a formalization of some of the content in the Homotopy Type Theory textbook in Idris.
Of course, univalence is inconsistent with the brand of pattern-matching that Idris has (which implies the uniqueness of identity proofs, axiom K, etc.), so we will have to be careful never to match on `Refl`.

* TypeTheory: Chapter 1
* Homotopy: Chapter 2 - Sections 2.1 to 2.4
* TypeFormers: Chapter 2 - Sections 2.5 to 2.11
* FunExt: Sections 2.9, 4.9, and 6.3 (TODO)
* Equivalence: Second half of Section 2.4; Chapter 4 (TODO)

## Bonus content
* PLFI: [Programming Language Foundations in Agda](https://plfa.github.io/), but in Idris. This only contains some of the sections I find interesting.
