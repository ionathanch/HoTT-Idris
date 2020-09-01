{-
  Chapter 4: Equivalences

  For now, this contains only the second half of Section 2.4.
-}

import Homotopy

%default total

----------------------------
---- BI-INVERTIBLE MAPS ----
----------------------------

-- Definition: Left inverse
-- linv(f) := ∃(g : B -> A) s.t. g ∘ f ~ id
linv : forall A, B. (f : A -> B) -> Type
linv f = (g : B -> A ** (g . f ~~ id {a = A}))

-- Definition: Right inverse
-- rinv(f) := ∃(h : B -> A) s.t. f ∘ h ~ id
rinv : forall A, B. (f : A -> B) -> Type
rinv f = (h : B -> A ** (f . h ~~ id {a = B}))

-- Definition: Bi-invertible map
-- binv(f) := linv(f) ∧ rinv(f)
binv : forall A, B. (f : A -> B) -> Type
binv f = (linv f, rinv f)

-- (i) qinv f -> binv f
qinvToBinv : forall A, B. (f : A -> B) -> qinv f -> binv f
qinvToBinv f (g ** (alpha, beta)) = (MkDPair {a = B -> A} g alpha, MkDPair {a = B -> A} g beta)

-- (ii) binv f -> qinv f
binvToQinv : forall A, B. (f : A -> B) -> binv f -> qinv f
binvToQinv f ((g ** alpha), (h ** beta)) =
  let gamma : h ~~ g
      gamma x = invert (alpha (h x)) <> ap g (beta x)
      alpha' : h . f ~~ id {a = A}
      alpha' x = gamma (f x) <> alpha x
  in MkDPair {a = B -> A} h (alpha', beta)

-- (iii) (e1, e2 : binv f) -> e1 = e2
-- We cannot prove this just yet


-- Definition: Equivalence of two types
-- For now, we define equivalence as a bi-invertible map
-- We will sometimes write f : A ≃ B for (f, e) : A ≃ B where f : A -> B,
-- and g(a) for ((pr1 g) a) where g : A ≃ B
a =~= b = (f : a -> b ** binv f)

-- Reflexivity: A ≃ A
-- equiv_refl : forall A. A =~= A
equiv_refl = MkDPair {a = A -> A} id (MkDPair {a = A -> A} id (\_ => Refl), MkDPair {a = A -> A} id (\_ => Refl))

-- Symmetry: If A ≃ B then B ≃ A
-- equiv_sym : forall A, B. A =~= B -> B =~= A
equiv_sym (f ** e) =
  let (finv ** (alpha, beta)) = binvToQinv f e
      einv = qinvToBinv finv (MkDPair {a = A -> B} f (beta, alpha))
  in MkDPair {a = B -> A} finv einv

-- Transitivity: If A ≃ B and B ≃ C then A ≃ C
-- equiv_trans : forall A, B, C. A =~= B -> B =~= C -> A =~= C
equiv_trans (f ** a) (g ** b) =
  let (finv ** (finvf, ffinv)) = binvToQinv f a
      (ginv ** (ginvg, gginv)) = binvToQinv g b
      gffginv = \c => ap g (ffinv (ginv c)) <> gginv c
      fginvgf = \a => ap finv (ginvg (f a)) <> finvf a
      abinv = qinvToBinv (g . f) (MkDPair {a = C -> A} (finv . ginv) (fginvgf, gffginv))
  in MkDPair {a = A -> C} (g . f) abinv
