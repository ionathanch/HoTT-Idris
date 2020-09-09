{-
  Chapter 4: Equivalences

  For now, this contains only the second half of Section 2.4.
-}

import Homotopy
import TypeFormers
import SetsLogic

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

-- (iii) isProp (binv f)
-- Technique: Show that linv and rinv are propositions, then use prodIsProp

-----------------------------
---- CONTRACTIBLE FIBERS ----
-----------------------------

-- Definition : Fibre of a map over a point
fib : {A, B : Type} -> (f : A -> B) -> (y : B) -> Type
fib f y = (x : A ** f x =:= y)

-- Definition: Contractible maps
contr : forall A, B. (f : A -> B) -> Type
contr f = (y : B) -> isContr (fib f y)

-- (i) qinf f -> contr f
{-
qinvToContr : forall A, B. (f : A -> B) -> qinv f -> contr f
qinvToContr f (g ** (alpha, beta)) y =
  let fibCentre : (x : A ** f x =:= y)
      fibCentre = (g y ** beta y)
      fibContr : (fibfy : (x : A ** f x =:= y)) -> fibCentre =:= fibfy
      fibContr (x ** p) =
        let gyx : g y =:= x
            gyx = ap g (invert p) <> alpha x
            fc1 : transport (\gy => f gy =:= y) gyx (beta y) =:= transport (\fx => fx =:= y) (ap f gyx) (beta y)
            fc1 = transport_ap f {P = \fx => fx =:= y} gyx (beta y) in
        let fc2 : transport (\fx => fx =:= y) (ap f gyx) (beta y) =:= invert (ap f gyx) <> beta y
            fc2 = transport_concatr {a = y} (ap f gyx) (beta y)
            fc3 : invert (ap f gyx) <> beta y =:= invert (ap f (ap g (invert p)) <> ap f (alpha x)) <> beta y
            fc3 = ap invert (ap_distrib f (ap g (invert p)) (alpha x)) |> beta y
            fc4 : invert (ap f (ap g (invert p)) <> ap f (alpha x)) <> beta y =:= invert (ap (f . g) (invert p) <> ap f (alpha x)) <> beta y
            fc4 = ap (\q => invert (q <> ap f (alpha x))) (ap_concat g f (invert p)) |> beta y
        in dprodId (gyx ** ?betayp)
  in (fibCentre ** fibContr)
-}

-- (ii) contr f -> qinf f
contrToQinv : forall A, B. (f : A -> B) -> contr f -> (g : B -> A ** ((x : A) -> g (f x) =:= x, (y : B) -> f (g y) =:= y))
contrToQinv f contrF =
  let g : B -> A
      g y = fst (fst (contrF y))
      fg : (y : B) -> f (g y) =:= y
      fg y = snd (fst (contrF y))
      gf : (x : A) -> g (f x) =:= x
      gf x =
        let p : (g (f x) ** fg (f x)) =:= MkDPair {p = \x' => f x' =:= f x} x Refl
            p = invert ((snd (contrF (f x))) (g (f x) ** fg (f x))) <> (snd (contrF (f x))) (x ** Refl)
        in fst (dprodId_pr p)
  in MkDPair {a = B -> A} g (gf, fg)

---------------------
---- EQUIVALENCE ----
---------------------

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

-- Transform a quasi-equivalence into an equivalence
-- qeqToEquiv : forall A, B. A <~> B -> A =~= B
qeqToEquiv ((f, g) ** (gf, fg)) = (f ** ((g ** gf), (g ** fg)))
