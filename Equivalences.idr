{-
  Chapter 4: Equivalences

  For now, this contains only the second half of Section 2.4.
-}

import Homotopy
import FunExt
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

-- ∃(γ : x = x') s.t. f(γ) · p' = p -> (x, p) = (x', p')
fibId : forall A, B. (f : A -> B) -> (y : B) -> (xp, xp' : fib f y) ->
  (gamma : (fst xp) =:= (fst xp') ** ap f gamma <> (snd xp') =:= snd xp) -> xp =:= xp'
fibId f y (x ** p) (x' ** p') (gamma ** pp') =
  let pp1 : (invert (ap f gamma)) <> (ap f gamma <> p') =:= p'
      pp1 = associativity (invert (ap f gamma)) (ap f gamma) p' <> (leftInv (ap f gamma) |> p')
      pp2 : p' =:= invert (ap f gamma) <> p
      pp2 = (invert pp1) <> ((invert (ap f gamma)) <| pp')
      pp3 : transport (\x => f x =:= y) gamma p =:= transport (\y' => y' =:= y) (ap f gamma) p
      pp3 = transport_ap f gamma p
      pp4 : transport (\y' => y' =:= y) (ap f gamma) p =:= (invert (ap f gamma)) <> p
      pp4 = transport_concatr (ap f gamma) p
      pp5 : transport (\x => f x =:= y) gamma p =:= p'
      pp5 = pp3 <> pp4 <> (invert pp2)
  in dprodId (gamma ** pp5)

-- Definition: Contractible maps
contr : forall A, B. (f : A -> B) -> Type
contr f = (y : B) -> isContr (fib f y)

-- (i) qinf f -> contr f
qinvToContr : {A, B : Type} -> (f : A -> B) -> qinv f -> contr f
qinvToContr f (g ** (alpha, beta)) y =
  let beta' : f . g ~~ id {a = B}
      beta' b = invert (beta (f (g b))) <> (ap f (alpha (g b)) <> beta b)
      tau : (a : A) -> beta' (f a) =:= ap f (alpha a)
      tau a =
        let tau1 : ap f (alpha (g (f a))) =:= ap (f . g . f) (alpha a)
            tau1 = ap (ap f) (hom_commute alpha a) <> ap_concat (g . f) f (alpha a) in
        let tau2 : ap (f . g . f) (alpha a) <> beta (f a) =:= beta (f (g (f a))) <> ap f (alpha a)
            tau2 = invert (naturality (\a => beta (f a)) (alpha a))
            tau3 : ap f (alpha (g (f a))) <> beta (f a) =:= beta (f (g (f a))) <> ap f (alpha a)
            tau3 = (tau1 |> beta (f a)) <> tau2
            tau4 : invert (beta (f (g (f a)))) <> (beta (f (g (f a))) <> ap f (alpha a)) =:= ap f (alpha a)
            tau4 = associativity (invert (beta (f (g (f a))))) (beta (f (g (f a)))) (ap f (alpha a)) <> (leftInv (beta (f (g (f a)))) |> ap f (alpha a))
        in (invert (beta (f (g (f a)))) <| tau3) <> tau4
      fibCentre : fib f y
      fibCentre = (g y ** beta' y)
      fibContr : (xp : fib f y) -> fibCentre =:= xp
      fibContr (x ** p) =
        let gamma : g y =:= x
            gamma = invert (ap g p) <> alpha x
            fc1 : ap f gamma =:= ap f (invert (ap g p)) <> ap f (alpha x)
            fc1 = ap_distrib f (invert (ap g p)) (alpha x)
            fc2 : ap f (invert (ap g p)) =:= invert (ap (f . g) p)
            fc2 = ap_invert f (ap g p) <> ap invert (ap_concat g f p)
            fc3 : ap f gamma =:= invert (ap (f . g) p) <> ap f (alpha x)
            fc3 = fc1 <> (fc2 |> ap f (alpha x))
            fc4 : invert (ap (f . g) p) <> ap f (alpha x) =:= invert (ap (f . g) p) <> beta' (f x)
            fc4 = invert (ap (f . g) p) <| (invert (tau x)) in
        let fc5 : ap f gamma <> p =:= invert (ap (f . g) p) <> (beta' (f x) <> p)
            fc5 = ((fc3 <> fc4) |> p) <> invert (associativity (invert (ap (f . g) p)) (beta' (f x)) p)
            fc6 : beta' (f x) <> p =:= ap (f . g) p <> beta' y
            fc6 = (beta' (f x) <| (invert (ap_ident p))) <> naturality beta' p
            fc7 : invert (ap (f . g) p) <> (ap (f . g) p <> beta' y) =:= beta' y
            fc7 = associativity (invert (ap (f . g) p)) (ap (f . g) p) (beta' y) <> (leftInv (ap (f . g) p) |> beta' y)
            fc8 : ap f gamma <> p =:= beta' y
            fc8 = fc5 <> (invert (ap (f . g) p) <| fc6) <> fc7
        in fibId f y (g y ** beta' y) (x ** p) (gamma ** fc8)
  in (fibCentre ** fibContr)

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

-- (iii) isProp (contr f)
contrEqvIsProp : {A, B : Type} -> (f : A -> B) -> isProp (contr f)
contrEqvIsProp f = funIsProp (\y => isContrIsProp {A = fib f y})

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
