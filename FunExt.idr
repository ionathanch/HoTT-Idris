{-
  Functional Extensionality
  Sections 2.9, 4.9, and 6.3

  Here is our plan of attack:
  * We assert the existence of an interval type, done so:
    https://homotopytypetheory.org/2011/04/23/running-circles-around-in-your-proof-assistant/
  * We prove naïve functional extensionality (a quasi-inverse to happly)
    using the interval type, as above and in Lemma 6.3.2
  * We prove weak functional extensionality (product of contractible types is contractible)
    from the naïve functional extensionality, done so:
    https://github.com/HoTT/HoTT/blob/master/theories/Metatheory/FunextVarieties.v
  * Finally, we prove strong functional extensionality (happly is an equivalence)
    from the weak functional extensionality, done both above and in Theorem 4.9.5.

  This should, in principle, not require univalence at all, only the interval type.
  The weak functional extensionality can also be derived from univalence by Lemma 4.9.2.
-}

import Homotopy

%default total

namespace Interval
  export -- Do not export constructors!
  data I : Type where
    Zero : I
    One : I

  public export
  zero : I
  zero = Zero

  public export
  one : I
  one = One

  export
  seg : Interval.zero =:= Interval.one

  public export
  rec_I : forall C. {a, b : C} -> (p : a =:= b) -> I -> C
  rec_I {a} {b} _ Zero = a
  rec_I {a} {b} _ One  = b

  public export
  ind_I : {C : I -> Type} -> {a : C Interval.zero} -> {b : C Interval.one} -> (p : transport C Interval.seg a =:= b) -> (i : I) -> C i
  ind_I {a} {b} _ Zero = a
  ind_I {a} {b} _ One  = b

  export
  seg_comp : forall C. {a, b : C} -> (p : a =:= b) -> ap (rec_I p) Interval.seg =:= p

-- Introduction rule: ∀x, f x = g x -> f = g
-- This is naïve functional extensionality and can also be proven from univalence
funext : forall A. {B : A -> Type} -> {f, g : (x : A) -> B x} -> f ~~ g -> f =:= g
funext h =
  let k : I -> (x : A) -> B x
      k i x = rec_I (h x) i
      res : (\x => f x) =:= (\x => g x)
      res = ap k seg
  in res

-- Elimination rule: f = g -> ∀x, f x = g x
happly : forall A. {B : A -> Type} -> {f, g : (x : A) -> B x} -> f =:= g -> f ~~ g
happly p = J {A = (x : A) -> B x} (\f, g, _ => f ~~ g) (\_, _ => Refl) p


-- [AXIOM] Reflexivity: funext (\_ => Refl) = Refl
fun_refl : forall A. {B : A -> Type} -> (f : (x : A) -> B x) -> funext {f = f} {g = f} (\_ => Refl) =:= Refl

-- Symmetry: funext (\x => (happly p x)⁻¹) = p⁻¹
fun_sym : forall A. {B : A -> Type} -> {f, g : (x : A) -> B x} -> (p : f =:= g) ->
  funext (\x => invert (happly p x)) =:= invert p
fun_sym p =
  J (\f, g, p => funext (\x => invert (happly {f} {g} p x)) =:= invert p) fun_refl p

-- Transitivity: funext (\x => happly p x <> happly q x) = p <> q
fun_trans : forall A. {B : A -> Type} -> {f, g, h : (x : A) -> B x} -> (p : f =:= g) -> (q : g =:= h) ->
  funext (\x => happly p x <> happly q x) =:= p <> q
fun_trans p q =
  let D : Dtype ((x : A) -> B x)
      D f g p = {h : (x : A) -> B x} -> (q : g =:= h) -> funext (\x => happly p x <> happly q x) =:= p <> q
      d : (g : (x : A) -> B x) -> D g g Refl
      d g q =
        let D' : Dtype ((x : A) -> B x)
            D' g h q = funext (\x => happly {f = g} {g = g} Refl x <> happly {f = g} {g = h} q x) =:= q
        in J D' fun_refl q
  in J D d p q


-- Computation rule: happly (funext h) = h
fun_comp : forall A. {B : A -> Type} -> {f, g : (x : A) -> B x} -> (h : f ~~ g) ->
  happly (funext h) =:= h
fun_comp h =
  let D : Dtype ((x : A) -> B x)
      D f g p = (h : f ~~ g) -> happly (funext h) =:= h
      d : (g : (x : A) -> B x) -> D g g Refl
      d g (\_ => Refl) = ap happly (fun_refl g)
  in J D d (funext h) h

-- Uniqueness principle: funext (happly h) = h
fun_uniq : forall A. {B : A -> Type} -> {f, g : (x : A) -> B x} -> (p : f =:= g) ->
  funext (happly p) =:= p
fun_uniq p = J {A = (x : A) -> B x} (\f, g, p => funext (happly p) =:= p) fun_refl p

-- f = g <~> f ~~ g
fun_qeqv : forall A. {B : A -> Type} -> {f, g : (x : A) -> B x} -> (f =:= g) <~> (f ~~ g)
fun_qeqv = ((happly, funext) ** (fun_uniq, fun_comp))
