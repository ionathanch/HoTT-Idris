{-
  Chapter 2: Homotopy Type Theory

  Conventions on implicit arguments:
  * Endpoints of a path or sections of a homotopy will be implicit,
    e.g. {x, y : A} -> x === y or {f, g : (x : A) -> P x} -> f ~~ g.
    The only exception is the definition of Dtype.
  * In lift and apd only, the type family P is implicit.
    This is for consistency with the book.
-}

-- Path induction family type
Dtype : Type -> Type
Dtype atype = (x, y : atype) -> x === y -> Type

-- The J operator, i.e. path induction
-- I think there's no way to prove this
-- except by matching on Refl.
J : forall A. (D : Dtype A) ->
  (d : (a : A) -> D a a Refl) ->
  {x, y : A} -> (p : x === y) -> D x y p
J _ d Refl = d x

-----------------------------
---- TYPES are GROUPOIDS ----
-----------------------------

{-
  Equality      Homotopy       ∞-Groupoid
  --------      --------       ----------
  reflexivity   const. path    id. morphism
  symmetry      inversion      inverse
  transitivity  concatenation  composition
-}

-- Symmetry: If x = y then y = x
invert : forall A. {x, y : A} -> x === y -> y === x
invert p = J (\x, y, _ => y === x) (\_ => Refl) p

-- Transitivity: If x = y and y = z then x = z
concat : forall A. {x, y, z : A} -> x === y -> y === z -> x === z
concat p q =
  let D : Dtype A
      D x y _ = (z : A) -> y = z -> x = z
  in J D (\_, _, r => r) p z q


-- p = Refl · p
leftId : forall A. {x, y : A} -> (p : x === y) -> p === concat Refl p
leftId p = J (\_, _, p => p === concat Refl p) (\_ => Refl) p

-- p = p · Refl
rightId : forall A. {x, y : A} -> (p : x === y) -> p === concat p Refl
rightId p = J (\_, _, p => p === concat p Refl) (\_ => Refl) p

-- Refl · p = p · Refl
leftrightId : forall A. {x, y : A} -> (p : x === y) -> concat Refl p === concat p Refl
leftrightId p = concat (invert (leftId p)) (rightId p)

-- p · Refl = Refl · p
rightleftId : forall A. {x, y : A} -> (p : x === y) -> concat p Refl === concat Refl p
rightleftId p = concat (invert (rightId p)) (leftId p)

-- p⁻¹ · p = Refl
leftInv : forall A. {x, y : A} -> (p : x === y) -> concat (invert p) p === Refl
leftInv p = J (\_, _, p => concat (invert p) p === Refl) (\_ => Refl) p

-- p · p⁻¹ = Refl
rightInv : forall A. {x, y : A} -> (p : x === y) -> concat p (invert p) === Refl
rightInv p = J (\_, _, p => concat p (invert p) === Refl) (\_ => Refl) p

-- (p⁻¹)⁻¹ = p
invertibility : forall A. {x, y : A} -> (p : x === y) -> invert (invert p) === p
invertibility p = J (\_, _, p => invert (invert p) === p) (\_ => Refl) p

-- p · (q · r) = (p · q) · r
associativity : forall A. {x, y, z, w : A} -> (p : x === y) -> (q : y === z) -> (r : z === w) ->
  concat p (concat q r) === concat (concat p q) r
associativity p q r =
  let D : Dtype A
      D x y p = {z, w : A} -> (q : y === z) -> (r : z === w) ->
        concat p (concat q r) === concat (concat p q) r
  in J D (\_, _, _ => Refl) p q r


-- Loop space of a point in a type
Omega : (A : Type) -> (a : A) -> Type
Omega _ a = a === a

-- Loop space of a loop space of a point
Omega2 : (A : Type) -> (a : A) -> Type
Omega2 _ a = Refl {x = a} === Refl {x = a}


-- Composition of 2-fold loop spaces is commutative
EckmannHilton : (A : Type) -> (a : A) -> (x, y : Omega2 A a) -> concat x y === concat y x
EckmannHilton _ a x y = ?eh


-- n-fold iterated loop spaces

loopSpace : (A : Type ** A) -> (A : Type ** A)
loopSpace (_ ** a) = (a === a ** Refl {x = a})

loopSpaceN : (n : Nat) -> (A : Type ** A) -> (A : Type ** A)
loopSpaceN Z pt = pt
loopSpaceN (S n) pt = loopSpaceN n (loopSpace pt)

--------------------------------
---- FUNCTIONS are FUNCTORS ----
--------------------------------

-- Application of f to a path; action on paths of f
-- In other words, mapping f over a path
ap : forall A, B. (f : A -> B) -> {x, y : A} -> x === y -> f x === f y
ap f p = J (\x, y, _ => f x === f y) (\_ => Refl) p


-- ap_f (p · q) = (ap f p) · (ap f q)
ap_distrib : forall A, B. (f : A -> B) -> {x, y, z : A} -> (p : x === y) -> (q : y === z) ->
  ap f (concat p q) === concat (ap f p) (ap f q)
ap_distrib f p q =
  let D : Dtype A
      D x y p = {z : A} -> (q : y === z) ->
        ap f (concat p q) === concat (ap f p) (ap f q)
  in J D (\_, _ => Refl) p q

-- ap f p⁻¹ = (ap f p)⁻¹
ap_invert : forall A, B. (f : A -> B) -> {x, y : A} -> (p : x === y) -> ap f (invert p) === invert (ap f p)
ap_invert f p = J (\_, _, p => ap f (invert p) === invert (ap f p)) (\_ => Refl) p

-- ap g (ap f p) = ap (g ∘ f) p
ap_concat : forall A, B, C. (f : A -> B) -> {x, y : A} -> (g : B -> C) -> (p : x === y) -> ap g (ap f p) === ap (g . f) p
ap_concat f g p = J (\_, _, p => ap g (ap f p) === ap (g . f) p) (\_ => Refl) p

-- ap id p = p
ap_ident : forall A. {x, y : A} -> (p : x === y) -> ap (id {a = A}) p === p
ap_ident p = J (\_, _, p => ap (id {a = A}) p === p) (\_ => Refl) p

--------------------------------------
---- TYPE FAMILIES are FIBRATIONS ----
--------------------------------------

-- The indiscernibility of identicals, renamed
-- We also write p* := transport P p for some implicit P
transport : forall A. (P : A -> Type) -> {x, y : A} -> (p : x === y) -> P x -> P y
transport ptype p = J (\x, y, _ => ptype x -> ptype y) (\_, px => px) p

-- Path lifting property
lift : forall A. {P : A -> Type} -> (u : forall x. P x) -> {x, y : A} -> (p : x === y) ->
  MkDPair {p = P} x u === MkDPair {p = P} y (transport P p u)
lift u p =
  let D : Dtype A
      D x y p = MkDPair {p = P} x u === MkDPair {p = P} y (transport P p u)
  in J D (\_ => Refl) p

-- Dependent ap, i.e. mapping over a path with a dependent function f
apd : forall A. {P : A -> Type} -> (f : (a : A) -> P a) -> {x, y : A} -> (p : x === y) -> transport P p (f x) === f y
apd f p = J (\x, y, p => transport P p (f x) === f y) (\_ => Refl) p

-- Transporting in a constant family type P := (\_ => B) does nothing
transportconst : forall A. (B : Type) -> {x, y : A} -> (p : x === y) -> (b : B) -> transport (\_ => B) p b === b
transportconst btype p b = J (\_, _, p => transport (\_ => btype) p b === b) (\_ => Refl) p


-- apd f p = transportconst B p (f x) · ap f p
-- That is, dependently applying a nondependent function to a path
-- yields the same thing as nondependently applying the function
apd_nondep : forall A. (B : Type) -> (f : A -> B) -> {x, y : A} -> (p : x === y) ->
  apd f p === concat (transportconst B p (f x)) (ap f p)
apd_nondep btype f p =
  let D : Dtype A
      D x y p = apd f p === concat (transportconst btype p (f x)) (ap f p)
  in J D (\_ => Refl) p

transport_distrib : forall A. (P : A -> Type) -> {x, y, z : A} -> (p : x === y) -> (q : y === z) -> (u : P x) ->
  transport P q (transport P p u) === transport P (concat p q) u
transport_distrib ptype p q u =
  let D : Dtype A
      D x y p = {z : A} -> (q : y === z) -> (u : ptype x) -> transport ptype q (transport ptype p u) === transport ptype (concat p q) u
  in J D (\_, _, _ => Refl) p q u

transport_ap : forall A, B. (f : A -> B) -> (P : B -> Type) -> {x, y : A} -> (p : x === y) -> (u : P (f x)) ->
  transport (P . f) p u === transport P (ap f p) u
transport_ap f ptype p u =
  let D : Dtype A
      D x y p = (u : ptype (f x)) -> transport (ptype . f) p u === transport ptype (ap f p) u
  in J D (\_, _ => Refl) p u

transport_commute : forall A. (P, Q : A -> Type) -> (f : (a : A) -> P a -> Q a) -> {x, y : A} -> (p : x === y) -> (u : P x) ->
  transport Q p (f x u) === f y (transport P p u)
transport_commute ptype qtype f p u =
  let D : Dtype A
      D x y p = (u : ptype x) -> transport qtype p (f x u) === f y (transport ptype p u)
  in J D (\_, _ => Refl) p u

-------------------------------------
---- HOMOTOPIES and EQUIVALENCES ----
-------------------------------------

infix 5 ~~
(~~) : forall A, P. (f, g : (x : A) -> P x) -> Type
f ~~ g = (x : A) -> f x === g x

hom_refl : f ~~ f
hom_refl _ = Refl

hom_symm : forall A, P. {f, g : (x : A) -> P x} -> f ~~ g -> g ~~ f
hom_symm fg x = invert (fg x)

hom_trans : forall A, P. {f, g, h : (x : A) -> P x} -> f ~~ g -> g ~~ h -> f ~~ h
hom_trans fg gh x = concat (fg x) (gh x)


hom_assoc : forall A, B. {f, g : A -> B} -> (H : f ~~ g) -> {x, y : A} -> (p : x === y) ->
  concat (H x) (ap g p) === concat (ap f p) (H y)
hom_assoc hom p =
  let D : Dtype A
      D x y p = concat (hom x) (ap g p) === concat (ap f p) (hom y)
      d : (a : A) -> concat (hom a) Refl === concat Refl (hom a)
      d a = rightleftId (hom a)
  in J D d p

hom_commute : forall A. {f : A -> A} -> (H : f ~~ id {a = A}) -> (a : A) -> H (f a) === ap f (H a)
hom_commute hom a = ?hc
