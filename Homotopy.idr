{-
  Chapter 2: Homotopy Type Theory
  Sections 2.1 to 2.4

  This file covers:
  * Properties of paths
  * `ap` and `transport` and properties thereof
  * Homotopy and naturality
  * Quasi-invertibility and properties of equivalence

  Conventions on implicit arguments:
  * Endpoints of a path or sections of a homotopy are implicit,
    e.g. {x, y : A} -> x =:= y or {f, g : (x : A) -> P x} -> f ~~ g.
    The only exception is the definition of Dtype.
  * Type parameters and type families are implicit,
    with the exception of transport and transportConst.
-}

%default total

-- Redefine homogenous equality with a lower infixity
-- so that it binds /less/ tightly than <>
infix 7 =:=
(=:=) : (x : a) -> (y : a) -> Type
(=:=) = (===)

-- Path induction family type
Dtype : Type -> Type
Dtype atype = (x, y : atype) -> x =:= y -> Type

-- The J operator, i.e. path induction
-- I think there's no way to prove this
-- except by matching on Refl.
J : forall A. (D : Dtype A) ->
  (d : (a : A) -> D a a Refl) ->
  {x, y : A} -> (p : x =:= y) -> D x y p
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
invert : forall A. {x, y : A} -> x =:= y -> y =:= x
invert p = J (\x, y, _ => y =:= x) (\_ => Refl) p

-- Transitivity: If x = y and y = z then x = z
infixr 8 <>
(<>) : forall A. {x, y, z : A} -> x =:= y -> y =:= z -> x =:= z
p <> q =
  let D : Dtype A
      D x y _ = (z : A) -> y = z -> x = z
  in J D (\_, _, r => r) p z q

{-
  We can also define it by double induction on both p and q.
  However, this causes (<>) to compute iff p and q are BOTH Refl,
  which can be inconvenient.

p <> q =
  let D : Dtype A
      D x y _ = {z : A} -> y = z -> x = z
      d : (y : A) -> D y y Refl
      d y q =
        let D' : Dtype A
            D' y z q = (y = z)
        in J D' (\_ => Refl) q
  in J D d p q
-}


-- p = Refl · p
leftId : forall A. {x, y : A} -> (p : x =:= y) -> p =:= Refl <> p
leftId p = J (\_, _, p => p =:= Refl <> p) (\_ => Refl) p

-- p = p · Refl
rightId : forall A. {x, y : A} -> (p : x =:= y) -> p =:= p <> Refl
rightId p = J (\_, _, p => p =:= p <> Refl) (\_ => Refl) p

-- Refl · p = p · Refl
leftrightId : forall A. {x, y : A} -> (p : x =:= y) -> Refl <> p =:= p <> Refl
leftrightId p = invert (leftId p) <> rightId p

-- p · Refl = Refl · p
rightleftId : forall A. {x, y : A} -> (p : x =:= y) -> p <> Refl =:= Refl <> p
rightleftId p = invert (rightId p) <> leftId p

-- p⁻¹ · p = Refl
leftInv : forall A. {x, y : A} -> (p : x =:= y) -> invert p <> p =:= Refl
leftInv p = J (\_, _, p => invert p <> p =:= Refl) (\_ => Refl) p

-- p · p⁻¹ = Refl
rightInv : forall A. {x, y : A} -> (p : x =:= y) -> p <> invert p =:= Refl
rightInv p = J (\_, _, p => p <> invert p =:= Refl) (\_ => Refl) p

-- (p⁻¹)⁻¹ = p
invertibility : forall A. {x, y : A} -> (p : x =:= y) -> invert (invert p) =:= p
invertibility p = J (\_, _, p => invert (invert p) =:= p) (\_ => Refl) p

-- p · (q · r) = (p · q) · r
associativity : forall A. {x, y, z, w : A} -> (p : x =:= y) -> (q : y =:= z) -> (r : z =:= w) ->
  p <> (q <> r) =:= (p <> q) <> r
associativity p q r =
  let D : Dtype A
      D x y p = {z, w : A} -> (q : y =:= z) -> (r : z =:= w) ->
        p <> (q <> r) =:= (p <> q) <> r
  in J D (\_, _, _ => Refl) p q r


{- Whiskering as defined as part of Theorem 2.1.6
  Later we will define whiskering using ap instead, which is much simpler

-- Right whisker: If p = q then p · r = q · r
whiskr : forall A. {x, y, z : A} -> {p, q : x =:= y} -> (a : p =:= q) -> (r : y =:= z) -> p <> r =:= q <> r
whiskr alpha r =
  let D : Dtype A
      D y z r = {x : A} -> (p, q : x =:= y) -> (alpha : p =:= q) -> p <> r =:= q <> r
      d : (a : A) -> {x : A} -> (p, q : x =:= a) -> (alpha : p =:= q) -> p <> Refl =:= q <> Refl
      d _ p q alpha = invert (rightId p) <> (alpha <> rightId q)
  in J D d r p q alpha

-- Left whisker: If r = s then q · r = q · s
whiskl : forall A. {x, y, z : A} -> {r, s : y =:= z} -> (q : x =:= y) -> (b : r =:= s) -> q <> r =:= q <> s
whiskl q beta =
  let D : Dtype A
      D x y q = {z : A} -> (r, s : y =:= z) -> (beta : r =:= s) -> q <> r =:= q <> s
      d : (a : A) -> {z : A} -> (r, s : a =:= z) -> (beta : r =:= s) -> Refl <> r =:= Refl <> s
      d _ r s beta = invert (leftId r) <> (beta <> leftId s)
  in J D d q r s beta
-}


-- Definition: Loop space of a point in a type
Omega : (A : Type) -> (a : A) -> Type
Omega _ a = a =:= a

-- Definition: Loop space of a loop space of a point
Omega2 : (A : Type) -> (a : A) -> Type
Omega2 _ a = Refl {x = a} =:= Refl {x = a}


-- Composition of 2-fold loop spaces is commutative
EckmannHilton : (A : Type) -> (a : A) -> (x, y : Omega2 A a) -> x <> y =:= y <> x


-- n-fold iterated loop spaces

loopSpace : (A : Type ** A) -> (A : Type ** A)
loopSpace (_ ** a) = (a =:= a ** Refl {x = a})

loopSpaceN : (n : Nat) -> (A : Type ** A) -> (A : Type ** A)
loopSpaceN Z pt = pt
loopSpaceN (S n) pt = loopSpaceN n (loopSpace pt)

--------------------------------
---- FUNCTIONS are FUNCTORS ----
--------------------------------

-- Application of f to a path; action on paths of f
-- In other words, mapping f over a path
-- We also write f(p)
ap : forall A, B. (f : A -> B) -> {x, y : A} -> x =:= y -> f x =:= f y
ap f p = J (\x, y, _ => f x =:= f y) (\_ => Refl) p


-- f(p · q) = f(p) · f(q)
ap_distrib : forall A, B. (f : A -> B) -> {x, y, z : A} -> (p : x =:= y) -> (q : y =:= z) ->
  ap f (p <> q) =:= ap f p <> ap f q
ap_distrib f p q =
  let D : Dtype A
      D x y p = {z : A} -> (q : y =:= z) ->
        ap f (p <> q) =:= ap f p <> ap f q
  in J D (\_, _ => Refl) p q

-- f(p⁻¹) = f(p)⁻¹
ap_invert : forall A, B. (f : A -> B) -> {x, y : A} -> (p : x =:= y) -> ap f (invert p) =:= invert (ap f p)
ap_invert f p = J (\_, _, p => ap f (invert p) =:= invert (ap f p)) (\_ => Refl) p

-- g(f(p)) = (g ∘ f)(p)
ap_concat : forall A, B, C. (f : A -> B) -> {x, y : A} -> (g : B -> C) -> (p : x =:= y) -> ap g (ap f p) =:= ap (g . f) p
ap_concat f g p = J (\_, _, p => ap g (ap f p) =:= ap (g . f) p) (\_ => Refl) p

-- id(p) = p
ap_ident : forall A. {x, y : A} -> (p : x =:= y) -> ap (id {a = A}) p =:= p
ap_ident p = J (\_, _, p => ap (id {a = A}) p =:= p) (\_ => Refl) p


-- Right whisker: If p = q then p · r = q · r
infixl 9 |>
(|>) : forall A. {x, y, z : A} -> {p, q : x =:= y} -> (a : p =:= q) -> (r : y =:= z) -> p <> r =:= q <> r
alpha |> r = ap (\s => s <> r) alpha

-- Left whisker: If r = s then q · r = q · s
infixr 9 <|
(<|) : forall A. {x, y, z : A} -> {r, s : y =:= z} -> (q : x =:= y) -> (b : r =:= s) -> q <> r =:= q <> s
q <| beta = ap (\p => q <> p) beta


-- p · q = p · r -> q = r
leftCancel : forall A. {x, y, z : A} -> (p : x =:= y) -> (q, r : y =:= z) ->
  p <> q =:= p <> r -> q =:= r
leftCancel p q r s =
  let t : invert p <> (p <> q) =:= invert p <> (p <> r)
      t = invert p <| s
      u : (invert p <> p) <> q =:= (invert p <> p) <> r
      u = invert (associativity (invert p) p q) <> t <> associativity (invert p) p r
      vl : q =:= (invert p <> p) <> q
      vl = leftId q <> (invert (leftInv p) |> q)
      vr : (invert p <> p) <> r =:= r
      vr = ((leftInv p) |> r) <> invert (leftId r)
  in vl <> u <> vr

-- p · r = q · r -> p = q
rightCancel : forall A. {x, y, z : A} -> (p, q : x =:= y) -> (r : y =:= z) ->
  p <> r = q <> r -> p = q
rightCancel p q r s =
  let t : (p <> r) <> invert r =:= (q <> r) <> invert r
      t = s |> invert r
      u : p <> (r <> invert r) =:= q <> (r <> invert r)
      u = associativity p r (invert r) <> t <> invert (associativity q r (invert r))
      vl : p =:= p <> (r <> invert r)
      vl = rightId p <> (p <| invert (rightInv r))
      vr : q <> (r <> invert r) =:= q
      vr = (q <| rightInv r) <> invert (rightId q)
  in vl <> u <> vr

--------------------------------------
---- TYPE FAMILIES are FIBRATIONS ----
--------------------------------------

-- The indiscernibility of identicals, renamed
-- We also write p* := transport P p for some implicit P, or p[P]* explicitly
transport : forall A. (P : A -> Type) -> {x, y : A} -> (p : x =:= y) -> P x -> P y
transport ptype p = J (\x, y, _ => ptype x -> ptype y) (\_, px => px) p

-- Path lifting property
lift : forall A. {P : A -> Type} -> (u : forall x. P x) -> {x, y : A} -> (p : x =:= y) ->
  MkDPair {p = P} x u =:= MkDPair {p = P} y (transport P p u)
lift u p =
  let D : Dtype A
      D x y p = MkDPair {p = P} x u =:= MkDPair {p = P} y (transport P p u)
  in J D (\_ => Refl) p

-- Dependent ap, i.e. mapping over a path p with a dependent function f
-- Similarly, we also write f(p) when it is clear that f is dependent
apd : forall A. {P : A -> Type} -> (f : (a : A) -> P a) -> {x, y : A} -> (p : x =:= y) -> transport P p (f x) =:= f y
apd f p = J (\x, y, p => transport P p (f x) =:= f y) (\_ => Refl) p

-- Transporting in a constant family type P := (\_ => B) does nothing
transportConst : forall A. (B : Type) -> {x, y : A} -> (p : x =:= y) -> (b : B) -> transport (\_ => B) p b =:= b
transportConst btype p b = J (\_, _, p => transport (\_ => btype) p b =:= b) (\_ => Refl) p


-- f(p) = transportConst B p (f x) · f(p)
-- That is, dependently applying a nondependent function to a path
-- yields the same thing as nondependently applying the function
apd_nondep : forall A. {B : Type} -> (f : A -> B) -> {x, y : A} -> (p : x =:= y) ->
  apd f p =:= transportConst B p (f x) <> ap f p
apd_nondep f p =
  let D : Dtype A
      D x y p = apd f p =:= transportConst B p (f x) <> ap f p
  in J D (\_ => Refl) p

-- q* (p* u) = (p <> q)* u
transport_distrib : forall A. {P : A -> Type} -> {x, y, z : A} -> (p : x =:= y) -> (q : y =:= z) -> (u : P x) ->
  transport P q (transport P p u) =:= transport P (p <> q) u
transport_distrib p q u =
  let D : Dtype A
      D x y p = {z : A} -> (q : y =:= z) -> (u : P x) -> transport P q (transport P p u) =:= transport P (p <> q) u
  in J D (\_, _, _ => Refl) p q u

-- p[P ∘ f]* u = f(p)[P]* u
transport_ap : forall A, B. (f : A -> B) -> {P : B -> Type} -> {x, y : A} -> (p : x =:= y) -> (u : P (f x)) ->
  transport (P . f) p u =:= transport P (ap f p) u
transport_ap f p u =
  let D : Dtype A
      D x y p = (u : P (f x)) -> transport (P . f) p u =:= transport P (ap f p) u
  in J D (\_, _ => Refl) p u

-- p[Q]* (f x u) = f y (p[P]* u)
transport_commute : forall A. {P, Q : A -> Type} -> (f : (a : A) -> P a -> Q a) -> {x, y : A} -> (p : x =:= y) -> (u : P x) ->
  transport Q p (f x u) =:= f y (transport P p u)
transport_commute f p u =
  let D : Dtype A
      D x y p = (u : P x) -> transport Q p (f x u) =:= f y (transport P p u)
  in J D (\_, _ => Refl) p u

--------------------
---- HOMOTOPIES ----
--------------------

-- Definition: Homotopy, i.e. extensionality
-- f ~ g := ∀(x : A), f x = g x
infix 5 ~~
(~~) : forall A, P. (f, g : (x : A) -> P x) -> Type
f ~~ g = (x : A) -> f x =:= g x

-- Reflexivity: f ~ f
hom_refl : f ~~ f
hom_refl _ = Refl

-- Symmetry: If f ~ g then g ~ f
hom_sym : forall A, P. {f, g : (x : A) -> P x} -> f ~~ g -> g ~~ f
hom_sym fg x = invert (fg x)

-- Transitivity: If f ~ g and g ~ h then f ~ h
hom_trans : forall A, P. {f, g, h : (x : A) -> P x} -> f ~~ g -> g ~~ h -> f ~~ h
hom_trans fg gh x = fg x <> gh x


-- H x · g(p) = f(p) · H y
naturality : forall A, B. {f, g : A -> B} -> (H : f ~~ g) -> {x, y : A} -> (p : x =:= y) ->
  H x <> ap g p =:= ap f p <> H y
naturality hom p =
  let D : Dtype A
      D x y p = hom x <> ap g p =:= ap f p <> hom y
      d : (a : A) -> hom a <> Refl =:= Refl <> hom a
      d a = rightleftId (hom a)
  in J D d p

-- H (f a) = f(H a)
-- This follows from naturality, with x = f x, y = x, f = f, g = id
-- In short, H : f ~ id
hom_commute : forall A. {f : A -> A} -> (H : f ~~ id {a = A}) -> (a : A) -> H (f a) =:= ap f (H a)
hom_commute hom a =
  let naturalized : hom (f a) <> hom a =:= ap f (hom a) <> hom a
      naturalized = h1 <> h2
        where
          h1 : hom (f a) <> hom a =:= hom (f a) <> ap (id {a = A}) (hom a)
          h1 = hom (f a) <| invert (ap_ident (hom a))
          h2 : hom (f a) <> ap (id {a = A}) (hom a) =:= ap f (hom a) <> hom a
          h2 = naturality hom (hom a)
      whisked : hom (f a) <> (hom a <> (invert (hom a))) =:= ap f (hom a) <> (hom a <> (invert (hom a)))
      whisked = hl <> h <> hr
        where
          h : (hom (f a) <> hom a) <> invert (hom a) =:= (ap f (hom a) <> hom a) <> invert (hom a)
          h = naturalized |> invert (hom a)
          hl : hom (f a) <> (hom a <> (invert (hom a))) =:= (hom (f a) <> hom a) <> invert (hom a)
          hl = associativity (hom (f a)) (hom a) (invert (hom a))
          hr : (ap f (hom a) <> hom a) <> invert (hom a) =:= ap f (hom a) <> (hom a <> (invert (hom a)))
          hr = invert $ associativity (ap f (hom a)) (hom a) (invert (hom a))
      cancel_left : hom (f a) =:= hom (f a) <> (hom a <> (invert (hom a)))
      cancel_left = hid <> hinv
        where
          hid : hom (f a) =:= hom (f a) <> Refl
          hid = rightId (hom (f a))
          hinv : hom (f a) <> Refl =:= hom (f a) <> (hom a <> (invert (hom a)))
          hinv = hom (f a) <| invert (rightInv (hom a))
      cancel_right : ap f (hom a) <> (hom a <> (invert (hom a))) =:= ap f (hom a)
      cancel_right = hinv <> hid
        where
          hinv : ap f (hom a) <> (hom a <> (invert (hom a))) =:= ap f (hom a) <> Refl
          hinv = ap f (hom a) <| rightInv (hom a)
          hid : ap f (hom a) <> Refl =:= ap f (hom a)
          hid = invert (rightId (ap f (hom a)))
  in cancel_left <> whisked <> cancel_right

------------------------
---- EQUIVALENCE ----
------------------------

{-
  A quasi-inverse is the inverse usually associated with isomorphisms.
  The quasi-inverse of a function f is a function g such that
    f ∘ g ~ id and g ∘ f ~ id.
  Then we would usually say that A and B are isomorphic if there exist
  a mapping f : A -> B with a quasi-inverse (qinv f) : B -> A such that
  the above homotopies hold.
  For our purposes we will call f an quasii-equivalence from A to B.

  An equivalence is defined in terms of quasi-inverses, and given some
  function f : A -> B, it must satisfy the following conditions:
      (i) qinv f -> equiv f
     (ii) equiv f -> qinv f
    (iii) (e1, e2 : equiv f) -> e1 = e2
  We delay the definition of equivalences to the Equivalences file.
  Since to show that two types are equivalent it suffices to show that
  there exists a quasi-equivalence, we will only show the equivalence
  theorems presented in the book up to quasi-invertibility.
-}

-- Definition: Quasi-inverse
-- qinv(f) := ∃(q : B -> A) s.t. (f ∘ g ~ id) ∧ (g ∘ f ~ id)
qinv : forall A, B. (f : A -> B) -> Type
qinv f = (g : B -> A ** (g . f ~~ id {a = A}, f . g ~~ id {a = B}))


-- Definition: Quasi-equivalence
-- A <~> B := ∃(f : A -> B) s.t. qinv(f)
infix 4 <~>
(<~>) : (A, B : Type) -> Type
a <~> b = (fg : (a -> b, b -> a) ** ((snd fg) . (fst fg) ~~ id {a = a}, (fst fg) . (snd fg) ~~ id {a = b}))

-- Reflexivity : A <~> A
qeqv_refl : forall A. A <~> A
qeqv_refl = ((id, id) ** (\_ => Refl, \_ => Refl))

-- Symmetry : If A <~> B then B <~> A
qeqv_sym : forall A, B. A <~> B -> B <~> A
qeqv_sym ((f, g) ** (p, q)) = ((g, f) ** (q, p))

-- Transitivity : If A <~> B and B <~> C then A <~> B
qeqv_trans : forall A, C, B. A <~> B -> B <~> C -> A <~> C
qeqv_trans ((c, d) ** (p, q)) ((f, g) ** (r, s)) =
  let fc : A -> C
      fc = f . c
      dg : C -> A
      dg = d . g
      dgfc : (a : A) -> dg (fc a) =:= a
      dgfc a = ap d (r (c a)) <> p a
      fcdg : (c : C) -> fc (dg c) =:= c
      fcdg c = ap f (q (g c)) <> s c
  in ((fc, dg) ** (dgfc, fcdg))

-- Convenient infix form for qeqv_trans
infixr 8 <->
(<->) : forall A, C, B. A <~> B -> B <~> C -> A <~> C
(<->) = qeqv_trans


-- Get the "to" direction of the quasi-equivalence
qeqvTo : forall A, B. A <~> B -> (A -> B)
qeqvTo ((f, g) ** _) = f

-- Get the "from" direction of the quasi-equivalence
qeqvFrom : forall A, B. A <~> B -> (B -> A)
qeqvFrom ((f, g) ** _) = g

-- Handy converters between quasi-invertibility proofs and quasi-equivalence proofs
qinvToQeqv : forall A, B. (f : A -> B) -> qinv f -> A <~> B
qinvToQeqv f (g ** (gf, fg)) = ((f, g) ** (gf, fg))

qeqvToQinv : forall A, B. A <~> B -> (f : A -> B ** qinv f)
qeqvToQinv ((f, g) ** (gf, fg)) = (f ** (g ** (gf, fg)))

-- Convert equality to quasi-equivalence
eqToQeqv : {A, B : Type} -> A =:= B -> A <~> B
eqToQeqv p =
  J (\x, y, _ => x <~> y) (\_ => qeqv_refl) p


-- A specific transport-like lemma for quasi-equivalence that we'll need later
qeqv_transport : forall A. {B : A -> Type} -> {P, Q : (a : A) -> B a -> Type} ->
  ((a : A) -> (u : B a) -> P a u <~> Q a u) -> ((a : A ** (u : B a ** P a u)) <~> (a : A ** (u : B a ** Q a u)))
qeqv_transport h =
  let f : (a : A ** (u : B a ** P a u)) -> (a : A ** (u : B a ** Q a u))
      f (a ** (u ** p)) = (a ** (u ** (fst (fst (h a u))) p))
      g : (a : A ** (u : B a ** Q a u)) -> (a : A ** (u : B a ** P a u))
      g (a ** (u ** q)) = (a ** (u ** (snd (fst (h a u))) q))
      gf : (aup : (a : A ** (u : B a ** P a u))) -> g (f aup) =:= aup
      gf (a ** (u ** p)) = ap (\p => (a ** (u ** p))) ((fst (snd (h a u))) p)
      fg : (auq : (a : A ** (u : B a ** Q a u))) -> f (g auq) =:= auq
      fg (a ** (u ** q)) = ap (\q => (a ** (u ** q))) ((snd (snd (h a u))) q)
  in ((f, g) ** (gf, fg))
