{-
  Chapter 2: Homotopy Type Theory

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
infix 8 =:=
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
infixr 9 <>
(<>) : forall A. {x, y, z : A} -> x =:= y -> y =:= z -> x =:= z
p <> q =
  let D : Dtype A
      D x y _ = (z : A) -> y = z -> x = z
  in J D (\_, _, r => r) p z q


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
EckmannHilton _ a x y = ?eh


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

-------------------------------------
---- NON-DEPENDENT PRODUCT TYPES ----
-------------------------------------

-- "Introduction rule": a = a' ∧ b = b' -> (a, b) = (a', b')
prodId : forall A, B. {x, y : (A, B)} -> (fst x =:= fst y, snd x =:= snd y) -> x =:= y
prodId {x = (a, b)} {y = (a', b')} (p, q) =
  let aa' = J (\a, a', p => (a, b) =:= (a', b)) (\_ => Refl) p
      bb' = J (\b, b', q => (a', b) =:= (a', b')) (\_ => Refl) q
  in aa' <> bb'

-- "Elimination rule": (a, b) = (a', b') -> a = a'
prodId_pr1 : forall A, B. {x, y : (A, B)} -> x =:= y -> fst x =:= fst y
prodId_pr1 refl = ap fst refl

-- "Elimination rule": (a, b) = (a', b') -> b = b'
prodId_pr2 : forall A, B. {x, y : (A, B)} -> x =:= y -> snd x =:= snd y
prodId_pr2 refl = ap snd refl

-- "Computation rule": prodId_pr1 (prodId (p, q)) = p
prodId_comp1 : forall A, B. {x, y : (A, B)} -> (p : fst x =:= fst y) -> (q : snd x =:= snd y) ->
  prodId_pr1 (prodId {x} {y} (p, q)) =:= p
prodId_comp1 {x = (a, b)} {y = (a', b')} p q =
  let D : Dtype A
      D a a' p = (q : b =:= b') -> prodId_pr1 (prodId {x = (a, b)} {y = (a', b')} (p, q)) =:= p
      d : (a : A) -> D a a Refl
      d a q =
        let D' : Dtype B
            D' b b' q = prodId_pr1 (prodId {x = (a, b)} {y = (a, b')} (Refl, q)) =:= Refl
        in J D' (\_ => Refl) q
  in J D d p q

-- "Computation rule": prodId_pr2 (prodId (p ∧ q)) = q
prodId_comp2 : forall A, B. {x, y : (A, B)} -> (p : fst x =:= fst y) -> (q : snd x =:= snd y) ->
  prodId_pr2 (prodId {x} {y} (p, q)) =:= q
prodId_comp2 {x = (a, b)} {y = (a', b')} p q =
  let D : Dtype B
      D b b' q = (p : a =:= a') -> prodId_pr2 (prodId {x = (a, b)} {y = (a', b')} (p, q)) =:= q
      d : (b : B) -> D b b Refl
      d b p =
        let D' : Dtype A
            D' a a' p = prodId_pr2 (prodId {x = (a, b)} {y = (a', b)} (p, Refl)) =:= Refl
        in J D' (\_ => Refl) p
  in J D d q p

-- "Uniqueness principle": r = prodId (prodId_pr1 r ∧ prodId_pr2 r)
prodId_uniq : forall A, B. {x, y : (A, B)} -> (r : x =:= y) -> r =:= prodId (prodId_pr1 r, prodId_pr2 r)
prodId_uniq {x = (a, b)} {y = (a', b')} r =
  let D : Dtype (A, B)
      D x y r = r =:= prodId (prodId_pr1 r, prodId_pr2 r)
  in J D (\(_, _) => Refl) r


-- Reflexivity: Refl {z} = prodId (Refl {fst z} ∧ Refl {snd z})
-- Alternatively, prodId_pr1 (Refl {z}) = Refl {fst z} and prodId_pr2 (Refl {z}) = Refl {snd z}
prodId_refl : forall A, B. {z : (A, B)} -> Refl =:= prodId {x = z} {y = z} (Refl, Refl)
prodId_refl {z = (a, b)} = Refl

-- Symmetry : r⁻¹ = prodId ((prodId_pr1 r)⁻¹ ∧ (prodId_pr2 r)⁻¹)
-- Alternatively, prodId (p⁻¹ ∧ q⁻¹) = (prodId (p ∧ q))⁻¹
prodId_sym : forall A, B. {x, y : (A, B)} -> (r : x =:= y) -> invert r =:= prodId (invert (prodId_pr1 r), invert (prodId_pr2 r))
prodId_sym {x = (a, b)} {y = (a', b')} r =
  let D : Dtype (A, B)
      D x y r = invert r =:= prodId (invert (prodId_pr1 r), invert (prodId_pr2 r))
  in J D (\(_, _) => Refl) r

-- Transitivity: p · q = prodId (prodId_pr1 p · prodId_pr1 q ∧ prodId_pr2 p · prodId_pr2 q)
-- Alternatively, prodId (p · q ∧ p' · q') = prodId (p ∧ p') · prodId (q ∧ q')
prodId_trans : forall A, B. {x, y, z : (A, B)} -> (p : x =:= y) -> (q : y =:= z) ->
  p <> q =:= prodId (prodId_pr1 p <> prodId_pr1 q, prodId_pr2 p <> prodId_pr2 q)
prodId_trans {x = (a, b)} {y = (a', b')} {z = (a'', b'')} p q =
  let D : Dtype (A, B)
      D x y p = {z : (A, B)} -> (q : y =:= z) -> p <> q =:= prodId (prodId_pr1 p <> prodId_pr1 q, prodId_pr2 p <> prodId_pr2 q)
      d : (z : (A, B)) -> D z z Refl
      d (_, _) q =
        let D' : Dtype (A, B)
            D' y z q = Refl <> q =:= prodId (prodId_pr1 Refl <> prodId_pr1 q, prodId_pr2 Refl <> prodId_pr2 q)
        in J D' (\(_, _) => Refl) q
  in J D d p q


-- p[(A _, B _)]* x = (p[A] (fst x), p[B] (snd x))
transport_prod : forall Z. {A, B : Z -> Type} -> {z, w : Z} -> (p : z =:= w) -> (x : (A z, B z)) ->
  transport (\z => (A z, B z)) p x =:= (transport A p (fst x), transport B p (snd x))
transport_prod p x =
  let D : Dtype Z
      D z w p = (x : (A z, B z)) -> transport (\z => (A z, B z)) p x =:= (transport A p (fst x), transport B p (snd x))
  in J D (\_, (_, _) => Refl) p x

-- ap (g (fst _), h (snd _)) (prodId (p ∧ q)) = prodId (g(p), h(q))
ap_prod : forall A, B, A', B'. (g : A -> A') -> (h : B -> B') -> {x, y : (A, B)} -> (p : fst x = fst y) -> (q : snd x = snd y) ->
  ap (\x => (g (fst x), h (snd x))) (prodId {x} {y} (p, q)) =:= prodId (ap g p, ap h q)
ap_prod g h {x = (a, b)} {y = (a', b')} p q =
  let D : Dtype A
      D a a' p = (q : b =:= b') -> ap (\x => (g (fst x), h (snd x))) (prodId {x = (a, b)} {y = (a', b')} (p, q)) =:= prodId (ap g p, ap h q)
      d : (a : A) -> D a a Refl
      d a q =
        let D' : Dtype B
            D' b b' q = ap (\x => (g (fst x), h (snd x))) (prodId {x = (a, b)} {y = (a, b')} (Refl, q)) =:= prodId (Refl, ap h q)
        in J D' (\_ => Refl) q
  in J D d p q
