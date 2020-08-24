{-
  Chapter 2: Homotopy Type Theory
-}

import TypeTheory

-- Path induction with types abstracted

Dtype : Type -> Type
Dtype atype = (x, y : atype) -> x === y -> Type

J : forall A. (D : Dtype A) ->
  (d : (a : A) -> D a a Refl) ->
  (x, y : A) -> (p : x === y) -> D x y p
J = ind_id

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
invert {x} {y} p = J (\x, y, _ => y === x) (\_ => Refl) x y p

-- Transitivity: If x = y and y = z then x = z
concat : forall A. {x, y, z : A} -> x === y -> y === z -> x === z
concat {x} {y} {z} p q =
  let D : Dtype A
      D x y _ = (z : A) -> y = z -> x = z
  in J D (\_, _, r => r) x y p z q


-- p = Refl · p
leftId : forall A. (x, y : A) -> (p : x === y) -> p === concat Refl p
leftId x y p = J (\_, _, p => p === concat Refl p) (\_ => Refl) x y p

-- p = p · Refl
rightId : forall A. (x, y : A) -> (p : x === y) -> p === concat p Refl
rightId x y p = J (\_, _, p => p === concat p Refl) (\_ => Refl) x y p

-- p⁻¹ · p = Refl
leftInv : forall A. (x, y : A) -> (p : x === y) -> concat (invert p) p === Refl
leftInv x y p = J (\_, _, p => concat (invert p) p === Refl) (\_ => Refl) x y p

-- p · p⁻¹ = Refl
rightInv : forall A. (x, y : A) -> (p : x === y) -> concat p (invert p) === Refl
rightInv x y p = J (\_, _, p => concat p (invert p) === Refl) (\_ => Refl) x y p

-- (p⁻¹)⁻¹ = p
invertibility : forall A. (x, y : A) -> (p : x === y) -> invert (invert p) === p
invertibility x y p = J (\_, _, p => invert (invert p) === p) (\_ => Refl) x y p

-- p · (q · r) = (p · q) · r
associativity : forall A. (x, y, z, w : A) -> (p : x === y) -> (q : y === z) -> (r : z === w) ->
  concat p (concat q r) === concat (concat p q) r
associativity x y z w p q r =
  let D : Dtype A
      D x y p = (z, w : A) -> (q : y === z) -> (r : z === w) ->
        concat p (concat q r) === concat (concat p q) r
  in J D (\_, _, _, _, _ => Refl) x y p z w q r


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
