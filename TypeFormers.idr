{-
  Chapter 2: Homotopy Type Theory
  Sections 2.5 to 2.15

  This file covers the type formers:
  * Nondependent and dependent product types
  * The unit type
  * Function types
  * Universes
  * The identity type
  * Coproduct types

  Each comes with four rules, informally stated as:
  * Introduction: If the components are equal then the types formed by them are equal
  * Elimination: If the formed types are equal then their components are equal
  * Computation: Eliminating an introduction gives you the original components
  * Uniqueness: Introducing using eliminated components gives you the original type

  The type formers also have ap and transport lemmas associated with them.

  We will also show that introduction and elimination are quasi-inverses,
  with computation and uniqueness as proofs.
-}

import Homotopy

%default total

-------------------------------------
---- NON-DEPENDENT PRODUCT TYPES ----
-------------------------------------

-- "Introduction rule": a = a' ∧ b = b' -> (a, b) = (a', b')
prodId : forall A, B. {x, y : (A, B)} -> (fst x =:= fst y, snd x =:= snd y) -> x =:= y
prodId {x = (a, b)} {y = (a', b')} (p, q) =
  let aa' = J (\a, a', p => (a, b) =:= (a', b)) (\_ => Refl) p
      bb' = J (\b, b', q => (a', b) =:= (a', b')) (\_ => Refl) q
  in aa' <> bb'

-- "Elimination rule" [fst]: (a, b) = (a', b') -> a = a'
prodId_pr1 : forall A, B. {x, y : (A, B)} -> x =:= y -> fst x =:= fst y
prodId_pr1 p = ap fst p

-- "Elimination rule" [snd]: (a, b) = (a', b') -> b = b'
prodId_pr2 : forall A, B. {x, y : (A, B)} -> x =:= y -> snd x =:= snd y
prodId_pr2 p = ap snd p

-- "Elimination rule": (a, b) = (a', b') -> (a = a' ∧ b = b')
prodId_pr : forall A, B. {x, y : (A, B)} -> x =:= y -> (fst x =:= fst y, snd x =:= snd y)
prodId_pr p = (prodId_pr1 p, prodId_pr2 p)

-- "Computation rule" [fst]: prodId_pr1 (prodId (p ∧ q)) = p
prodId_comp1 : forall A, B. {x, y : (A, B)} -> (pq : (fst x =:= fst y, snd x =:= snd y)) ->
  prodId_pr1 (prodId {x} {y} pq) =:= fst pq
prodId_comp1 {x = (a, b)} {y = (a', b')} (p, q) =
  let D : Dtype A
      D a a' p = (q : b =:= b') -> prodId_pr1 (prodId {x = (a, b)} {y = (a', b')} (p, q)) =:= p
      d : (a : A) -> D a a Refl
      d a q =
        let D' : Dtype B
            D' b b' q = prodId_pr1 (prodId {x = (a, b)} {y = (a, b')} (Refl, q)) =:= Refl
        in J D' (\_ => Refl) q
  in J D d p q

-- "Computation rule" [snd]: prodId_pr2 (prodId (p ∧ q)) = q
prodId_comp2 : forall A, B. {x, y : (A, B)} -> (pq : (fst x =:= fst y, snd x =:= snd y)) ->
  prodId_pr2 (prodId {x} {y} pq) =:= snd pq
prodId_comp2 {x = (a, b)} {y = (a', b')} (p, q) =
  let D : Dtype B
      D b b' q = (p : a =:= a') -> prodId_pr2 (prodId {x = (a, b)} {y = (a', b')} (p, q)) =:= q
      d : (b : B) -> D b b Refl
      d b p =
        let D' : Dtype A
            D' a a' p = prodId_pr2 (prodId {x = (a, b)} {y = (a', b)} (p, Refl)) =:= Refl
        in J D' (\_ => Refl) p
  in J D d q p

-- "Computation rule": prodId_pr (prodId (p ∧ q)) = (p ∧ q)
prodId_comp : forall A, B. {x, y : (A, B)} -> (pq : (fst x =:= fst y, snd x =:= snd y)) ->
  prodId_pr (prodId {x} {y} pq) =:= pq
prodId_comp {x = (a, b)} {y = (a', b')} pq =
  let comp1 = prodId_comp1 {x = (a, b)} {y = (a', b')} pq
      comp2 = prodId_comp2 {x = (a, b)} {y = (a', b')} pq
  in prodId (comp1, comp2)

-- "Uniqueness principle": prodId (prodId r) = r
prodId_uniq : forall A, B. {x, y : (A, B)} -> (r : x =:= y) -> prodId (prodId_pr r) =:= r
prodId_uniq {x = (a, b)} {y = (a', b')} r =
  let D : Dtype (A, B)
      D x y r = prodId (prodId_pr r) =:= r
  in J D (\(_, _) => Refl) r

-- prodId is a quasi-equivalence from (a = a', b = b') to (a, b) = (a', b')
prodId_qinv : forall A, B. {x, y : (A, B)} -> qinv (prodId {x} {y})
prodId_qinv = (prodId_pr ** (prodId_comp, prodId_uniq))


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


-- p[(A _, B _)]* x = (p[A]* (fst x), p[B]* (snd x))
transport_prod : forall Z. {A, B : Z -> Type} -> {z, w : Z} -> (p : z =:= w) -> (x : (A z, B z)) ->
  transport (\z => (A z, B z)) p x =:= (transport A p (fst x), transport B p (snd x))
transport_prod p x =
  let D : Dtype Z
      D z w p = (x : (A z, B z)) -> transport (\z => (A z, B z)) p x =:= (transport A p (fst x), transport B p (snd x))
  in J D (\_, (_, _) => Refl) p x

-- ap (g (fst _), h (snd _)) (prodId (p ∧ q)) = prodId (g(p), h(q))
ap_prod : forall A, B, A', B'. (g : A -> A') -> (h : B -> B') -> {x, y : (A, B)} -> (p : fst x =:= fst y) -> (q : snd x =:= snd y) ->
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

---------------------------------
---- DEPENDENT PRODUCT TYPES ----
---------------------------------

-- "Introduction rule": ∃(p : a = a') s.t. p*(b) = b' -> (a ** b) = (a' ** b')
dprodId : forall A. {P : A -> Type} -> {w, w' : (x : A ** P x)} ->
  (p : fst w =:= fst w' ** transport P p (snd w) =:= snd w') -> w =:= w'
dprodId {w = (a ** b)} {w' = (a' ** b')} (p ** q) =
  let D : Dtype A
      D a a' p = {b : P a} -> {b' : P a'} -> transport P p b =:= b' -> MkDPair {p = P} a b =:= MkDPair {p = P} a' b'
      d : (a : A) -> D a a Refl
      d a q =
        let D' : Dtype (P a)
            D' b b' q = MkDPair {p = P} a b =:= MkDPair {p = P} a b'
        in J D' (\_ => Refl) q
  in J D d p q

-- "Elimination rule": (a ** b) = (a' ** b') -> ∃(p : a = a') s.t. p*(b) = b'
dprodId_pr : forall A. {P : A -> Type} -> {w, w' : (x : A ** P x)} ->
  w =:= w' -> (p : fst w =:= fst w' ** transport P p (snd w) =:= snd w')
dprodId_pr q =
  let D : Dtype (x : A ** P x)
      D w w' _ = (p : fst w =:= fst w' ** transport P p (snd w) =:= snd w')
  in J D (\_ => (Refl ** Refl)) q

-- "Computation rule": (dprodId_pr (dprodId (p ** q))) = p ** q
dprodId_comp : forall A. {P : A -> Type} -> {w, w' : (x : A ** P x)} ->
  (r : (p : fst w =:= fst w' ** transport P p (snd w) =:= snd w')) -> dprodId_pr (dprodId {w} {w'} r) =:= r
dprodId_comp {w = (a ** b)} {w' = (a' ** b')} (p ** q) =
  let D : Dtype A
      D a a' p = {b : P a} -> {b' : P a'} -> (q : transport P p b =:= b') ->
        dprodId_pr (dprodId {w = (a ** b)} {w' = (a' ** b')} (p ** q)) =:= (p ** q)
      d : (a : A) -> D a a Refl
      d a q =
        let D' : Dtype (P a)
            D' b b' q = dprodId_pr (dprodId {w = (a ** b)} {w' = (a ** b')} (Refl ** q)) =:= (MkDPair {p = \p => transport P p b =:= b'} Refl q)
        in J D' (\_ => Refl) q
  in J D d p q

-- "Uniqueness principle": dprodId (dprodId_pr r) = r
dprodId_uniq : forall A. {P : A -> Type} -> {w, w' : (x : A ** P x)} -> (r : w =:= w') -> dprodId (dprodId_pr r) =:= r
dprodId_uniq {w = (a ** b)} {w' = (a' ** b')} r =
  let D : Dtype (x : A ** P x)
      D x y r = dprodId (dprodId_pr r) =:= r
  in J D (\(_ ** _) => Refl) r

-- dprodId is a quasi-equivalence from (a = a' ** b = b') to (a ** b) = (a' ** b')
dprodId_qinv : forall A. {P : A -> Type} -> {w, w' : (x : A ** P x)} -> qinv (dprodId {w} {w'})
dprodId_qinv = (dprodId_pr ** (dprodId_comp, dprodId_uniq))


-- p[(u : P _ ** Q (_ ** u))]* w = (p[P]* (fst x) ** (dprodId (p ** Refl))[Q]* (snd x))
transport_dprod : forall A. {P : A -> Type} -> {Q : (x : A ** P x) -> Type} -> {x, y : A} -> (p : x =:= y) -> (w : (u : P x ** Q (x ** u))) ->
  transport (\z => (u : P z ** Q (z ** u))) p w =:= (transport P p (fst w) ** transport Q (dprodId (p ** Refl)) (snd w))
transport_dprod p w =
  let D : Dtype A
      D x y p = (w : (u : P x ** Q (x ** u))) ->
        transport (\z => (u : P z ** Q (z ** u))) p w =:= (transport P p (fst w) ** transport Q (dprodId (p ** Refl)) (snd w))
  in J D (\_, (_ ** _) => Refl) p w

-- ap (g _ ** h _) p = dprodId (g(p) ** (transport_ap g p (h x))⁻¹ · h(p))
ap_dprod : forall A, A'. {P : A' -> Type} -> (g : A -> A') -> (h : (a : A) -> P (g a)) -> {x, y : A} -> (p : x =:= y) ->
  ap (\z => (g z ** h z)) p =:= dprodId {P} (ap g p ** invert (transport_ap g {P} p (h x)) <> apd h p)
ap_dprod g h p =
  let D : Dtype A
      D x y p = ap (\z => (g z ** h z)) p =:= dprodId {P} (ap g p ** invert (transport_ap g {P} p (h x)) <> apd h p)
  in J D (\_ => Refl) p

-------------------
---- UNIT TYPE ----
-------------------

-- "Introduction rule": () -> () = ()
unitId : {x, y : Unit} -> Unit -> x =:= y
unitId {x = ()} {y = ()} () = Refl

-- "Elimination rule": () = () -> ()
unitId_elim : {x, y : Unit} -> x =:= y -> Unit
unitId_elim _ = ()

-- "Computation rule": unitId_elim (unitId ()) = ()
unitId_comp : {u : Unit} -> unitId_elim (unitId u) = u
unitId_comp {u = ()} = Refl

-- "Uniqueness principle": unitId (unitId_elim p) = p
unitId_uniq : {x, y : Unit} -> (p : x =:= y) -> unitId (unitId_elim p) = p
unitId_uniq {x = ()} {y = ()} p =
  J (\(), (), p => unitId (unitId_elim p) = p) (\() => Refl) p
