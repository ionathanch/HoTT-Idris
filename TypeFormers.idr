{-
  Chapter 2: Homotopy Type Theory
  Sections 2.5 to 2.13, 2.14

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

  Finally, we have the universal properties of these type formers.
-}

import TypeTheory
import Homotopy
import FunExt

%default total

-------------------------------------
---- NON-DEPENDENT PRODUCT TYPES ----
-------------------------------------

-- Introduction rule: a = a' ∧ b = b' -> (a, b) = (a', b')
prodId : forall A, B. {x, y : (A, B)} -> (fst x =:= fst y, snd x =:= snd y) -> x =:= y
prodId {x = (a, b)} {y = (a', b')} (p, q) =
  let aa' = J (\a, a', p => (a, b) =:= (a', b)) (\_ => Refl) p
      bb' = J (\b, b', q => (a', b) =:= (a', b')) (\_ => Refl) q
  in aa' <> bb'

-- Elimination rule [fst]: (a, b) = (a', b') -> a = a'
prodId_pr1 : forall A, B. {x, y : (A, B)} -> x =:= y -> fst x =:= fst y
prodId_pr1 p = ap fst p

-- Elimination rule [snd]: (a, b) = (a', b') -> b = b'
prodId_pr2 : forall A, B. {x, y : (A, B)} -> x =:= y -> snd x =:= snd y
prodId_pr2 p = ap snd p

-- Elimination rule: (a, b) = (a', b') -> (a = a' ∧ b = b')
prodId_pr : forall A, B. {x, y : (A, B)} -> x =:= y -> (fst x =:= fst y, snd x =:= snd y)
prodId_pr p = (prodId_pr1 p, prodId_pr2 p)

-- Computation rule [fst]: prodId_pr1 (prodId (p ∧ q)) = p
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

-- Computation rule [snd]: prodId_pr2 (prodId (p ∧ q)) = q
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

-- Computation rule: prodId_pr (prodId (p ∧ q)) = (p ∧ q)
prodId_comp : forall A, B. {x, y : (A, B)} -> (pq : (fst x =:= fst y, snd x =:= snd y)) ->
  prodId_pr (prodId {x} {y} pq) =:= pq
prodId_comp {x = (a, b)} {y = (a', b')} pq =
  let comp1 = prodId_comp1 {x = (a, b)} {y = (a', b')} pq
      comp2 = prodId_comp2 {x = (a, b)} {y = (a', b')} pq
  in prodId (comp1, comp2)

-- Uniqueness principle: prodId (prodId r) = r
prodId_uniq : forall A, B. {x, y : (A, B)} -> (r : x =:= y) -> prodId (prodId_pr r) =:= r
prodId_uniq {x = (a, b)} {y = (a', b')} r =
  let D : Dtype (A, B)
      D x y r = prodId (prodId_pr r) =:= r
  in J D (\(_, _) => Refl) r

-- (a = a', b = b') <~> (a, b) = (a', b')
prodId_qinv : forall A, B. {a, a' : A} -> {b, b' : B} -> (a =:= a', b =:= b') <~> (a, b) =:= (a', b')
prodId_qinv = ((prodId, prodId_pr) ** (prodId_comp, prodId_uniq))


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

-- Introduction rule: ∃(p : a = a') s.t. p*(b) = b' -> (a ** b) = (a' ** b')
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

-- Elimination rule: (a ** b) = (a' ** b') -> ∃(p : a = a') s.t. p*(b) = b'
dprodId_pr : forall A. {P : A -> Type} -> {w, w' : (x : A ** P x)} ->
  w =:= w' -> (p : fst w =:= fst w' ** transport P p (snd w) =:= snd w')
dprodId_pr q =
  let D : Dtype (x : A ** P x)
      D w w' _ = (p : fst w =:= fst w' ** transport P p (snd w) =:= snd w')
  in J D (\_ => (Refl ** Refl)) q

-- Computation rule: (dprodId_pr (dprodId (p ** q))) = p ** q
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

-- Uniqueness principle: dprodId (dprodId_pr r) = r
dprodId_uniq : forall A. {P : A -> Type} -> {w, w' : (x : A ** P x)} -> (r : w =:= w') -> dprodId (dprodId_pr r) =:= r
dprodId_uniq {w = (a ** b)} {w' = (a' ** b')} r =
  let D : Dtype (x : A ** P x)
      D x y r = dprodId (dprodId_pr r) =:= r
  in J D (\(_ ** _) => Refl) r

-- (a = a' ** b = b') <~> (a ** b) = (a' ** b')
dprodId_qinv : forall A. {P : A -> Type} -> {a, a' : A} -> {b : P a} -> {b' : P a'} ->
  (p : a =:= a' ** transport P p b =:= b') <~> (MkDPair {p = P} a b =:= MkDPair {p = P} a' b')
dprodId_qinv = ((dprodId, dprodId_pr) ** (dprodId_comp, dprodId_uniq))


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

-- Introduction rule: () -> () = ()
unitId : {x, y : Unit} -> Unit -> x =:= y
unitId {x = ()} {y = ()} () = Refl

-- Elimination rule: () = () -> ()
unitId_elim : {x, y : Unit} -> x =:= y -> Unit
unitId_elim _ = ()

-- Computation rule: unitId_elim (unitId ()) = ()
unitId_comp : {u : Unit} -> unitId_elim (unitId u) = u
unitId_comp {u = ()} = Refl

-- Uniqueness principle: unitId (unitId_elim p) = p
unitId_uniq : {x, y : Unit} -> (p : x =:= y) -> unitId (unitId_elim p) = p
unitId_uniq {x = ()} {y = ()} p =
  J (\(), (), p => unitId (unitId_elim p) = p) (\() => Refl) p

------------------------
---- FUNCTION TYPES ----
------------------------

-- p[A _ -> B _]* f = (\x => p[B]* (f (p⁻¹[A]* x)))
transport_fun : forall X. {A, B : X -> Type} -> {x1, x2 : X} -> (p : x1 =:= x2) -> (f : A x1 -> B x1) ->
  transport (\x => A x -> B x) p f =:= (\x => transport B p (f (transport A (invert p) x)))
transport_fun p f =
  let D : Dtype X
      D x1 x2 p = (f : A x1 -> B x1) -> transport (\x => A x -> B x) p f =:= (\x => transport B p (f (transport A (invert p) x)))
  in J D (\_, _ => funext (\_ => Refl)) p f

-- I have no idea what's going on here
transport_dfun : forall X. {A : X -> Type} -> {B : (x : X) -> A x -> Type} -> {x1, x2 : X} ->
  (p : x1 =:= x2) -> (f : (a : A x1) -> B x1 a) -> (a : A x2) ->
  let AB : X -> Type
      AB x = (a : A x) -> B x a
      Bhat : (x : X ** A x) -> Type
      Bhat w = B (fst w) (snd w)
      a' : A x1
      a' = transport A (invert p) a
      q : (MkDPair {p = A} x1 a') =:= (MkDPair {p = A} x2 a)
      q = invert (dprodId (invert p ** Refl))
  in transport AB p f a =:= transport Bhat q (f a')
transport_dfun p f a =
  let D : Dtype X
      D x1 x2 p = (f : (a : A x1) -> B x1 a) -> (a : A x2) ->
        let AB : X -> Type
            AB x = (a : A x) -> B x a
            Bhat : (x : X ** A x) -> Type
            Bhat w = B (fst w) (snd w)
            a' : A x1
            a' = transport A (invert p) a
            q : MkDPair {p = A} x1 a' =:= MkDPair {p = A} x2 a
            q = invert (dprodId (invert p ** Refl))
        in transport AB p f a =:= transport Bhat q (f a')
  in J D (\_, _, _ => Refl) p f a


-- p[A _ -> B _]* f = g <~> ∀(a : A x), p[B]* (f a) = g (p[A]* a)
ap_fun : forall X. {A, B : X -> Type} -> {x, y : X} -> (p : x =:= y) -> (f : A x -> B x) -> (g : A y -> B y) ->
  transport (\z => A z -> B z) p f =:= g <~> (a : A x) -> (transport B p (f a) =:= g (transport A p a))
ap_fun p f g =
  let D : Dtype X
      D x y p = (f : A x -> B x) -> (g : A y -> B y) ->
        transport (\z => A z -> B z) p f =:= g <~> (a : A x) -> transport B p (f a) =:= g (transport A p a)
  in J D (\_, _, _ => fun_qinv) p f g

-- I don't know what this is and I don't know how to name it
ap_fun_q : forall X. {A, B : X -> Type} -> {x, y : X} -> (p : x =:= y) -> (f : A x -> B x) -> (g : A y -> B y) ->
  (q : transport (\z => A z -> B z) p f =:= g) -> (a : A x) ->
  let i : transport (\z => A z -> B z) p f (transport A p a) =:= transport B p (f (transport A (invert p) (transport A p a)))
      i = happly (transport_fun p f) (transport A p a)
      j : transport B p (f (transport A (invert p) (transport A p a))) =:= transport B p (f a)
      j = let j1 : transport A (invert p) (transport A p a) =:= transport A (p <> invert p) a
              j1 = transport_distrib p (invert p) a
              j2 : transport A (p <> invert p) a =:= a
              j2 = ap (\p => transport A p a) (rightInv p)
          in ap (transport B p . f) (j1 <> j2)
      k : transport B p (f a) =:= g (transport A p a)
      k = (qeqTo (ap_fun p f g)) q a
  in happly q (transport A p a) =:= i <> j <> k
ap_fun_q p f g q a =
  let D : Dtype X
      D x y p = (f : A x -> B x) -> (g : A y -> B y) -> (q : transport (\z => A z -> B z) p f =:= g) -> (a : A x) ->
        let i : transport (\z => A z -> B z) p f (transport A p a) =:= transport B p (f (transport A (invert p) (transport A p a)))
            i = happly (transport_fun p f) (transport A p a)
            j : transport B p (f (transport A (invert p) (transport A p a))) =:= transport B p (f a)
            j = let j1 : transport A (invert p) (transport A p a) =:= transport A (p <> invert p) a
                    j1 = transport_distrib p (invert p) a
                    j2 : transport A (p <> invert p) a =:= a
                    j2 = ap (\p => transport A p a) (rightInv p)
                in ap (transport B p . f) (j1 <> j2)
            k : transport B p (f a) =:= g (transport A p a)
            k = (qeqTo (ap_fun p f g)) q a
        in happly q (transport A p a) =:= i <> j <> k
      d : (x : X) -> (f, g : A x -> B x) -> (q : f =:= g) -> (a : A x) ->
        happly q a =:= happly (funext {f = f} {g = f} (\_ => Refl)) a <> happly q a
      d x f g q a = invert (happly (fun_comp (\_ => Refl)) a |> happly q a)
  in J D d p f g q a

-- I have no idea what's going on here either
ap_dfun : forall X. {A : X -> Type} -> {B : (x : X) -> A x -> Type} -> {x, y : X} -> (p : x =:= y) ->
  (f : (a : A x) -> B x a) -> (g : (a : A y) -> B y a) ->
  transport (\z => (a : A z) -> B z a) p f =:= g <~> (a : A x) ->
    let Bhat : (x : X ** A x) -> Type
        Bhat w = B (fst w) (snd w)
        a' : A y
        a' = transport A p a
        q : MkDPair {p = A} x a =:= MkDPair {p = A} y a'
        q = dprodId (p ** Refl)
    in transport Bhat q (f a) = g a'
ap_dfun p f g =
  let D : Dtype X
      D x y p = (f : (a : A x) -> B x a) -> (g : (a : A y) -> B y a) ->
        transport (\z => (a : A z) -> B z a) p f =:= g <~> (a : A x) ->
          let Bhat : (x : X ** A x) -> Type
              Bhat w = B (fst w) (snd w)
              a' : A y
              a' = transport A p a
              q : MkDPair {p = A} x a =:= MkDPair {p = A} y a'
              q = dprodId (p ** Refl)
          in transport Bhat q (f a) = g a'
  in J D (\_, _, _ => fun_qinv) p f g

------------------------
---- IDENTITY TYPES ----
------------------------

{- 
  We use the book's names here rather than our conventions
  *Id, *Id_elim, *Id_comp, *Id_uniq, transport_*, ap_*
  since these seems to differ from this pattern a bit here.
-}

ap_inv : forall A, B. (f : A -> B) -> qinv f -> {a, a' : A} -> f a =:= f a' -> a =:= a'
ap_inv f (g ** (alpha, beta)) q = ((invert (alpha a)) <> ap g q) <> alpha a'

ap_comp : forall A, B. (f : A -> B) -> (g : qinv f) -> {a, a' : A} -> (p : a =:= a') -> ap_inv f g (ap f p) =:= p
ap_comp f (g ** (alpha, beta)) p =
  let alpha' : Prelude.id ~~ g . f
      alpha' a = invert (alpha a)
      ap_func : alpha' a <> ap g (ap f p) =:= alpha' a <> ap (g . f) p
      ap_func = alpha' a <| ap_concat f g p
      ap_nat : alpha' a <> ap (g . f) p =:= p <> alpha' a'
      ap_nat = naturality alpha' p <> ap_ident p |> alpha' a'
      ap_res : (alpha' a <> ap g (ap f p)) <> alpha a' =:= p <> alpha' a' <> alpha a'
      ap_res = ((ap_func <> ap_nat) |> alpha a') <> invert (associativity p (alpha' a') (alpha a'))
      cancelRight : p <> alpha' a' <> alpha a' =:= p
      cancelRight = (p <| leftInv (alpha a')) <> invert (rightId p)
  in ap_res <> cancelRight

ap_uniq : forall A, B. (f : A -> B) -> (g : qinv f) -> {a, a' : A} -> (q : f a =:= f a') -> ap f (ap_inv f g q) =:= q
ap_uniq f (g ** (alpha, beta)) q =
  let beta' : Prelude.id ~~ f . g
      beta' a = invert (beta a)
      apapinv : f a =:= f a'
      apapinv = ap f ((invert (alpha a) <> ap g q) <> alpha a')
      apu1 : apapinv =:= beta' (f a) <> beta (f a) <> apapinv
      apu1 = leftId apapinv
        <> (invert (leftInv (beta (f a))) |> apapinv)
        <> invert (associativity (beta' (f a)) (beta (f a)) apapinv)
      apu2 : beta' (f a) <> beta (f a) <> apapinv =:= (beta' (f a) <> (beta (f a) <> apapinv) <> beta' (f a')) <> beta (f a')
      apu2 = rightId (beta' (f a) <> beta (f a) <> apapinv)
        <> ((beta' (f a) <> beta (f a) <> apapinv) <| invert (leftInv (beta (f a'))))
        <> associativity (beta' (f a) <> beta (f a) <> apapinv) (beta' (f a')) (beta (f a'))
        <> (invert (associativity (beta' (f a)) (beta (f a) <> apapinv) (beta' (f a'))) |> beta (f a'))
      apu3 : (beta' (f a) <> (beta (f a) <> apapinv) <> beta' (f a')) <> beta (f a') =:= q
      apu3 = believe_me () -- I swear it's true. Theorem 2.11.1
  in apu1 <> apu2 <> apu3

ap_qinv : forall A, B. (f : A -> B) -> qinv f -> {a, a' : A} -> a =:= a' <~> f a =:= f a'
ap_qinv f g = ((ap f, ap_inv f g) ** (ap_comp f g, ap_uniq f g))

transport_concatl : forall A. {a, x1, x2 : A} -> (p : x1 =:= x2) -> (q : a =:= x1) ->
  transport (\x => a =:= x) p q =:= q <> p
transport_concatl p q =
  let D : Dtype A
      D x1 x2 p = (q : a =:= x1) -> transport (\x => a =:= x) p q =:= q <> p
  in J D (\_, q => rightId q) p q

transport_concatr : forall A. {a, x1, x2 : A} -> (p : x1 =:= x2) -> (q : x1 =:= a) ->
  transport (\x => x =:= a) p q =:= (invert p) <> q
transport_concatr p q =
  let D : Dtype A
      D x1 x2 p = (q : x1 =:= a) -> transport (\x => x =:= a) p q =:= (invert p) <> q
  in J D (\_, q => leftId q) p q

transport_concat : forall A. {a, x1, x2 : A} -> (p : x1 =:= x2) -> (q : x1 =:= x1) ->
  transport (\x => x =:= x) p q =:= (invert p) <> q <> p
transport_concat p q =
  let D : Dtype A
      D x1 x2 p = (q : x1 =:= x1) -> transport (\x => x =:= x) p q =:= (invert p) <> q <> p
  in J D (\_, q => rightId q) p q

------------------------------
---- UNIVERSAL PROPERTIES ----
------------------------------

-- Universal property for nondependent products : (X -> (A, B)) -> (X -> A, X -> B)
prod_univ : forall X, A, B. (X -> (A, B)) -> (X -> A, X -> B)
prod_univ f = (\x => fst (f x), \x => snd (f x))

-- Quasi-inverse of prod_univ
prod_vinu : forall X, A, B. (X -> A, X -> B) -> (X -> (A, B))
prod_vinu (f, g) x = (f x, g x)

-- The universal property for nondependent products is a quasi-equivalence

prod_uv : forall X, A, B. (fg : (X -> A, X -> B)) -> prod_univ (prod_vinu fg) =:= fg
prod_uv (f, g) = rewrite eta f in rewrite eta g in Refl

prod_vu : forall X. {A, B : Type} -> (f : X -> (A, B)) -> prod_vinu (prod_univ f) =:= f
prod_vu f = funext (\x => uniq_prod (f x))

prod_univ_qinv : forall X. {A, B : Type} -> (X -> (A, B)) <~> (X -> A, X -> B)
prod_univ_qinv = ((prod_univ, prod_vinu) ** (prod_vu, prod_uv))


-- Universal property for dependent products: ∀(x : X) (A x, B x) -> (∀(x : X) A x, ∀(x : X) B x)
dprod_univ : forall X. {A, B : X -> Type} -> ((x : X) -> (A x, B x)) -> ((x : X) -> A x, (x : X) -> B x)
dprod_univ f = (\x => fst (f x), \x => snd (f x))

-- Quasi-inverse of dprod_univ
dprod_vinu : forall X. {A, B : X -> Type} -> ((x : X) -> A x, (x : X) -> B x) -> ((x : X) -> (A x, B x))
dprod_vinu (f, g) x = (f x, g x)

-- The universal property for dependent products is a quasi-equivalence

dprod_uv : forall X. {A, B : X -> Type} -> (fg : ((x : X) -> A x, (x : X) -> B x)) -> dprod_univ (dprod_vinu fg) =:= fg
dprod_uv (f, g) = rewrite eta f in rewrite eta g in Refl

dprod_vu : forall X. {A, B : X -> Type} -> (f : (x : X) -> (A x, B x)) -> dprod_vinu (dprod_univ f) =:= f
dprod_vu f = funext (\x => uniq_prod (f x))

dprod_univ_qinv : forall X. {A, B : X -> Type} -> ((x : X) -> (A x, B x)) <~> ((x : X) -> A x, (x : X) -> B x)
dprod_univ_qinv = ((dprod_univ, dprod_vinu) ** (dprod_vu, dprod_uv))


-- The axiom of choice: ∀(x : X), ∃(a : A x) s.t. P x a -> ∃(g : (x : X) -> A x) s.t. ∀(x : X), P x (g x)
ac : forall X. {A : X -> Type} -> {P : (x : X) -> (a : A x) -> Type} ->
  (f : (x : X) -> (a : A x ** P x a)) -> (g : (x : X) -> A x ** (x : X) -> P x (g x))
ac f = MkDPair {a = (x : X) -> A x} (\x => fst (f x)) (\x => snd (f x))

-- Quasi-inverse of the axiom of choice
ac_inv : forall X. {A : X -> Type} -> {P : (x : X) -> (a : A x) -> Type} ->
  (gh : (g : (x : X) -> A x ** (x : X) -> P x (g x))) -> ((x : X) -> (a : A x ** P x a))
ac_inv (g ** h) x = (g x ** h x)

-- The axiom of choice is a quasi-equivalence

ac_comp : forall X. {A : X -> Type} -> {P : (x : X) -> (a : A x) -> Type} ->
  (gh : (g : (x : X) -> A x ** (x : X) -> P x (g x))) -> ac {P} (ac_inv {P} gh) =:= gh
ac_comp (g ** h) = rewrite eta g in rewrite eta h in Refl

ac_uniq : forall X. {A : X -> Type} -> {P : (x : X) -> (a : A x) -> Type} ->
  (f : (x : X) -> (a : A x ** P x a)) -> ac_inv {P} (ac {P} f) =:= f
ac_uniq f = funext (\x => uniq_dprod (f x))

ac_qinv : forall X. {A : X -> Type} -> {P : (x : X) -> (a : A x) -> Type} ->
  ((x : X) -> (a : A x ** P x a)) <~> (g : (x : X) -> A x ** (x : X) -> P x (g x))
ac_qinv = ((ac, ac_inv) ** (ac_uniq, ac_comp))
