{-
  Chapter 3: Sets and Logic
-}

import TypeTheory
import Homotopy
import TypeFormers
import FunExt

%default total

--------------
---- SETS ----
--------------

-- Definition: Sets (0-types)
isSet : (A : Type) -> Type
isSet a = (x, y : a) -> (p, q : x =:= y) -> p =:= q

-- Definition: Homotopy 1-types
isOne : (A : Type) -> Type
isOne a = (x, y : a) -> (p, q : x =:= y) -> (r, s : p =:= q) -> r =:= s

-- If A is a 0-type then A is a 1-type
setIsOne: forall A. isSet A -> isOne A
setIsOne f x y p q r s =
  let g : (q : x =:= y) -> p =:= q
      g q = f x y p q
      apdg : {p, q : x =:= y} -> (t : p =:= q) -> g p <> t =:= g q
      apdg {p} {q} t = invert (transport_concatl t (g p)) <> apd g t
      gprs : g p <> r =:= g p <> s
      gprs = apdg r <> invert (apdg s)
  in leftCancel (g p) r s gprs

----------------------
---- PROPOSITIONS ----
----------------------

-- Definition: Mere propositions
isProp : (P : Type) -> Type
isProp p = (x, y : p) -> x =:= y

-- If propositions are logically equivalent then they are quasi-equivalent
logicalEquiv : forall P, Q. isProp P -> isProp Q -> (P -> Q) -> (Q -> P) -> P <~> Q
logicalEquiv propP propQ f g =
  ((f, g) ** (\p => propP (g (f p)) p, \q => propQ (f (g q)) q))

-- Mere propositions are quasi-equivalent to unit
propUnit : forall P. isProp P -> (x : P) -> P <~> Unit
propUnit propP x = logicalEquiv propP (\(), () => Refl) (\_ => ()) (\() => x)

-- Mere propsitions are sets
propIsSet : forall P. isProp P -> isSet P
propIsSet f x y p q =
  let g : (y : P) -> x =:= y
      g y = f x y
      apdg : {x, y : P} -> (p : x =:= y) -> g x <> p =:= g y
      apdg {x} {y} p = invert (transport_concatl p (g x)) <> apd g p
      gxpq : g x <> p =:= g x <> q
      gxpq = apdg p <> invert (apdg q)
  in leftCancel (g x) p q gxpq

-- isProp is a mere proposition
isPropIsProp : forall P. isProp (isProp P)
isPropIsProp f g =
  let fgxy : (x, y : P) -> f x y =:= g x y
      fgxy x y = propIsSet f x y (f x y) (g x y)
  in funext (\x => funext (fgxy x))

-- isSet is a mere proposition
isSetIsProp : forall A. isProp (isSet A)
isSetIsProp f g =
  let fgxypq : (x, y : A) -> (p, q : x =:= y) -> f x y p q =:= g x y p q
      fgxypq x y p q = setIsOne f x y p q (f x y p q) (g x y p q)
  in funext (\x => funext (\y => funext (\p => funext (fgxypq x y p))))

--------------------------------
---- LOGIC and DECIDABILITY ----
--------------------------------

-- Definition: Law of excluded middle
LEM : Type
LEM = (A : Type) -> isProp A -> A # Not A

-- Definition: Law of double negation
LDN : Type
LDN = (A : Type) -> isProp A -> (Not (Not A) -> A)

-- Definition: Decidability of a type
decType : (A : Type) -> Type
decType a = a # Not a

-- Definition: Decidability of a type family
decTypeFam : forall A. (B : A -> Type) -> Type
decTypeFam b = (a : A) -> b a # Not (b a)

-- Definition: Decidability of equality of a type
decEq : (A : Type) -> Type
decEq a = (b, c : a) -> b =:= c # Not (b =:= c)

------------------
---- SUBTYPES ----
------------------

-- If P is a proposition, ux = uv, and we have proofs of P ux and P vx,
-- then those proofs must be equal.
propNoSub : forall A. {P : A -> Type} -> ((x : A) -> isProp (P x)) ->
  (u, v : DPair A P) -> fst u =:= fst v -> u =:= v
propNoSub f (ux ** pu) (vx ** pv) p =
  dprodId (p ** f vx (transport P p pu) pv)

-- Definition: a ∈ P
member : forall A. (a : A) -> (P : A -> Type) -> Type
member a p = p a

-- Definition: P ⊆ Q
containedIn : forall A. (P, Q : A -> Type) -> Type
containedIn p q = (x : A) -> p x -> q x

-- Definition: {A : Type | isSet A}
SetU : Type
SetU = (A : Type ** isSet A)

-- Definition : {P : Type | isProp P}
PropU : Type
PropU = (P : Type ** isProp P)

-- Definition: Powerset
powerset : (A : Type) -> Type
powerset a = a -> PropU

----------------------------------
---- PROPOSITIONAL TRUNCATION ----
----------------------------------
