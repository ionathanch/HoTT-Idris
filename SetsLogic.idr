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

-- Products of sets are sets
prodIsSet : {A, B : Type} -> isSet A -> isSet B -> isSet (A, B)
prodIsSet f g x y p q =
  let pqfst : prodId_pr1 p =:= prodId_pr1 q
      pqfst = f (fst x) (fst y) (prodId_pr1 p) (prodId_pr1 q)
      pqsnd : prodId_pr2 p =:= prodId_pr2 q
      pqsnd = g (snd x) (snd y) (prodId_pr2 p) (prodId_pr2 q)
      pq : prodId {x} {y} (prodId_pr p) =:= prodId {x} {y} (prodId_pr q)
      pq = ap prodId (prodId (pqfst, pqsnd))
  in invert (prodId_uniq p) <> pq <> prodId_uniq q

-- Functions to sets are sets
funIsSet : {A : Type} -> {B : A -> Type} -> ((x : A) -> isSet (B x)) -> isSet ((x : A) -> B x)
funIsSet setB f g p q =
  let pq_happly : (x : A) -> happly p x =:= happly q x
      pq_happly = \x => setB x (f x) (g x) (happly p x) (happly q x)
      pq : funext (happly p) =:= funext (happly q)
      pq = ap funext (funext pq_happly)
  in invert (fun_uniq p) <> pq <> fun_uniq q

{-
-- Exercise 3.1: If A <~> B and A is a set, then B is a set
AEqvBIsSet: {A, B: Type} -> (f: A -> B) -> (g: B -> A) -> ((x: B) -> f (g x) =:= x) -> isSet A -> isSet B
AEqvBIsSet f g fg isSetA x y p q =
  let --gpgq: ap g p =:= ap g q
      --gpgq = isSetA (g x) (g y) (ap g p) (ap g q)
      --fgpfgq: ap f (ap g p) =:= ap f (ap g q)
      --fgpfgq = ap (ap f) gpgq
      --fgpq: ap (f . g) p =:= ap (f . g) q
      --fgpq = invert (ap_concat g f p) <> fgpfgq <> ap_concat g f q
      funext' : forall A. {B : A -> Type} -> {f, g : (x : A) -> B x} -> ((x: A) -> f x =:= g x) -> f =:= g
      transport' : forall A. (P : A -> Type) -> {x, y : A} -> (p : x =:= y) -> P x -> P y
      transport' p Refl px = px
      ap' : forall A, B. (f : A -> B) -> {x, y : A} -> x =:= y -> f x =:= f y
      ap' f Refl = Refl
      apd' : forall A. {P : A -> Type} -> (f : (a : A) -> P a) -> {x, y : A} -> (p : x =:= y) -> transport' P p (f x) =:= f y
      apd' f Refl = Refl
      helpp: transport' (\f => f x =:= f y) (funext' fg) (ap' (\x => f (g x)) p) =:= ap' (\x => x) p
      --helpp = apd' (\f => ap' f p) (funext' fg)
  in ?h
-}

----------------------
---- PROPOSITIONS ----
----------------------

-- Definition: Mere propositions ((-1)-types)
isProp : (P : Type) -> Type
isProp p = (x, y : p) -> x =:= y

-- If propositions are logically equivalent then they are quasi-equivalent
logicalEquiv : forall P, Q. isProp P -> isProp Q -> (P -> Q) -> (Q -> P) -> P <~> Q
logicalEquiv propP propQ f g =
  ((f, g) ** (\p => propP (g (f p)) p, \q => propQ (f (g q)) q))

-- Mere propositions are quasi-equivalent to unit
propUnit : {P : Type} -> isProp P -> (x : P) -> P <~> Unit
propUnit propP x = logicalEquiv propP (\(), () => Refl) (\_ => ()) (\() => x)

-- Mere propsitions are sets
propIsSet : {P : Type} -> isProp P -> isSet P
propIsSet f x y p q =
  let g : (y : P) -> x =:= y
      g y = f x y
      apdg : {x, y : P} -> (p : x =:= y) -> g x <> p =:= g y
      apdg {x} {y} p = invert (transport_concatl p (g x)) <> apd g p
      gxpq : g x <> p =:= g x <> q
      gxpq = apdg p <> invert (apdg q)
  in leftCancel (g x) p q gxpq

-- isProp is a mere proposition
isPropIsProp : {P : Type} -> isProp (isProp P)
isPropIsProp f g =
  let isPropHom : (x, y : P) -> f x y =:= g x y
      isPropHom x y = propIsSet f x y (f x y) (g x y)
  in funext (\x => funext (isPropHom x))

-- isSet is a mere proposition
isSetIsProp : {A : Type} -> isProp (isSet A)
isSetIsProp f g =
  let isSetHom : (x, y : A) -> (p, q : x =:= y) -> f x y p q =:= g x y p q
      isSetHom x y p q = setIsOne f x y p q (f x y p q) (g x y p q)
  in funext (\x => funext (\y => funext (\p => funext (isSetHom x y p))))

-- Products of propositions are propositions
-- Idris bug: All hell breaks loose when you uncomment this out. I don't know why.
-- prodIsProp : {A, B : Type} -> isProp A -> isProp B -> isProp (A, B)
-- prodIsProp f g (a, b) (a', b') = prodId (f a a', g b b')

-- Functions to propositions are propositions
funIsProp : {A : Type} -> {B : A -> Type} -> ((x : A) -> isProp (B x)) -> isProp ((x : A) -> B x)
funIsProp propB f g = funext (\x => propB x (f x) (g x))

-- The empty type is a proposition
voidIsProp : isProp Void
voidIsProp void impossible

-- The unit type is a proposition
unitIsProp : isProp Unit
unitIsProp () () = Refl

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
decTypeFam : {A : Type} -> (B : A -> Type) -> Type
decTypeFam b = (a : A) -> b a # Not (b a)

-- Definition: Decidability of equality of a type
decEq : (A : Type) -> Type
decEq a = (b, c : a) -> b =:= c # Not (b =:= c)

------------------
---- SUBTYPES ----
------------------

-- If P is a proposition, ux = uv, and we have proofs of P ux and P vx,
-- then those proofs must be equal.
propNoSub : {A : Type} -> {P : A -> Type} -> ((x : A) -> isProp (P x)) ->
  (u, v : DPair A P) -> fst u =:= fst v -> u =:= v
propNoSub f (ux ** pu) (vx ** pv) p =
  dprodId (p ** f vx (transport P p pu) pv)

-- Definition: a ∈ P
member : forall A. (a : A) -> (P : A -> Type) -> Type
member a p = p a

-- Definition: P ⊆ Q
containedIn : {A : Type} -> (P, Q : A -> Type) -> Type
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

namespace Squash
  export
  data Squash : Type -> Type where
    MkSquash : forall A. (a : A) -> Squash A

  public export
  mkSquash : forall A. (a : A) -> Squash A
  mkSquash a = MkSquash a

  export
  squash : forall A. (x, y : Squash A) -> x =:= y

  public export
  squash_rec : forall A, B. isProp B -> (f : A -> B) ->
    (g : Squash A -> B ** g . Squash.mkSquash ~~ f)
  squash_rec propB f =
    let g : Squash A -> B
        g (MkSquash a) = f a
        h : g . Squash.mkSquash ~~ f
        h a = propB (g (mkSquash a)) (f a)
    in (g ** h)

  public export
  squash_ind : forall A. {B : Squash A -> Type} -> ((x : Squash A) -> isProp (B x)) ->
    ((a : A) -> B (mkSquash a)) -> ((x : Squash A) -> B x)
  squash_ind _ f (MkSquash a) = f a

-------------------------
---- AXIOM of CHOICE ----
-------------------------

-- The axiom of choice: If ∀(x : X), ∃(a : A x) s.t. P x a,
-- then ∃(g : (x : X) -> A x) s.t. ∀(x : X), P x (g x)
-- Intuitively, if for every x there's an a that satisfies P,
-- then there is a choice function g that can pick out the correct a
-- associated with that x such that P is satisfied.
AC : Type
AC = {X : Type} -> (A : X -> Type) -> (P : (x : X) -> A x -> Type) ->
  isSet X -> ((x : X) -> isSet (A x)) -> ((x : X) -> (a : A x) -> isProp (P x a)) ->
  ((x : X) -> Squash (a : A x ** P x a)) -> Squash (g : (x : X) -> A x ** (x : X) -> P x (g x))

-- The cartesian product of a family of nonempty sets is nonempty.
CP : Type
CP = {X : Type} -> (Y : X -> Type) -> ((x : X) -> Squash (Y x)) -> Squash ((x : X) -> Y x)

ACqeqvCP : AC <~> CP

------------------------------------
---- PRINCIPLE of UNIQUE CHOICE ----
------------------------------------

squash_qeqv : forall P. isProp P -> P <~> Squash P
squash_qeqv propP =
  let unMkSquash : Squash P -> P
      unMkSquash = fst (squash_rec propP id)
  in logicalEquiv propP squash mkSquash unMkSquash

puc : forall A. {P : A -> Type} -> ((x : A) -> isProp (P x)) -> ((x : A) -> Squash (P x)) -> (x : A) -> P x
puc propP squashP x = (qeqvFrom (squash_qeqv (propP x))) (squashP x)

-- Exercise 3.19
--unsquashDec : (P : Nat -> Type) -> decTypeFam P -> Squash (n : Nat ** P n) -> (n : Nat ** P n)

-------------------------
---- CONTRACTIBILITY ----
-------------------------

-- Definition: Contractible types ((-2)-types)
isContr : (A : Type) -> Type
isContr a = (c : a ** (x : a) -> c =:= x)

-- A contractible type is a mere proposition
contrIsProp : {A : Type} -> isContr A -> isProp A
contrIsProp (c ** contrA) x y = invert (contrA x) <> contrA y

-- An inhabited mere proposition is contractible
propIsContr : {A : Type} -> A -> isProp A -> isContr A
propIsContr a propA = (a ** propA a)

-- Contractible types are equivalent to unit
contrUnit : {A : Type} -> isContr A -> A <~> Unit
contrUnit a@(c ** contrA) = propUnit (contrIsProp a) c

-- Contractibility is a mere proposition
isContrIsProp : {A : Type} -> isProp (isContr A)
isContrIsProp c@(a ** p) c'@(a' ** p') =
  let q : a =:= a'
      q = p a'
      p'' : (x : A) -> a' =:= x
      p'' = transport (\a => (x : A) -> a =:= x) q p
      setA : isSet A
      setA = propIsSet (contrIsProp c)
      propP : isProp ((x : A) -> a' =:= x)
      propP = funIsProp (\x => setA a' x)
  in dprodId (q ** propP p'' p')

-- Contractibility of contractibles is contractible
contrIsContr : {A : Type} -> isContr A -> isContr (isContr A)
contrIsContr contrA = propIsContr contrA isContrIsProp

-- Products of contractible types are contractible
prodIsContr : {A, B : Type} -> isContr A -> isContr B -> isContr (A, B)
prodIsContr (a ** contrA) (b ** contrB) =
  let contrAB : (ab : (A, B)) -> (a, b) =:= ab
      contrAB (a', b') = prodId (contrA a', contrB b')
  in ((a, b) ** contrAB)

-- Functions to contractible types are contractible
funIsContr : {A : Type} -> {P : A -> Type} -> ((a : A) -> isContr (P a)) -> isContr ((x : A) -> P x)
funIsContr contrP = propIsContr {A = (a : A) -> P a} (\x => fst (contrP x)) (funIsProp (\a => contrIsProp (contrP a)))

-- The unit type is contractible
unitIsContr : isContr Unit
unitIsContr = MkDPair () (\() => Refl)

-- ∃(x : A) s.t. a = x is contractible
singleLeftIsContr : {A : Type} -> (a : A) -> isContr (x : A ** a =:= x)
singleLeftIsContr a =
  let centre : (x : A ** a =:= x)
      centre = (a ** Refl)
      centreEq : (xp : (x : A ** a =:= x)) -> centre =:= xp
      centreEq (x ** p) = dprodId (p ** transport_concatl p Refl)
  in (centre ** centreEq)

-- ∃(x : A) s.t. x = a is contractible
singleRightIsContr : {A : Type} -> (a : A) -> isContr (x : A ** x =:= a)
singleRightIsContr a =
  let centre : (x : A ** x =:= a)
      centre = (a ** Refl)
      contrCentre : (xp : (x : A ** x =:= a)) -> centre =:= xp
      contrCentre (x ** p) = invert (dprodId (p ** transport_concatr p p <> leftInv p))
  in (centre ** contrCentre)


-- B is a retract of A if
-- there is a retraction (r : A -> B) and a section (s : B -> A) such that
-- there is a homotopy (r . s ~~ id)
isRetr : (B : Type) -> (A : Type) -> Type
isRetr b a = (rs : (a -> b, b -> a) **
  let (r, s) = rs
  in (y : b) -> r (s y) =:= y)

-- If B is a retract of A and A is contractible then B is contractible
retrIsContr : {A, B : Type} -> isRetr B A -> isContr A -> isContr B
retrIsContr ((r, s) ** e) (a0 ** contrA) =
  let b0 : B
      b0 = r a0
      contrB : (b : B) -> b0 =:= b
      contrB b = ap r (contrA (s b)) <> e b
  in (b0 ** contrB)


-- ∀(x : A) isContr (P x) -> ∃(x : A) s.t. P x <~> A
contrFamilyType : forall A. {P : A -> Type} -> ((x : A) -> isContr (P x)) -> (x : A ** P x) <~> A
contrFamilyType contrP =
  let g : A -> (x : A ** P x)
      g x = (x ** fst (contrP x))
      gfst : (x : (a : A ** P a)) -> g (fst x) =:= x
      gfst (a ** pa) = ap (\pa => (a ** pa)) (snd (contrP a) pa)
  in ((fst, g) ** (gfst, \_ => Refl))

-- ∀(x : A) isContr A @ c -> ∃(x : A) s.t. P x <~> P c
contrFamilyCentre : {A : Type} -> {P : A -> Type} -> (contrA : isContr A) -> (x : A ** P x) <~> P (fst contrA)
contrFamilyCentre (c ** contrA) =
  let f : (x : A ** P x) -> P c
      f (x ** px) = transport P (invert (contrA x)) px
      g : P c -> (x : A ** P x)
      g pc = (c ** pc)
      fg : (pc : P c) -> transport {A} P (invert (contrA c)) pc =:= pc
      gf : (xpx : (x : A ** P x)) -> g (f xpx) =:= xpx
      gf (x ** px) =
        let cx : c =:= x
            cx = contrA x in
        let pcx1 : transport P cx (transport P (invert cx) px) =:= transport P (invert cx <> cx) px
            pcx1 = transport_distrib (invert cx) cx px
            pcx2 : transport P (invert cx <> cx) px =:= px
            pcx2 = ap (\p => transport P p px) (leftInv cx)
        in dprodId (cx ** pcx1 <> pcx2)
  in ((f, g) ** (gf, fg))


-- A is a mere proposition iff ∀(x, y : A), x = y is contractible
propIsContrId : {A : Type} -> isProp A -> (x, y : A) -> isContr (x =:= y)
propIsContrId propA x y =
  let xy : x =:= y
      xy = propA x y
  in (xy ** (propIsSet propA) x y xy)

contrIdIsProp : forall A. ((x, y : A) -> isContr (x =:= y)) -> isProp A
contrIdIsProp contrId x y = fst (contrId x y)


-- A <~> B -> isContr A <-> isContr B (reverse direction follows by symmetry)
qeqvToContr : {A, B : Type} -> A <~> B -> isContr A -> isContr B
qeqvToContr ((f, g) ** (gf, fg)) (a ** contrA) =
  let contrB : (y : B) -> f a =:= y
      contrB y = ap f (contrA (g y)) <> fg y
  in (f a ** contrB)
