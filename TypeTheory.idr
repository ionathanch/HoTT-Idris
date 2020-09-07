{-
  Chapter 1: Type Theory

  The constructions presented in this chapter are inherent to the type theory used
  (in this case, MLTT), but since we have inductive definitions available, we can
  build them up ourselves -- or rather, use Idris' Prelude definitions.
  We do define projections for products using recursors and induction,
  but in practice we will use the built-in `fst`, `snd` functions, or use
  pattern-matching directly.
-}

%default total

------------------------
---- FUNCTION TYPES ----
------------------------

-- Uniqueness principle, i.e. η-equivalence
eta : forall A. {B : A -> Type} -> (f : (a : A) -> B a) -> (\a => f a) === f
eta f = Refl

-----------------------
---- PRODUCT TYPES ----
-----------------------

-- Recursor for Unit
rec_unit : forall c. c -> Unit -> c
rec_unit c () = c

-- Induction for Unit
ind_unit : forall c. c () -> (x : Unit) -> c x
ind_unit c () = c

-- Uniqueness principle for Unit
uniq_unit : (x : Unit) -> x === ()
uniq_unit x = ind_unit {c = (\y => y === ())} Refl x


-- Recursor for nondependent products
rec_prod : forall c. (a -> b -> c) -> (a, b) -> c
rec_prod g (a, b) = g a b

-- Induction for nondependent products
ind_prod : forall c. ((x : a) -> (y : b) -> c (x, y)) -> (x : (a, b)) -> c x
ind_prod g (a, b) = g a b

-- Projection functions for nondependent products
pr1_prod : (a, b) -> a
pr1_prod = rec_prod (\a, b => a)

pr2_prod : (a, b) -> b
pr2_prod = rec_prod (\a, b => b)

-- Uniqueness principle for nondependent products
uniq_prod : (x : (a, b)) -> (fst x, snd x) === x
uniq_prod x = ind_prod {c = \x => (fst x, snd x) === x} (\_, _ => Refl) x


-- Recursor for dependent products
rec_dprod : forall a, b, c. ((x : a) -> b x -> c) -> (x : a ** b x) -> c
rec_dprod g (a ** b) = g a b

-- Induction for dependent products
ind_dprod : forall a, b, c. ((x : a) -> (y : b x) -> c (x ** y)) -> (p : (x : a ** b x)) -> c p
ind_dprod g (a ** b) = g a b

-- Projection functions for dependent products
pr1_dprod : forall a, b. (x : a ** b x) -> a
pr1_dprod = rec_dprod (\a, b => a)

-- N.B. In ind_dprod, c = \p => b (pr1_dprod p)
pr2_dprod : forall a, b. (p : (x : a ** b x)) -> b (pr1_dprod p)
pr2_dprod = ind_dprod (\a, b => b)

-- Uniqueness for dependent products
uniq_dprod : forall a, b. (p : (x : a ** b x)) -> (fst p ** snd p) === p
uniq_dprod p = ind_dprod {c = \p => (fst p ** snd p) === p} (\_, _ => Refl) p


-- Type-theoretic axiom of choice:
-- If for every x there is a y such that R(x, y), then there is an f such that for every x, R(x, f(x))
ac' : forall a, b, r. ((x : a) -> (y : b ** r x y)) -> (f : a -> b ** (x : a) -> r x (f x))
ac' g = MkDPair {a = a -> b} (\x => pr1_dprod (g x)) (\x => pr2_dprod (g x))

-- Example: Magmas
magma : Type
magma = (a : Type ** a -> a -> a)

pointedMagma : Type
pointedMagma = (a : Type ** (a -> a -> a, a))

-------------------------
---- COPRODUCT TYPES ----
-------------------------

-- Recursor for Void
rec_void : forall c. Void -> c
rec_void void impossible

-- Induction for Void
ind_void : forall c. (z : Void) -> c z
ind_void void impossible


-- Two-variant coproduct
infix 5 #
data (#) : Type -> Type -> Type where
  inl : a -> a # b
  inr : b -> a # b

-- Recursor for coproduct
rec_coprod : forall c. (a -> c) -> (b -> c) -> a # b -> c
rec_coprod f g (inl a) = f a
rec_coprod f g (inr b) = g b

-- Induction for coproduct
ind_coprod : forall c. ((x : a) -> c (inl x)) -> ((y : b) -> c (inr y)) -> (q : a # b) -> c q
ind_coprod f g (inl a) = f a
ind_coprod f g (inr b) = g b

------------------
---- BOOLEANS ----
------------------

-- Recursor for Bool (nondependent conditional)
rec_bool : forall c. c -> c -> Bool -> c
rec_bool c1 c2 True  = c1
rec_bool c1 c2 False = c2

-- Induction for Bool (dependent conditional)
ind_bool : forall c. c True -> c False -> (b : Bool) -> c b
ind_bool c1 c2 True  = c1
ind_bool c1 c2 False = c2


-- Defining coproducts as dependent products indexed over Bools
infix 5 ##
(##) : Type -> Type -> Type
a ## b = (x : Bool ** rec_bool a b x)

-- Recursor for alternate coproduct
rec_coprod' : forall c. (a -> c) -> (b -> c) -> a ## b -> c
rec_coprod' f g (True  ** a) = f a
rec_coprod' f g (False ** b) = g b

-- Induction for altenate coproduct
ind_coprod' : forall c. ((x : a) -> c (True ** x)) -> ((y : b) -> c (False ** y)) -> (q : a ## b) -> c q
ind_coprod' f g (True  ** a) = f a
ind_coprod' f g (False ** b) = g b

------------------
---- NATURALS ----
------------------

-- Recursor for Nat
rec_nat : forall c. c -> (Nat -> c -> c) -> Nat -> c
rec_nat cz cs Z = cz
rec_nat cz cs (S n) = cs n (rec_nat cz cs n)

-- Doubling
double : Nat -> Nat
double = rec_nat 0 (\n, y => S (S y))

-- Addition
-- Intuitively, g is the continuation, which we define as
-- the successor of the previous continuation applied to m
-- while the base continuation is the identity function,
-- so n layers of continuations means applying the successor
-- n times to onto m.
add : Nat -> Nat -> Nat
add = rec_nat (\n => n) (\n, g, m => S (g m))

-- Induction for Nat
ind_nat : forall c. c Z -> ((n : Nat) -> c n -> c (S n)) -> (n : Nat) -> c n
ind_nat cz cs Z = cz
ind_nat cz cs (S n) = cs n (ind_nat cz cs n)

-------------------------------
---- PROPOSITIONS as TYPES ----
-------------------------------

deMorganToNor : (a -> Void, b -> Void) -> a # b -> Void
deMorganToNor (an't, bn't) (inl a) = an't a
deMorganToNor (an't, bn't) (inr b) = bn't b

deMorganFromNor : (a # b -> Void) -> (a -> Void, b -> Void)
deMorganFromNor nor = (\a => nor (inl a), \b => nor (inr b))

splitProduct : forall p, q. ((x : _) -> (p x, q x)) -> ((x : _) -> p x, (x : _) -> q x)
splitProduct pq = (\x => fst (pq x), \x => snd (pq x))

-----------------------
---- IDENTITY TYPE ----
-----------------------

-- Recursor for identity: indiscernibility of identicals
rec_id : (C : a -> Type) -> (x, y : a) -> (p : x === y) -> C x -> C y
rec_id _ x x Refl cx = cx

-- Induction for identity: path induction
-- Intuitively, if C(x, x) holds when x === x,
-- then C(x, y) holds when x === y.
-- C(x, y) may also depend on the path from x to y, but to prove
-- induction we only need to consider when the path is x === x.
ind_id : (C : (x : a) -> (y : a) -> x === y -> Type) ->
  (c : (x : a) -> C x x Refl) ->
  (x, y : a) -> (p : x === y) -> C x y p
ind_id _ c x x Refl = c x

-- The recursor can be defined from induction
rec'_id : (C : a -> Type) -> (x, y : a) -> (p : x === y) -> C x -> C y
rec'_id c x y refl = ind_id (\x, y, _ => c x -> c y) (\_, cx => cx) x y refl

-- Based path induction: induction for identity,
-- but with one end of the path fixed at some point.
-- Intuitively, if C(a, a) and a === a holds,
-- then C(a, x) holds when a === x.
based_ind_id : forall A. (a : A) -> (C : (x : A) -> a === x -> Type) ->
  (c : C a Refl) ->
  (x : A) -> (p : a === x) -> C x p
based_ind_id a _ c a Refl = c

-- Path induction can be defined from based path induction;
-- The first argument x becomes the fixed endpoint in the based path.
ind'_id : (C : (x : a) -> (y : a) -> x === y -> Type) ->
  (c : (x : a) -> C x x Refl) ->
  (x : a) -> (y : a) -> (p : x === y) -> C x y p
ind'_id ctype c x y p = based_ind_id x (ctype x) (c x) y p

-- Based path induction can be defined from path induction
-- Let D(x, y, p) = (C : (z : A) -> x === z -> Type) -> C x Refl -> C y p.
-- In ind_id, instantiating C with D, we have
--  ind_id D : (c : (x : a) -> (C : (z : A) -> x === z -> Type) -> C x Refl -> C x Refl) ->
--    (x : a) -> (y : a) -> (p : x === y) ->
--    (C : (z : A) -> x === z -> Type) -> C x Refl -> C y p
-- Then we instantiate with an identity function d = (\x, C, c => c) to get
--  ind_id D d : (x : a) -> (y : a) -> (p : x === y) ->
--    (C : (z : A) -> x === z -> Type) -> C x Refl -> C y p
-- Next is straightforward: we instantiate with a, x, and p:
--  ind_id D d a x p : (C : (z : A) -> a === z -> Type) -> C a Refl -> C x p
-- Finally, this is exactly the ctype and c arguments, so we get
--  ind_id D d a x p ctype c = C x p
based_ind'_id : forall A. (a : A) -> (C : (x : A) -> a === x -> Type) ->
  (c : C a Refl) ->
  (x : A) -> (p : a === x) -> C x p
based_ind'_id a ctype c x p = ind_id
  (\x, y, p => (C : (z : A) -> x === z -> Type) -> C x Refl -> C y p)
  (\_, _, c => c)
  a x p ctype c

infix 9 =/=
(=/=) : a -> a -> Type
x =/= y = x === y -> Void
