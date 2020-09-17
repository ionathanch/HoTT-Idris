{-
  Chapter 5: Induction
-}

import Homotopy

-----------------
---- W-TYPES ----
-----------------

-- A represents the label of the inductive type; if the type has n constructors, then |A| = n.
-- Given an (a : A), (B a) are the constructor arguments of a.
data W : (A : Type) -> (B : A -> Type) -> Type where
  Sup : forall A. {B : A -> Type} -> (a: A) -> (B a -> W A B) -> W A B

-- The type of the inductive premise
-- Given some motive E, for any "constructor" a and its "arguments" f,
-- we must show that the inductive hypothesis holds, i.e. every sub-W (f b) satisfies E.
eind : forall A. {B : A -> Type} -> (E : W A B -> Type) -> Type
eind etype = (a : A) -> (f : B a -> W A B) -> (g : (b : B a) -> etype (f b)) -> etype (Sup a f)

-- Computation rule: Given a motive E, if the inductive premise holds, then ∀(w : W A B), E w holds.
-- This is the induction principle for W-types; I don't know why it's named like a recursor.
rec_W : forall A. {B : A -> Type} -> (E : W A B -> Type) -> eind E -> (w : W A B) -> E w
rec_W etype e (Sup a f) = e a f (\b => rec_W etype e (f b))

-- Uniqueness principle: Any two functions that satisfy the inductive hypothesis are equal
W_uniq : forall A. {B : A -> Type} -> (E : W A B -> Type) -> (e : eind E) -> (g, h : (w : W A B) -> E w) ->
  ((a : A) -> (f : B a -> W A B) -> g (Sup a f) =:= e a f (\b => g (f b))) ->
  ((a : A) -> (f : B a -> W A B) -> h (Sup a f) =:= e a f (\b => h (f b))) -> g =:= h
W_uniq etype e g h gind hind = ?wu
