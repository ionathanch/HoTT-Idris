{-
  Chapter 2: Homotopy Type Theory
-}

import TypeTheory

J : (D : (x : a) -> (y : a) -> x === y -> Type) ->
  (d : (x : a) -> D x x Refl) ->
  (x, y : a) -> (p : x === y) -> D x y p
J = ind_id

-----------------------------
---- TYPES are GROUPOIDS ----
-----------------------------

symm : (x, y : _) -> x === y -> y === x
symm x y p =
  let dtype : (x, y : _) -> x === y -> Type
      dtype x y _ = y === x
      d : (x : _) -> dtype x x Refl
      d _ = Refl
  in J dtype d x y p

trans : (x, y, z : _) -> x === y -> y === z -> x === z
trans x y z p q = ?tr