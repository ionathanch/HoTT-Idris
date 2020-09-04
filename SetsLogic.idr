{-
  Chapter 3: Sets and Logic
-}

import Homotopy
import TypeFormers

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
upwardClosure: forall A. isSet A -> isOne A
upwardClosure f x y p q r s =
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
