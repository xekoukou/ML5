open import lib.SumsProds

module lib.EqSet where

module EqSet where

  data EqSet : Set1 where
    Eq : (t : Set) -> (t -> t -> Sums.Bool) -> EqSet

  t : EqSet -> Set
  t (Eq x _ ) = x
  
  eq : (s : EqSet) -> (t s) -> (t s) -> Sums.Bool
  eq (Eq x y) = y