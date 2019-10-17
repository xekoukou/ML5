module A where

import Nat 
open Nat

-- Modded out by equality:

lte-if-summand : {n m l : Nat} -> Id (n + m) l -> (Lte n l × Lte m l)
-- BUG: 
-- not allowed: 
--   lte-if-summand {Z} {m} {m} Refl = {! !}
--  even though it's forced by typing
lte-if-summand {Z} {Z}   Refl = (Inr Refl , Inr Refl)
lte-if-summand {Z} {S m} Refl = (Inl Lt/zs , Inr Refl)
lte-if-summand {S n} {m} Refl = (lte/ss (fst (lte-if-summand Refl)) , 
                                 lte/s-right (snd (lte-if-summand {n} {m} Refl)))

-- just for comparison, version without pattern matching on the equality proof:
-- lte-if-summand {Z} {Z} {l}   p = (Inr p , Inr p)
-- lte-if-summand {Z} {S m} {l} p = (Inl (subst (\x -> Lt Z x) p Lt/zs) , Inr p)
-- lte-if-summand {S n} {m} {S l} p = (lte/ss (fst (lte-if-summand {n} {m} {l} (id-s-cong-inv p))) , 
--                                    lte/s-right (snd (lte-if-summand {n} {m} {l} (id-s-cong-inv p))))

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

-- better:

lte-if-summand : (n m : Nat) -> (Lte n (n + m) × Lte m (n + m))
lte-if-summand Z Z   = (Inr Refl , Inr Refl)
lte-if-summand Z (S m) = (Inl Lt/zs , Inr Refl)
lte-if-summand (S n) m = (lte/ss (fst (lte-if-summand n m)) , 
                            lte/s-right (snd (lte-if-summand n m)))

lte-if-summand/id : {n m l : Nat} -> Id (n + m) l -> (Lte n l × Lte m l)
lte-if-summand/id Refl = lte-if-summand _ _

