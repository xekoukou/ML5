
-- 
-- version that uses a reverse:
-- ident : (l : Nat) -> Subst (Z , l) (Z , l)
-- ident l = reverse (ident' l l (Inr Refl)) -- reverse because we get the nth thing from the front when we look up!
--   where ident' : (l : Nat) (l' : Nat) -> Lte l l' -> Subst (Z , l') (Z , l)
--         ident' Z     l' _ = Nil
--         ident' (S l) l' p = Cons (^ (l , Inr (lt-if-lte-s p))) (ident' l l' (Inl (lt-if-lte-s p)))

-- version passing identity proofs:
-- ident : (l : Nat) -> Subst (Z , l) (Z , l)
-- ident l = ident' Z l (+-rh-z l)
--  where ident' : (cur left : Nat) -> Id l (left + cur) -> Subst (Z , l) (Z , left)
--         ident' _    Z       _ = Nil
--         ident' cur (S left) p = Cons (^ (cur , Inr (lt-if-lte-s
--                                                      (snd
--                                                       (lte-if-summand/id {left} {S cur} (sym (trans p (+-rh-s left cur))))))))
--                                      (ident' (S cur) left (trans p (+-rh-s left cur)))
-- 
--   -- pattern matching on p directly instead: 
--   where ident' : {l : Nat} -> (cur left : Nat) -> Id l (left + cur) -> Subst (Z , l) (Z , left)
--         ident' _    Z       _ = Nil
--         ident' cur (S left) Refl = Cons (^ (cur , Inr (subst (\x -> Lt cur x)
--                                                               (sym (+-rh-s left cur))
--                                                       (lt-if-lte-s (snd (lte-if-summand left (S cur)))))))
--                                         (ident' (S cur) left (+-rh-s left cur))

ident : (l : Nat) -> Subst (Z , l) (Z , l)
ident l = ident' Z l
        -- don't pass in an identity proof at all
  where ident' : (cur left : Nat) -> Subst (Z , cur + left) (Z , left)
        ident' _    Z       = Nil
        ident' cur (S left) = Cons (^ (cur , Inr (subst (\x -> Lt cur x)
                                                   (trans (+-comm left (S cur)) (+-rh-s cur left))
                                                   (lt-if-lte-s (snd (lte-if-summand left (S cur)))))))
                                   (subst (\ x -> Subst (Z , x) (Z , left)) (+-rh-s cur left) (ident' (S cur) left))

