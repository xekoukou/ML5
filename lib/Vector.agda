open import lib.Nat
open Nat
open import lib.NatThms
open NatThms
open import lib.SumsProds
open Prods.ProdsOP
open import lib.Id
open Id
open import lib.List
open List.ListOP

module lib.Vector where

module Vec where
  data Vec (a : Set) : Nat -> Set where
    Nil  : Vec a Z
    Cons : {n : _} -> a -> Vec a n -> Vec a (S n)
  
  forget : {A : Set} {n : Nat} -> Vec A n -> List A
  forget Nil = []
  forget (Cons x xs) = x :: (forget xs)

  append : forall {a n n'} -> Vec a n -> Vec a n' -> Vec a (n + n')
  append Nil l2 = l2 
  append (Cons x xs) l2 = Cons x (append xs l2)
  
  nth : forall {a k n} -> Vec a n -> Lt k n -> a
  nth Nil () 
  nth (Cons x zs) Lt/zs = x
  nth (Cons x xs) (Lt/ss l) = nth xs l
  
  map : forall {a b n} -> (a -> b) -> Vec a n -> Vec b n
  map f Nil = Nil
  map f (Cons x xs) = Cons (f x) (map f xs)

  map-id : forall {A n} (v : Vec A n) -> Id (map (\ x -> x) v) v
  map-id Nil = Refl
  map-id (Cons y y') = Id.substeq (\ y' -> Cons y y') (map-id y')

  map-compose : forall {A B C n} (f : A -> B) (g : B -> C) (v : Vec A n)
              -> Id (map (\ x -> (g (f x))) v) (map g (map f v))
  map-compose f g Nil = Refl
  map-compose f g (Cons x xs) = Id.substeq (\ y -> Cons (g (f x)) y) (map-compose f g xs)
  
  Snoc : forall {a n} -> Vec a n -> a -> Vec a  (n + 1)
  Snoc {a} {n} v x = append v (Cons x Nil)
  
  -- could also prove the identity
  unsnoc : {a : Set} (n : Nat) -> Vec a (n + 1) -> (Vec a n × a)
  unsnoc Z     (Cons x Nil) = Nil , x
  unsnoc (S n) (Cons x xs) with unsnoc n xs
  ...                         | rest , last = (Cons x rest) , last
  
  reverse : forall {a n} -> Vec a n -> Vec a n
  reverse {a} {n} v =  subst (\k -> Vec a k) (sym (+-rh-z n)) (rev v Nil)
    where rev : {n m : Nat} -> Vec a n -> Vec a m -> Vec a (n + m)
          rev {Z} Nil acc = acc
          rev {S n} {m} (Cons x xs) acc = subst (\k -> Vec a k) (sym (+-rh-s n m))
                                                (rev xs (Cons x acc))
  
  split : {a : Set} (l1 l2 : Nat) -> (v : Vec a (l1 + l2)) -> 
             (Σ (\ (front : Vec a l1) -> Σ (\ (back : Vec a l2) -> Id v (append front back))))
  split Z       _ v = Nil , (v , Refl)
  split (S l1) l2 (Cons x xs) with split l1 l2 xs 
  ...                            | (front' , (back' , id')) = Cons x front' , (back' , substeq (\tl -> Cons x tl) id') 

  split2 : {a : Set} (l1 l2 : Nat) -> (Vec a (l1 + l2)) -> (Vec a l1 × Vec a l2)
  split2 Z       _ v = Nil , v
  split2 (S l1) l2 (Cons x xs) =  (Cons x (fst (split2 l1 l2 xs)) , (snd (split2 l1 l2 xs)))

--   split2' : {a : Set} {l1 : Nat} -> (Vec a (l1 + l1)) -> (Vec a l1 × Vec a l1)
--   split2' {a} {l1} = split2 l1 l1

  zip : {A B : Set} {n : Nat} -> Vec A n -> Vec B n -> Vec (A × B) n 
  zip Nil Nil = Nil
  zip (Cons x xs) (Cons y ys) = Cons (x , y) (zip xs ys)
  
module Vec1 where

-- FIXME: better solution than copying the entire thing?
  
  data Vec (a : Set1) : Nat -> Set1 where
    Nil  : Vec a Z
    Cons : {n : _} -> a -> Vec a n -> Vec a (S n)
  
  append : forall {a n n'} -> Vec a n -> Vec a n' -> Vec a (n + n')
  append Nil l2 = l2
  append (Cons x xs) l2 = Cons x (append xs l2)
  
  nth : forall {a k n} -> Vec a n -> Lt k n -> a
  nth Nil () 
  nth (Cons x zs) Lt/zs = x
  nth (Cons x xs) (Lt/ss l) = nth xs l
  
  map : forall {a b n} -> (a -> b) -> Vec a n -> Vec b n
  map f Nil = Nil
  map f (Cons x xs) = Cons (f x) (map f xs)
  
  Snoc : forall {a n} -> Vec a n -> a -> Vec a  (n + 1)
  Snoc {a} {n} v x = append v (Cons x Nil)
  
  -- -- could also prove the identity
  -- unsnoc : {a : Set} (n : Nat) -> Vec a (n + 1) -> (Vec a n × a)
  -- unsnoc Z     (Cons x Nil) = Nil , x
  -- unsnoc (S n) (Cons x xs) with unsnoc n xs
  -- ...                         | rest , last = (Cons x rest) , last
  
  -- reverse : forall {a n} -> Vec a n -> Vec a n
  -- reverse {a} {n} v =  subst (\k -> Vec a k) (sym (+-rh-z n)) (rev v Nil)
  --   where rev : forall {a n m} -> Vec a n -> Vec a m -> Vec a (n + m)
  --         rev Nil acc = acc
  --         rev {a} {S n'} {m} (Cons x xs) acc = subst (\k -> Vec a k) (sym (+-rh-s n' m)) (rev xs (Cons x acc))
  
  
  -- split : {a : Set} (l1 l2 : Nat) -> (v : Vec a (l1 + l2)) -> 
  --            (Σ (\ (front : Vec a l1) -> Σ (\ (back : Vec a l2) -> Id v (append front back))))
  -- split Z       _ v = Nil , (v , Refl)
  -- split (S l1) l2 (Cons x xs) with split l1 l2 xs 
  -- ...                            | (front' , (back' , id')) = Cons x front' , (back' , substeq (\tl -> Cons x tl) id') 


