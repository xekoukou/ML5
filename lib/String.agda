open import lib.SumsProds
open import lib.Id
open import lib.List
open import lib.Char

module lib.String where

module String where

  module StringOP where
    postulate String : Set
    {-# BUILTIN STRING  String #-}

  open StringOP public

  private
    primitive
       primStringToList   : String -> Listm.List Char.Char
       primStringFromList : Listm.List Char.Char -> String
       primStringAppend   : String -> String -> String
       primStringEquality : String -> String -> Sums.Bool


  equal : String -> String -> Sums.Bool
  equal = primStringEquality

  toList = primStringToList
  fromList = primStringFromList

  string-append = primStringAppend

  -- function: is this a boundary char?
  split : String -> (Char.Char -> Sums.Bool) -> Listm.List String
  split s f = split' (toList s) Listm.[] where 
    reconstruct : Listm.List Char.Char -> String
    reconstruct l = fromList (Listm.reverse l)

    split' : Listm.List Char.Char -> Listm.List Char.Char -> Listm.List String
    split' Listm.[] currentword = Listm._::_ (reconstruct currentword) Listm.[] 
    split' (Listm._::_ x xs) currentword with f x
    ... | Sums.True  = Listm._::_ (reconstruct currentword) (split' xs Listm.[])  
    ... | Sums.False = split' xs (Listm._::_ x currentword)

  private
    postulate
      primTrustMe : ∀ {A : Set} {x y : A} -> Idm.Id x y

  equal/id : (x y : String) -> Sums.Maybe (Idm.Id x y)
  equal/id s₁ s₂ with (equal s₁ s₂)
  ... | Sums.True  = Sums.Some primTrustMe
  ... | Sums.False = Sums.None 


  postulate 
    same-eq : {s : String} -> Idm.Id (equal s s) Sums.True
