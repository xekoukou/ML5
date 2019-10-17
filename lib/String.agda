open import lib.SumsProds
open import lib.Id
open import lib.List
open import lib.Char

module lib.String where

module String where

  module StringOP where
    postulate String : Set
    {-# BUILTIN STRING  String #-}
    {-# COMPILED_TYPE String String #-}

  open StringOP public

  private
    primitive
       primStringToList   : String -> List.List Char.Char
       primStringFromList : List.List Char.Char -> String
       primStringAppend   : String -> String -> String
       primStringEquality : String -> String -> Sums.Bool


  equal : String -> String -> Sums.Bool
  equal = primStringEquality

  toList = primStringToList
  fromList = primStringFromList

  string-append = primStringAppend

  -- function: is this a boundary char?
  split : String -> (Char.Char -> Sums.Bool) -> List.List String
  split s f = split' (toList s) List.[] where 
    reconstruct : List.List Char.Char -> String
    reconstruct l = fromList (List.reverse l)

    split' : List.List Char.Char -> List.List Char.Char -> List.List String
    split' List.[] currentword = List._::_ (reconstruct currentword) List.[] 
    split' (List._::_ x xs) currentword with f x
    ... | Sums.True  = List._::_ (reconstruct currentword) (split' xs List.[])  
    ... | Sums.False = split' xs (List._::_ x currentword)


  private primitive primTrustMe : ∀ {A : Set} {x y : A} -> Id.Id x y

  equal/id : (x y : String) -> Sums.Maybe (Id.Id x y)
  equal/id s₁ s₂ with (equal s₁ s₂)
  ... | Sums.True  = Sums.Some primTrustMe
  ... | Sums.False = Sums.None 


  postulate 
    same-eq : {s : String} -> Id.Id (equal s s) Sums.True