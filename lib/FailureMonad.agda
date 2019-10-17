
open import lib.SumsProds
open Sums
open import lib.List

module lib.FailureMonad where

module FailureMonad where

  return : {A : Set} -> A -> Maybe A
  return = Some

  _>>=_ : ∀ {A B} -> Maybe A -> (A -> Maybe B) -> Maybe B
  (Some x) >>= f = f x
  None >>= f = None

  _||_ : ∀ {A} -> Maybe A -> Maybe A -> Maybe A
  (Some x) || _ = Some x
  None     || y = y

  fail : ∀ {A} -> Maybe A
  fail = None

  or : ∀ {A} -> Listm.List (Maybe A) -> Maybe A
  or = Listm.fold fail _||_

  map : ∀ {A B} -> (A -> B) -> Maybe A -> Maybe B
  map = Sums.mapMaybe 
