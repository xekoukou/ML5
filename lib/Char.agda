
open import lib.SumsProds
open import lib.Id
open import lib.SumsProds
open import lib.Nat

module lib.Char where

module Char where

  postulate
    Char : Set
  
  {-# BUILTIN CHAR Char #-}
  
  ------------------------------------------------------------------------
  -- Operations
  
  private
   primitive
    primCharToNat    : Char → Natm.Nat
    primCharEquality : Char → Char → Sums.Bool
  
  toNat : Char → Natm.Nat
  toNat = primCharToNat
  
  equal : Char -> Char -> Sums.Bool
  equal = primCharEquality

