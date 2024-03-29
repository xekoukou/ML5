module lib.Nat where

module Natm where
  module NatOP where
    data Nat : Set where
      Z : Nat
      S : Nat -> Nat

    {-# BUILTIN NATURAL Nat #-}

  open NatOP public

  natrec : {p : Nat -> Set} -> 
            p Z -> 
            ((n : Nat) -> p n -> p (S n)) -> 
            (n : Nat) -> p n
  natrec zc sc Z = zc
  natrec zc sc (S n) = sc n (natrec zc sc n)
  
  _+_ : Nat -> Nat -> Nat
  _+_ Z n = n
  _+_ (S n) n' = S (n + n')

  
