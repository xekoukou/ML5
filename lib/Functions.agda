
module lib.Functions where

module Functions where

  module FunctionsOP where

    _$_ : ∀ {A B : Set} -> (A -> B) -> A -> B
    f $ x = f x
    infixr 11 _$_ 

  open FunctionsOP public

