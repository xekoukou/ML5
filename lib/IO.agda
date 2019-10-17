
open import lib.String
open String

open import lib.SumsProds
open Sums

module lib.IO where

module IO where

  postulate
    {- FIXME: add monad laws-}
    IO : Set → Set
    return : ∀ {A} → A → IO A
    _>>=_  : ∀ {A B} → IO A → (A → IO B) → IO B
  
  infixl 1 _>>=_
  
  postulate
    MyUnit : Set

  postulate
    readFile   : String → IO String
    writeFile  : String → String → IO MyUnit
    appendFile : String → String → IO MyUnit
    openTempFile : String → String → IO String
    putStr   : String -> IO MyUnit
    putStrLn : String -> IO MyUnit
    getLine  : IO String
    flip     : IO Bool
    error    : {A : Set} -> String -> IO A
    fix      : {A : Set} -> (IO A -> IO A) -> IO A

  postulate
    IORef : Set -> Set
    newIORef : ∀ {A} -> A -> IO (IORef A)
    readIORef : ∀ {A} -> IORef A -> IO A
    writeIORef : ∀ {A} -> IORef A -> A -> IO MyUnit

