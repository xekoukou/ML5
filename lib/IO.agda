
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
  
  {-# COMPILED_TYPE IO IO #-}
  {-# COMPILED return (\_ -> return :: a -> IO a) #-}
  {-# COMPILED _>>=_  (\_ _ -> (>>=) :: IO a -> (a -> IO b) -> IO b) #-}
  
  postulate
    MyUnit : Set
  {-# COMPILED_TYPE MyUnit () #-}

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
  {-# IMPORT System.IO.UTF8 #-}
  {-# IMPORT IO  #-}
  {-# IMPORT System.IO  #-}
  {-# IMPORT Random  #-}
  {-# COMPILED readFile \ s -> System.IO.UTF8.readFile ("RuntimeRoot/" ++ s)   #-}
  {-# COMPILED writeFile \ s -> System.IO.UTF8.writeFile ("RuntimeRoot/" ++ s)   #-}
  {-# COMPILED appendFile \ s -> System.IO.UTF8.appendFile ("RuntimeRoot/" ++ s)   #-}
  {-# COMPILED openTempFile \ s s' -> do {(x , _) <- System.IO.openTempFile ("RuntimeRoot/" ++ s) s'; return x}   #-}
  {-# COMPILED putStrLn System.IO.UTF8.putStrLn  #-}
  {-# COMPILED putStr   \ s -> do { System.IO.UTF8.putStr s ; IO.hFlush IO.stdout}  #-}
  {-# COMPILED getLine  System.IO.UTF8.getLine #-}  
  {-# COMPILED error    \ _ s -> error s #-}  
  {-# COMPILED flip     Random.randomRIO (True , False) #-}  
  {-# COMPILED fix      \ _ -> let fix f = f (fix f) in fix #-}

  postulate
    IORef : Set -> Set
    newIORef : ∀ {A} -> A -> IO (IORef A)
    readIORef : ∀ {A} -> IORef A -> IO A
    writeIORef : ∀ {A} -> IORef A -> A -> IO MyUnit
  {-# IMPORT Data.IORef  #-}
  {-# COMPILED_TYPE IORef Data.IORef.IORef #-}
  {-# COMPILED newIORef \ _ x -> Data.IORef.newIORef x #-}
  {-# COMPILED readIORef \ _ x -> Data.IORef.readIORef x #-}
  {-# COMPILED writeIORef \ _ x y -> Data.IORef.writeIORef x y #-}

