open import lib.SumsProds
open Sums 
open Prods

module lib.Not where

module Not where

  ¬ : Set -> Set
  ¬ A = A -> Void

  ¬Either : {A B : Set} -> ¬ (Either A B) -> (¬ A) × (¬ B)
  ¬Either f = ( (\a -> f (Inl a)) , \b -> f (Inr b))

  un¬Either : {A B : Set} -> (¬ A) × (¬ B) -> ¬ (Either A B)
  un¬Either (nota , notb) (Inl a) = nota a   
  un¬Either (nota , notb) (Inr b) = notb b

--  ¬× : {A B : Set} -> ¬ (A × B) -> Either (¬ A) (¬ B)

  un¬× : {A B : Set} -> Either (¬ A) (¬ B) -> ¬ (A × B) 
  un¬× (Inl nota) (a , b) = nota a
  un¬× (Inr notb) (a , b) = notb b

  Decidable : Set -> Set
  Decidable A = Either A (¬ A)

  contrapos : {A B : Set} → (A → B) → ¬ B → ¬ A
  contrapos P B A = B (P A)