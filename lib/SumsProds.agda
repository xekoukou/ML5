open import lib.Id
open Idm
open import lib.Nat
open Natm

module lib.SumsProds where

  data Fin : Natm.Nat -> Set where
    Fz : {n : Natm.Nat} -> Fin (Nat.S n)
    Fs : {n : Natm.Nat} -> Fin n -> Fin (Nat.S n)

  -- FIXME : relate to Sigma k.Lt k n 

  module Prods where

    module ProdsOP where
      record Unit : Set where
      <> : Unit 
      <> = record {}
  
      data Σ {a : Set} (b : a -> Set) : Set where
        _,_ : (x : a) -> (b x) -> Σ b
      
      infixr 0 _,_
      
      _×_ : Set -> Set -> Set
      a × b = Σ (\ (_ : a) -> b)

      infixr 10 _×_

      fst : {a : _} {b : a -> Set} -> Σ (\ (x : a) -> b x) -> a
      fst (x , y) = x
       
      snd : {a : _} {b : a -> Set } (p : Σ {a} b) -> (b (fst p))
      snd (x , y) = y

      third : {a : _} {b : a -> Set} {c : (x : a) -> (b x) -> Set} 
            -> (p : (Σ \ (x : a) -> Σ \(y : b x) -> (c x y)))
            -> (c (fst p) (fst (snd p)))
      third (x , y , z) = z

--      fourth = \x -> fst (snd (snd x))

    open ProdsOP public

    split : {A : Set} {B : A -> Set} {C : Σ B -> Set}
            (p : Σ B) 
            -> ((x : A) (y : B x) -> C (x , y)) 
            -> C p
    split (x , y) f = f x y

    choice : {A B : Set} {R : A -> B -> Set} 
           -> ((x : A) -> Σ (\y -> R x y))
           -> (Σ \ (f : A -> B) -> (x : A) -> (R x (f x)))
    choice f = (\x -> fst (f x)) , \x -> snd (f x)
 
    data NDPair (A B : Set) : Set where
      _,_ : A -> B -> NDPair A B

    ndToDep : ∀ {A B} -> NDPair A B -> A × B
    ndToDep (x , y) = (x , y)

    depToND : ∀ {A B} -> A × B -> NDPair A B
    depToND (x , y) = (x , y)
   
    module Eta where
           
       Σ-eta+ : forall {A B} 
                {C : Σ B -> Set}
                {ctxt : (p : Σ {A} B) -> C p}
                (p : Σ B)
                -> Id (ctxt p) (split {A}{B}{C} p (\ x y -> ctxt (x , y)))
       Σ-eta+ (x , y) = Refl
    
       Σ-eta- : {A : Set} {B : A -> Set} (x : Σ (\(x : A) -> B x)) -> Id x (fst x , snd x)
       Σ-eta- (x , y) = Refl
       
       -- ENH: would be prettier with heterogeneous equality 
       Σ-ext- : {A : _} {B : A -> Set} {x y : Σ (\ (x : A) -> B x)} 
             -> (p1 : Id (fst x) (fst y))
             -> (p2 : Id {(B (fst x))} (snd x) (subst B (sym p1) (snd y)))
             -> Id x y
       Σ-ext- {A} {B} {(xf , xs)} {yf , ys} p1 p2 = id2 (sym p1) id0
         where id0 : Id {A × (B xf)} (xf , xs) (yf , subst B (sym p1) ys)
               id0 = substeqeq {_} {_} {\f ->  (f , xs)} {\f -> (f , subst B (sym p1) ys)}
                     (\x' -> substeq (\s -> x' , s) p2)
                     p1
       
               id1 : forall {xf xs ys} ->
                     Id {Σ (\_ -> (B xf))} (xf , xs) (xf , ys) ->
                     Id {Σ B} (xf , xs) (xf , ys)
               id1 Refl = Refl
       
               id2 : forall {xf yf xs ys} (p : Id yf xf) ->
                     Id {A × (B xf)} (xf , xs) (yf , subst B p ys)
                     -> Id {Σ B} (xf , xs) (yf , ys)
               id2 Refl p = id1 p 

  module Sums where
    open Prods

    module SumsOP where
      data Void : Set where
  
      data Either (a : Set) (b : Set) : Set where
        Inl : a -> Either a b
        Inr : b -> Either a b
  
      data Maybe (a : Set) : Set where
        Some : a -> Maybe a
        None : Maybe a

      data Bool : Set where
        True : Bool
        False : Bool
 --     {-# COMPILED_DATA Bool Bool True False #-}
  
      if_/_then_else : (p : Bool -> Set) -> (b : Bool) -> p True -> p False -> p b
      if _ / True then b1 else b2 = b1
      if _ / False then b1 else b2 = b2
     
      -- FIXME: better way than copying?
      if1_/_then_else : (p : Bool -> Set1) -> (b : Bool) -> p True -> p False -> p b
      if1 _ / True then b1 else b2 = b1
      if1 _ / False then b1 else b2 = b2
     
      Check : Bool -> Set 
      Check True  = Unit
      Check False = Void

      data CheckI : Bool -> Set where
        OK : CheckI True

      checki : forall {b : Bool} -> Check b -> CheckI b
      checki {True} _ = OK
      checki {False} ()

      check : (b : Bool) -> Either (Check b) (Id b False)
      check False = Inr Refl
      check True = Inl <>

      check/i : (b : Bool) -> Either (CheckI b) (Id b False)
      check/i False = Inr Refl
      check/i True = Inl OK
      
      _andalso_ : Bool -> Bool -> Bool 
      b1 andalso b2 = if (\_ -> Bool) / b1 then b2 else False
      
      _orelse_ : Bool -> Bool -> Bool 
      b1 orelse b2 = if (\_ -> Bool) / b1 then True else b2
      
      check-andI : {b1 b2 : Bool} -> Check b1 -> Check b2 -> Check (b1 andalso b2)
      check-andI {True} {True} _ _ = <>
      check-andI {False} () _ 
      check-andI {_} {False} _ () 

      check-andE : {b1 b2 : Bool} -> Check (b1 andalso b2) -> Check b1 × Check b2 
      check-andE {True} {True} _ = (_ , _)
      check-andE {False} ()  
      check-andE {True} {False} () 

      check-id-not : {b1 : Bool} -> Id b1 False -> Check (if (\ _ -> Bool) / b1 then False else True)
      check-id-not Refl = _

      check-noncontra : (b : Bool) -> Check b -> Check (if (\ _ -> Bool) / b then False else True) -> Void
      check-noncontra True _ v = v
      check-noncontra False v _ = v

      {-# BUILTIN BOOL  Bool  #-}
      {-# BUILTIN TRUE  True  #-}
      {-# BUILTIN FALSE False #-}
    
    open SumsOP public

    case : {A B C : Set} -> Either A B -> (A -> C) -> (B -> C) -> C
    case (Inl x) e1 e2 = e1 x
    case (Inr x) e1 e2 = e2 x
  
    abort : {A : Set} -> Void -> A
    abort () 
    
    join1 : {a : Set} -> Maybe a -> Maybe a -> Maybe a
    join1 (Some x) _ = Some x
    join1 None     b = b
    
    join2 : {a : Set} -> Maybe a -> Maybe a -> Maybe a
    join2 _   (Some y) = Some y
    join2 a   None     = a

    not : Bool -> Bool
    not b = if (\ _ -> Bool) / b then False else True

    forgetMaybe : {A : Set} {B : A -> Set} -> ((x : A) -> Maybe (B x)) -> (A -> Bool)
    forgetMaybe f x with f x
    ... | Some _ = True
    ... | None = False
  
    extract-forgotten : {A : Set} {B : A -> Set} -> (f : (x : A) -> Maybe (B x)) (x : A) -> Check (forgetMaybe f x) -> (B x)
    extract-forgotten f x p with f x
    ... | Some b = b
    extract-forgotten _ _ () | None 
     
    mapMaybe : ∀ {A B} -> (A -> B) -> Maybe A -> Maybe B
    mapMaybe f (Some x) = Some (f x)
    mapMaybe f None = None

    isSome : {A : Set} -> Maybe A -> Bool 
    isSome (Some _) = True
    isSome None = False

    getSome : {A : Set} (s : Maybe A) -> {_ : Check (isSome s)} -> A
    getSome (Some x) = x
    getSome None {()}

    solve : {A : Set} (s : Maybe A) -> {_ : Check (isSome s)} -> A
    solve = getSome

    case_None⇒_Some⇒ : ∀ {A C : Set} -> (Maybe A) -> C -> (A -> C) -> C
    case None None⇒ e1 Some⇒ e2 = e1
    case (Some x) None⇒ e1 Some⇒ e2 = e2 x

    none⇒_some⇒ : ∀ {A C : Set} -> C -> (A -> C) -> Maybe A -> C
    none⇒ n some⇒ y e = case e None⇒ n Some⇒ y

    forgetMaybe2  : {a : Set}{C : a -> a -> Set}  -> ((x : a) -> (y : a) -> Maybe (C x y)) -> (a -> a -> Bool)
    forgetMaybe2 f x y  with (f x y) 
    ...                | Some t = True
    ...                | None = False



