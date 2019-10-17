module lib.Id where

module Idm where

  module IdOP where
    data Id {A : Set} : A -> A -> Set where
      Refl : {a : A} -> Id a a
    {-# BUILTIN EQUALITY Id #-}
    {-# BUILTIN REFL Refl #-}
  
    data HId {A : Set} (a : A) : {B : Set} -> B -> Set where
      HRefl : HId a a 
  
  module Hom where
    open IdOP

    fromHet : {A : Set} {x y : A} -> HId x y -> Id x y 
    fromHet HRefl = Refl

    subst : {a : Set} (p : a -> Set) {x : a} {y : a} -> Id x y -> p x -> p y
    subst _ Refl t = t
    
    irrel-subst : {a : Set} {x : a} 
                  (p : (y : a) -> Id x y -> Set)
                -> {y : a} -> (pf : Id x y) -> p x Refl 
                -> p y pf
    irrel-subst _ Refl t = t

    sym : {a : Set} {x y : a} -> Id x y -> Id y x 
    sym Refl = Refl
    
    trans : {a : Set} {x y z : a} -> Id x y -> Id y z -> Id x z
    trans Refl Refl = Refl
    
    _===_ :  {a : Set} {x y z : a} -> Id x y -> Id y z -> Id x z
    _===_ = trans
    infixl 2 _===_
    
    substeq : {a b : Set} (p : a -> b) -> {x y : a}  -> Id x y -> Id (p x) (p y)
    substeq _ Refl = Refl

    -- FIXME: version where p is dependent
    substeq2 : {a b c : Set} (p : a -> b -> c) -> {x y : a} {z w : b} -> Id x y -> Id z w -> Id (p x z) (p y w)
    substeq2 _ Refl Refl = Refl
  
    substeq3 : {a b c d : Set} (p : a -> b -> c -> d) -> {x y : a} {z w : b} {u v : c} 
             -> Id x y -> Id z w -> Id u v -> Id (p x z u) (p y w v)
    substeq3 _ Refl Refl Refl = Refl


    substeq4 : {a b c d e : Set} (p : a -> b -> c -> d -> e) -> {x y : a} {z w : b} {u v : c} {t t' : d} 
             -> Id x y -> Id z w -> Id u v -> Id t t' -> Id (p x z u t) (p y w v t')
    substeq4 _ Refl Refl Refl Refl = Refl

    
    substeqeq : {a b : Set} {p p' : a -> b} -> {x y : a} -> ((x : a) -> Id (p x) (p' x)) -> Id x y -> Id (p x) (p' y)
    substeqeq ph Refl = ph _
    
    weak-coh : {a : Set} {x : a} (pf : Id x x) {p : a -> Set} (e : p x) -> Id e (subst p pf e) 
    weak-coh Refl e = Refl
    
    cconv-subst : forall {a x y}
                  (pf : Id x y) ->
                  (p p' : a -> Set) ->
                  (e : p x) ->
                  (f : a -> a) -> 
                  (c  : {x : a} -> p x -> p' (f x))
                  (pf' : Id (f x) (f y)) ->
                  Id (c (subst p pf e)) (subst p' pf' (c e))
    cconv-subst Refl p p' e c f Refl = Refl 

    data Inspect {a : Set} (x : a) : Set where
      _with-eq_ : (y : a) (eq : Id y x) -> Inspect x

    inspect : forall {a} (x : a) -> Inspect x
    inspect x = x with-eq Refl
  
-- FIXME: implement more of the above
  module Het where
    open IdOP

    fromHom : {A : Set} {x : A} {y : A} -> Id x y -> HId x y
    fromHom Refl = HRefl 

    toHom : {I : Set} {A : I -> Set} {i1 i2 : I} {x : A i1} {y : A i2}
          -> (p : Id i1 i2)
          -> HId x y
          -> Id (Hom.subst A p x) y
    toHom Refl HRefl = Refl

    subst-irrel-hom : {a : Set} (p : a -> Set) {x : a} {y : a} -> (id : Id x y) -> (e : p x) 
                    -> HId e (Hom.subst p id e)
    subst-irrel-hom p Refl e = HRefl

    refleq : {I : Set} {i1 i2 : I} (p : HId i1 i2) 
           -> (A : I -> Set) (f : {i : I} -> A i) -> HId (f {i1}) (f {i2})
    refleq HRefl A f = HRefl 

{-
    irrel-hom : {A : Set} {B : Set} {x y : A} {x' y' : B} {p : Id x y} {p' : Id x' y'}
              -> HId x x'
              -> HId y y'
              -> HId p p'
    irrel-hom HRefl HRefl = HRefl
-}

{-
    trans : {I : Set} (A : I -> Set)
            {i1 : I} {i2 : I} {i3 : I} 
          -> HId i1 i2 -> HId i2 i3
          -> {x : A i1} {y : A i2} {z : A i3}
          -> HId x y -> HId y z -> HId x z
    trans _ HRefl HRefl HRefl HRefl = HRefl
-}

    -- uses a new feature of pattern matching, where you can
    -- match with HRefl even when the types aren't equal,
    -- which asserts that the types are equal.
    trans : {A B C : Set} {x : A} {y : B} {z : C} -> HId x y -> HId y z -> HId x z 
    trans HRefl HRefl = HRefl

    sym : {A B : Set} {x : A} {y : B} -> HId x y -> HId y x
    sym HRefl = HRefl

    -- what's the most general thing here?
    substeq/hom : {a b : Set} (p : a -> b) -> {x y : a}  -> HId x y -> HId (p x) (p y)
    substeq/hom _ HRefl = HRefl

    substeq/hom2 : {a b c : Set} (p : a -> b -> c) -> {x y : a} {z w : b} -> HId x y -> HId z w -> HId (p x z) (p y w)
    substeq/hom2 _ HRefl HRefl = HRefl
  
    substeq/hom3 : {a b c d : Set} (p : a -> b -> c -> d) -> {x y : a} {z w : b} {u v : c} 
             -> HId x y -> HId z w -> HId u v -> HId (p x z u) (p y w v)
    substeq/hom3 _ HRefl HRefl HRefl = HRefl

    substeq/hom4 : {a b c d e : Set} (p : a -> b -> c -> d -> e) -> {x y : a} {z w : b} {u v : c} {t t' : d} 
             -> HId x y -> HId z w -> HId u v -> HId t t' -> HId (p x z u t) (p y w v t')
    substeq/hom4 _ HRefl HRefl HRefl HRefl = HRefl

    substeq/ind : {I : Set} {A : I -> Set} {B : I -> Set} 
                (c : {i : I} -> A i -> B i) 
                {i : I} {j : I}
                (p : HId i j) {x : A i} {y : A j}
                -> HId x y -> HId (c x) (c y)
    substeq/ind c HRefl HRefl = HRefl

    substeq/2ind : {I : Set} {I2 : Set}
                   {A : I -> I2 -> Set} {B : I -> I2 -> Set} 
                   (c : {i : I} {i2 : I2} -> A i i2 -> B i i2) 
                   {i : I} {j : I} {i2 : I2} {j2 : I2}
                   (p : HId i j) (p2 : HId i2 j2) 
                   {x : A i i2} {y : A j j2}
                   -> HId x y -> HId (c x) (c y)
    substeq/2ind c HRefl HRefl HRefl = HRefl

    substeq/3ind : {I : Set} {I2 : Set} {I3 : Set}
                   {A : I -> I2 -> I3 -> Set} {B : I -> I2 -> I3 -> Set} 
                   (c : {i : I} {i2 : I2} {i3 : I3} -> A i i2 i3 -> B i i2 i3) 
                   {i : I} {j : I} {i2 : I2} {j2 : I2} {i3 : I3} {j3 : I3} 
                   (p : HId i j) (p2 : HId i2 j2) (p3 : HId i3 j3) 
                   {x : A i i2 i3} {y : A j j2 j3}
                   -> HId x y -> HId (c x) (c y)
    substeq/3ind c HRefl HRefl HRefl HRefl = HRefl

  module Hom1 where
    data Id {A : Set1} : A -> A -> Set1 where
      Refl : {a : A} -> Id a a
  
    subst : {a : Set1} (p : a -> Set1) {x : a} {y : a} -> Id x y -> p x -> p y
    subst _ Refl t = t
    
    sym : {a : Set1} {x y : a} -> Id x y -> Id y x 
    sym Refl = Refl
    
    trans : {a : Set1} {x y z : a} -> Id x y -> Id y z -> Id x z
    trans Refl Refl = Refl
    
    _===_ :  {a : Set1} {x y z : a} -> Id x y -> Id y z -> Id x z
    _===_ = trans
    infixl 2 _===_
    
    substeq : {a b : Set1} (p : a -> b) -> {x y : a}  -> Id x y -> Id (p x) (p y)
    substeq _ Refl = Refl

    -- FIXME: version where p is dependent
    substeq2 : {a b c : Set1} (p : a -> b -> c) -> {x y : a} {z w : b} -> Id x y -> Id z w -> Id (p x z) (p y w)
    substeq2 _ Refl Refl = Refl
  
    substeq3 : {a b c d : Set1} (p : a -> b -> c -> d) -> {x y : a} {z w : b} {u v : c} 
             -> Id x y -> Id z w -> Id u v -> Id (p x z u) (p y w v)
    substeq3 _ Refl Refl Refl = Refl

    substeq4 : {a b c d e : Set1} (p : a -> b -> c -> d -> e) -> {x y : a} {z w : b} {u v : c} {t t' : d} 
             -> Id x y -> Id z w -> Id u v -> Id t t' -> Id (p x z u t) (p y w v t')
    substeq4 _ Refl Refl Refl Refl = Refl

    substeqeq : {a b : Set1} {p p' : a -> b} -> {x y : a} -> ((x : a) -> Id (p x) (p' x)) -> Id x y -> Id (p x) (p' y)
    substeqeq ph Refl = ph _
    
    weak-coh : {a : Set1} {x : a} (pf : Id x x) {p : a -> Set1} (e : p x) -> Id e (subst p pf e) 
    weak-coh Refl e = Refl
    
    cconv-subst : forall {a x y}
                  (pf : Id x y) ->
                  (p p' : a -> Set1) ->
                  (e : p x) ->
                  (f : a -> a) -> 
                  (c  : {x : a} -> p x -> p' (f x))
                  (pf' : Id (f x) (f y)) ->
                  Id (c (subst p pf e)) (subst p' pf' (c e))
    cconv-subst Refl p p' e c f Refl = Refl 

    data Inspect {a : Set1} (x : a) : Set1 where
      _with-eq_ : (y : a) (eq : Id y x) -> Inspect x

    inspect : forall {a} (x : a) -> Inspect x
    inspect x = x with-eq Refl

  -- for easy access
  open IdOP public
  open Hom public
