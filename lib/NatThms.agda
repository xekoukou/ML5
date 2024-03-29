open import lib.Nat
open Natm
open import lib.SumsProds
open Sums
open Prods
open import lib.Id
open Idm
open import lib.Not
open Not

module lib.NatThms where

module NatThms where
  
  data Lt : Nat -> Nat -> Set where
    Lt/zs : forall {n} -> Lt Z (S n)
    Lt/ss : forall {n n'} -> Lt n n' -> Lt (S n) (S n')
  
  data Gt : Nat -> Nat -> Set where
    Gt/sz : {n : _} -> Gt (S n) Z 
    Gt/ss : {n : _} {n' : _} -> Gt n n' -> Gt (S n) (S n')
  
  Lte : Nat -> Nat -> Set
  Lte a b = Either (Lt a b) (Id a b)
  
  data Trich (n : Nat) (m : Nat) : Set where
    LT : Lt n m -> Trich n m
    GT : Gt n m -> Trich n m
    EQ : Id n m -> Trich n m
  
  trich : (n : Nat) -> (m : Nat) -> Trich n m
  trich Z (S _) = LT Lt/zs
  trich (S _) Z = GT Gt/sz
  trich Z  Z = EQ Refl
  trich (S n) (S n') with trich n n' 
  ...                  | LT l = LT (Lt/ss l)
  ...                  | GT g = GT (Gt/ss g)
  ...                  | EQ p = EQ (subst (\k -> Id (S n) (S k)) p Refl)
  
  natEq : (n : Nat) -> (m : Nat) -> Maybe (Id n m)
  natEq Z Z = Some Refl
  natEq (S n) (S m) = Sums.mapMaybe (\ y ->  (substeq S y))  (natEq n m)
  natEq _ _ = None

  id-s-cong : {n n' : Nat} -> Id n n' -> Id (S n) (S n')
  id-s-cong Refl = Refl
  
  id-s-cong-inv : {n n' : Nat} -> Id (S n) (S n') -> Id n n'
  id-s-cong-inv Refl = Refl
  
  +-rh-z : (n : Nat) -> Id n (n + Z)
  +-rh-z Z = Refl
  +-rh-z (S n) = id-s-cong (+-rh-z n)
  
  +-rh-s : (n m : Nat) -> Id (S (n + m)) (n + S m)
  +-rh-s Z _ = Refl
  +-rh-s (S n) m = id-s-cong (+-rh-s n m)
  
  +-comm : (n m : Nat) -> Id (n + m) (m + n)
  +-comm Z m = +-rh-z m
  +-comm (S n) m = trans (id-s-cong (+-comm n m)) (+-rh-s m n)
  
  lt/my-succ : (n : _) -> Lt n (S n)
  lt/my-succ Z = Lt/zs
  lt/my-succ (S n) = Lt/ss (lt/my-succ n)

  lt-leq# : {n n' : Nat} -> Lt n n' -> Lte n' n -> Void
  lt-leq# Lt/zs (Inl ()) 
  lt-leq# Lt/zs (Inr ()) 
  lt-leq# (Lt/ss y) (Inl (Lt/ss y')) = lt-leq# y (Inl y')
  lt-leq# (Lt/ss y) (Inr Refl) = lt-leq# y (Inr Refl)

  lt/s-right : {n n' : Nat} -> Lt n n' -> Lt n (S n')
  lt/s-right Lt/zs = Lt/zs
  lt/s-right (Lt/ss l) = Lt/ss (lt/s-right l)
  
  lt/+-right : {n n' : Nat} (k : Nat) -> Lt n n' -> Lt n (k + n')
  lt/+-right Z l = l
  lt/+-right (S k) l = lt/s-right (lt/+-right k l)
  
  lt/+-right-comm : {n n' : Nat} (k : Nat) -> Lt n n' -> Lt n (n' + k)
  lt/+-right-comm {n} {n'} k l = subst (\k -> Lt n k) (+-comm k n') (lt/+-right k l)
  
  lt/+-both : {n n' : Nat} (k : Nat) -> Lt n n' -> Lt (k + n) (k + n')
  lt/+-both Z l = l
  lt/+-both (S k) l = Lt/ss (lt/+-both k l)
  
  lt/+-both-comm : {n n' : Nat} (k : Nat) -> Lt n n' -> Lt (n + k) (n' + k) 
  lt/+-both-comm {n} {n'} k l = subst (\l1 -> Lt l1 (n' + k))
                                      (+-comm k n)
                                      (subst (\l2 -> Lt (k + n) l2) (+-comm k n') (lt/+-both k l))
  
  lte/s-right : {n m : Nat} -> Lte n m -> Lte n (S m)
  lte/s-right (Inr Refl) = Inl (lt/my-succ _)
  lte/s-right (Inl l)    = Inl (lt/s-right l)
  
  lte/ss : {a b : Nat} -> Lte a b -> Lte (S a) (S b)
  lte/ss (Inl l) = Inl (Lt/ss l)
  lte/ss (Inr e) = Inr (id-s-cong e)
  
  refute-lt-z : (a : Set) {n : Nat} -> Lt n Z -> a
  refute-lt-z a ()
  
  lt/pred-left : {n : Nat} {m : Nat} -> Lt (S n) m -> Lt n m
  lt/pred-left (Lt/ss d) = lt/s-right d
  
  lte/pred-left : {n : Nat} {m : Nat} -> Lte (S n) m -> Lte n m
  lte/pred-left (Inl (Lt/ss y)) = Inl (lt/s-right y)
  lte/pred-left (Inr Refl) = Inl (lt/my-succ _)

  lte-if-lt-s : {n : Nat} {m : Nat} -> Lt n (S m) -> Lte n m
  lte-if-lt-s {Z} {Z} _ = Inr Refl 
  lte-if-lt-s {Z} {S n} _ = Inl Lt/zs
  lte-if-lt-s {S n} {Z} (Lt/ss ()) 
  lte-if-lt-s {S n} {S m} (Lt/ss e) = lte/ss (lte-if-lt-s e)
  
  lt-if-lte-s : {n : Nat} {m : Nat} -> Lte (S n) m -> Lt n m
  lt-if-lte-s (Inr Refl) = lt/my-succ _
  lt-if-lte-s (Inl lt)   = lt/pred-left lt 
  
  lte-if-summand : (n m : Nat) -> (Lte n (n + m) × Lte m (n + m))
  lte-if-summand Z Z   = (Inr Refl , Inr Refl)
  lte-if-summand Z (S m) = (Inl Lt/zs , Inr Refl)
  lte-if-summand (S n) m = (lte/ss (fst (lte-if-summand n m)) , 
                              lte/s-right (snd (lte-if-summand n m)))
  
  lte-if-summand/id : {n m l : Nat} -> Id (n + m) l -> (Lte n l × Lte m l)
  lte-if-summand/id Refl = lte-if-summand _ _
  
  lt-proof-unique : {n m : Nat} -> (p1 p2 : Lt n m) -> Id p1 p2
  lt-proof-unique Lt/zs Lt/zs = Refl
  lt-proof-unique (Lt/ss p1) (Lt/ss p2) = subst (\x -> Id (Lt/ss p1) (Lt/ss x)) (lt-proof-unique p1 p2) Refl
  
  
  -- well-foundedness
  
  data LtAccess (x : Nat) : Set where
    LtAcc : ((y : Nat) -> Lt y x -> LtAccess y) -> LtAccess x
  
  unAcc : {x : _} -> LtAccess x -> ((y : Nat) -> Lt y x -> LtAccess y)
  unAcc (LtAcc f) = f
  
  wf : (x : Nat) -> LtAccess x
  wf Z     = LtAcc (\n -> refute-lt-z (LtAccess n)) 
  wf (S n) = LtAcc res
       where res : (y : Nat) -> Lt y (S n) -> LtAccess y
             res y p with lte-if-lt-s p 
             ...        | Inr eq         = subst (\k -> LtAccess k) (sym eq) (wf n)
             ...        | Inl lt         = unAcc (wf n) y lt
  
  -- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  -- boolean-valued orderings

  eq : Nat -> Nat -> Bool
  eq Z Z = True
  eq Z (S _) = False
  eq (S _) Z = False
  eq (S x) (S y) = eq x y
  
  lt2 : Nat -> Nat -> Bool
  lt2 Z Z      = False
  lt2 Z (S _ ) = True
  lt2 (S _) Z = False
  lt2 (S n) (S n') = lt2 n n'
  
  witness-lt : forall {n m} -> Check (lt2 n m) -> Lt n m
  witness-lt {Z} {Z} () 
  witness-lt {S _} {Z} () 
  witness-lt {Z} {(S _)} p with checki p 
  ...                         | OK = Lt/zs
  witness-lt {S n} {S n'} p = Lt/ss (witness-lt {n} {n'} p)
  



