
open import lib.SumsProds
open Sums
open Prods
open import lib.Nat
open Nat
open import lib.NatThms
open NatThms
open import lib.Id
open Id 

module lib.List where

module List where

  module ListOP where

    data List (a : Set) : Set where
      []  : List a
      _::_ : a -> List a -> List a 

    {-# COMPILED_DATA List [] [] (:) #-}
    {-# BUILTIN LIST List #-}
    {-# BUILTIN NIL [] #-}
    {-# BUILTIN CONS _::_ #-}

    infixr 99 _::_
    
    [_] : {A : Set} -> A -> List A
    [_] x  = x :: []

    -- we expand this out, rather than using (Somewhere (\x -> Id x a) l)
    -- so that we don't have to write the silly identity proof in the deBruijn index 
    data _∈_ {A : Set} : A -> List A -> Set where
      i0 : {x : A}   {xs : List A} -> x ∈ (x :: xs )
      iS : {x y : A} {xs : List A} -> y ∈ xs -> y ∈ (x :: xs)
    infix 10 _∈_

    data Everywhere {A : Set} (P : A -> Set) : List A -> Set where
      E[] : Everywhere P []
      _E::_ : forall {x xs} -> P x -> Everywhere P xs -> Everywhere P (x :: xs) 

    infixr 98 _E::_

  open ListOP public

  Lists : Set -> Set
  Lists A = List (List A)

-- FIXME: organize the theorems

  append : forall {a} -> List a -> List a -> List a
  append [] l2 = l2
  append (x :: xs) l2 = x :: (append xs l2)

  invert-append-nil : {A : Set} {l1 l2 : List A} -> Id (append l1 l2) [] -> Id l1 [] × Id l2 []
  invert-append-nil {A} {[]} id = Refl , id
  invert-append-nil {A} {x :: xs} ()

  appendmayber : forall {a} -> List a -> List a -> List a
  appendmayber l1 [] = l1
  appendmayber l1 (x :: xs) = append l1 (x :: xs)
  
  append-rh-[] : {A : Set} -> (l : List A) -> Id (append l []) l
  append-rh-[] [] = Refl
  append-rh-[] (h :: tl) with (append tl []) | append-rh-[] tl 
  ...                       | .tl            | Refl = Refl

  appendmayber-is-append : {A : Set} -> (l1 l2 : List A) -> Id (appendmayber l1 l2) (append l1 l2)
  appendmayber-is-append _ [] = Id.sym (append-rh-[] _)
  appendmayber-is-append _ (x :: xs) = Refl

  _++_ : {a : Set} -> List a -> List a -> List a
  _++_ = append
  infixr 20 _++_

  append-assoc : {A : Set} {l1 l2 l3 : List A} -> Id ((l1 ++ l2) ++ l3) (l1 ++ (l2 ++ l3))
  append-assoc {_}{[]} {l2} {l3} = Refl
  append-assoc {_}{x1 :: l1} {l2} {l3} = Id.substeq (\xs -> x1 :: xs) (append-assoc {_} {l1} {l2} {l3})

  fold : {a b : Set} -> b -> (a -> b -> b) -> List a -> b
  fold n c [] = n
  fold n c (x :: xs) = c x (fold n c xs)

  concat : {A : Set} -> List (List A) -> List A
  concat = fold [] append

  map : {a b : Set} -> (a -> b) -> List a -> List b
  map f [] = []
  map f (x :: xs) = f x :: (map f xs)

  mapid : {A : Set} (l : List A) -> Id (map (\x -> x) l) l
  mapid [] = Refl
  mapid (x :: xs) with (map (\x -> x) xs) | mapid xs
  ...                | .xs                | Refl = Refl

  append-maps : {A B : Set} (l1 l2 : List A) {f : A -> B} -> Id ((map f l1) ++ (map f l2)) (map f (append l1 l2))
  append-maps []        l2 = Refl
  append-maps (x :: l1) l2 {f} = Id.substeq (\ l -> f x :: l)  (append-maps l1 l2)

  fuse-map : ∀ {A B C} {f : A -> B} {g : B -> C} (l : List A) -> Id (map g (map f l)) (map (\ x -> g (f x)) l) 
  fuse-map [] = Refl
  fuse-map {f = f} {g = g} (x :: xs) = Id.substeq (\ xs -> (g (f x)) :: xs) (fuse-map xs)

  map-ext : ∀ {A B} {f g : A -> B} -> ((x : A) -> Id (f x) (g x)) -> (l : List A) -> Id (map f l) (map g l)
  map-ext id [] = Refl
  map-ext id (x :: xs) = Id.substeq2 _::_ (id x) (map-ext id xs)
  
  map-compose : ∀ {A B B' C} {f : A -> B} {g : B -> C} {f' : A -> B'} {g' : B' -> C} {l : List A}
              -> ((x : A) -> Id (g (f x)) (g' (f' x))) 
              -> Id (map g (map f l)) (map g' (map f' l))
  map-compose {l = l} id = Id.trans (fuse-map l) (Id.trans (map-ext id l) (Id.sym (fuse-map l)))

  fold-map : ∀ {A B C} {f : A -> B} {n : C} {c : B -> C -> C} 
           -> (l : List A)
           -> Id (fold n c (map f l)) (fold n (\ hd r -> c (f hd) r) l)
  fold-map [] = Refl
  fold-map{f = f}{c = c} (x :: xs) = Id.substeq (\ tl -> c (f x) tl) (fold-map xs)
  
  length : forall {a} -> List a -> Nat.Nat
  length []       = Nat.Z
  length (x :: xs) = S (length xs)

  exists : {a : Set} -> (a -> Bool) -> List a -> Bool
  exists f [] = False
  exists f (x :: xs) with f x 
  ...                   | True  = True
  ...                   | False = exists f xs

  all : {a : Set} -> (a -> Bool) -> List a -> Bool
  all f [] = True
  all f (x :: xs) = (f x) andalso (all f xs)
  
  find : {a : Set} -> (a -> Bool) -> List a -> Maybe a
  find f [] = None
  find f (x :: xs) with f x 
  ...                   | True  = Some x
  ...                   | False = find f xs
  
  -- formerly appendRest
  appendNew : {a : Set}  -> ((x : a) -> (y : a) -> (Maybe (Id x y))) -> List a -> List a -> List a
  appendNew f l1 [] = l1
  appendNew f l1 (x :: xs)  with (find (Sums.forgetMaybe2 f x) l1)
  ...                          | Some k = appendNew f l1 xs
  ...                          | None = appendNew f (x :: l1) xs
    
  _+-_ : {a : Set} -> ((x : a) -> (y : a) -> (Maybe (Id x y ))) ->  List a -> List a -> List a
  _+-_ = appendNew
  infixr 20 _+-_
  

  findMod : {a : Set} {b : Set} -> (a -> Maybe b) -> List a -> Maybe b
  findMod f [] = None
  findMod f (x :: xs) = join1 (f x) (findMod f xs)
  
  nth : {a : Set} (n : Nat) -> (l : List a) -> Lt n (length l) -> a
  nth _ [] ()
  nth Z (x :: xs) _             = x
  nth (S n) (_ :: xs) (Lt/ss l) = nth n xs l

  filter : {a : Set} -> (f : a -> Bool) -> List a -> List a
  filter f [] = []
  filter f (x :: xs) with (f x)
  ...                   | True  = x :: (filter f xs)
  ...                   | False = filter f xs

  -- nonsense lemma for in-filter
  fire-filter : {a : Set} -> (x x' : a) -> (xs : List a) -> (f : a -> Bool) 
                -> x ∈ (filter f (x' :: xs)) -> Id True (f x') -> x ∈ x' :: (filter f xs)
  fire-filter x x' xs f i p with (f x')
  ...                          | True = i
  fire-filter _ _ _ _ _ ()   | False 

  in-filter : {a : Set} -> (x : a) -> (l : List a) -> (f : a -> Bool) -> (x ∈ filter f l) ->  ((x ∈ l) × (Id (f x) True))
  in-filter x [] f ()
  in-filter x (x' :: xs) f i with inspect (f x')
  ...                           | False with-eq p with (f x')
  in-filter x (x' :: xs) f i    | False with-eq ()   | True 
  ...                                                | False = iS (fst (in-filter x xs f i)) , snd (in-filter x xs f i)
  in-filter x (x' :: xs) f i    | True with-eq p with fire-filter _ _ _ _ i p
  in-filter x (.x :: xs) f i    | True with-eq p    | i0 = i0 , sym p 
  ...                                               | (iS i') = iS (fst (in-filter x xs f i')) , snd (in-filter x xs f i') 

  filterp : {a b : Set} -> (f : a -> Maybe b) -> List a -> List a
  filterp {a} f l =  filter f' l where
    f' : a -> Bool
    f' x with f x
    ... | Some _ = True
    ... | None = False

  filtermap : {a b : Set} -> (f : a -> Maybe b) -> List a -> List b
  filtermap f [] = []
  filtermap f (x :: xs) with (f x)
  ...                   | Some x'  = x' :: (filtermap f xs)
  ...                   | None = filtermap f xs

  unzip : {A B : Set} -> List (A × B) -> List A × List B
  unzip [] = [] , []
  unzip ((x , y) :: l) with unzip l
  ...                     | (xs , ys) = x :: xs , y :: ys

  reverse : {A : Set} -> List A -> List A
  reverse l = reverse' l [] where
    reverse' : {A : Set} -> List A -> List A -> List A
    reverse' [] l = l
    reverse' (x :: xs) ys = reverse' xs (x :: ys)

  listeq-semidec : ∀ {A} -> (Eq : ((x y : A ) -> Maybe (Id x y)))
                 (L1 L2 : List A) -> Maybe (Id L1 L2)
  listeq-semidec Eq [] [] = Some Refl
  listeq-semidec Eq (x :: xs) (y :: ys) with listeq-semidec Eq xs ys | Eq x y
  listeq-semidec Eq (x :: xs) (.x :: .xs) | Some Refl | Some Refl = Some Refl
  ... | _ | _ = None
  listeq-semidec Eq _ _ = None

  module In where
    iSmany : {A : Set} {a : A} (orig : List A) (new : List A) -> (a ∈ orig) -> (a ∈ (new ++ orig))
    iSmany l1 [] i = i
    iSmany l1 (a' :: l2) i = iS (iSmany l1 l2 i)

    skip : {A : Set} (l1 : List A) {l2 : List A} {x : A} -> x ∈ l2 -> x ∈ (l1 ++ l2)
    skip l1 i = iSmany _ l1 i

    iSmanyi : {A : Set} {a : A} (orig : List A) {new : List A} -> (a ∈ orig) -> (a ∈ (new ++ orig))
    iSmanyi l1 {[]} i = i
    iSmanyi l1 {(a' :: l2)} i = iS (iSmanyi l1 {l2} i)
      
    i0-app-right : {A : Set} {a : A} (l1 : List A) ( l2 : List A) 
                 -> (a ∈ (l2 ++ (a :: l1)))
    i0-app-right l1 [] = i0
    i0-app-right l1 (a :: l2) = iS (i0-app-right l1 l2)
    
    iS-app-right : {A : Set} {a a' : A} (l1 : List A) ( l2 : List A) 
                 -> (a ∈ (l2 ++ l1))
                 -> (a ∈ (l2 ++ (a' :: l1)))
    iS-app-right l1 [] i = iS i
    iS-app-right l1 (a :: l2) i0 = i0
    iS-app-right l1 (a0 :: l2) (iS i) = iS (iS-app-right l1 l2 i)
    
    iswapapp : {A : Set} {a : A} (l1 : List A) ( l2 : List A) -> (a ∈ (l2 ++ l1)) -> (a ∈ (l1 ++ l2))
    iswapapp l1 [] i with append l1 [] | append-rh-[] l1
    ...                 | .l1          | Refl = i
    iswapapp l1 (a' :: l2) i0 = i0-app-right l2 l1
    iswapapp l1 (a' :: l2) (iS i) = iS-app-right l2 l1 (iswapapp l1 l2 i)

    iSmany-right : {A : Set} {a : A} (orig : List A) (new : List A) -> (a ∈ orig) -> (a ∈ (orig ++ new))
    iSmany-right l1 l2 i = iswapapp l1 l2 (iSmany l1 l2 i)

    skip/right : {A : Set} {a : A} (orig : List A) {new : List A} -> (a ∈ orig) -> (a ∈ (orig ++ new))
    skip/right orig {new} i = iSmany-right orig new i
    
    incr : {A : Set} {a : A} ( l1 : List A) ( l2 : List A) (a' : A) -> (a ∈ (l2 ++ l1)) -> (a ∈ (l2 ++ (a' :: l1)))
    incr l1 []       a' i = iS i 
    incr l1 (a2 :: l2) a' i0 = i0
    incr l1 (a2 :: l2) a' (iS i') = iS (incr l1 l2 a' i') 
    
    remove : {a : Set} {x : a} (l : List a) -> x ∈ l -> List a
    remove [] () 
    remove (x :: xs) i0 = xs
    remove (x :: xs) (iS i) = x :: (remove xs i)
  
    _-_ : {a : Set} {x : a} (l : List a) -> x ∈ l -> List a
    _-_ = remove
    
    -- ENH: the type could be more precise here:
    -- the output index actually points to the same occurrence as the input!
    splitappend : {A : Set} {a : A} -> (l1 l2 : List A) -> a ∈ (l1 ++ l2) -> Either (a ∈ l1) (a ∈ l2) 
    splitappend [] l2 i = Inr i
    splitappend (l :: l1) l2 i0 = Inl i0 
    splitappend (l :: l1) l2 (iS i') with splitappend l1 l2 i' 
    ...                                 | Inr inl2 =  Inr inl2
    ...                                 | Inl inl1 =  Inl (iS inl1)
    
    indeq : {A : Set} {a : A} {b : A} {f : List A} -> (ia : (a ∈ f)) -> (ib : (b ∈ f))
          -- lossy: only returns exactly the consequences you need below
          -- FIXME: could do better, but I can't figure out how to use heterogeneous equality
          -> Either (Id a b) (b ∈ (remove f ia))
    indeq i0 i0 = Inl Refl
    indeq i0 (iS xs) = Inr xs
    indeq (iS xs) i0 = Inr i0
    indeq {_} {a} {b} (iS i) (iS{x} i') with indeq i i' 
    ...                                    | Inl p = Inl p
    ...                                    | Inr r = Inr (iS {_} {x} r)
    
    neqEltsNeqInds : {A : Set} {a : A} {b : A} {f : List A} 
                   -> (Id a b -> Void) -> (ia : (a ∈ f)) -> (ib : (b ∈ f)) -> (a ∈ (remove f ib))
    neqEltsNeqInds ref i1 i2 with indeq i2 i1 
    ...                         | Inl typeq = abort (ref (sym typeq))
    ...                         | Inr x = x

    indices : {I : Set} (is : List I)
              -> List (Σ \i -> i ∈ is)
    indices [] = []
    indices (i :: is) = ((_ , i0) :: map (\x -> wk x) (indices is)) where
        wk : {I : Set} {is : List I} {j : I}
           -> Σ (\ i -> i ∈ is)
           -> Σ \ i -> i ∈ (j :: is)
        wk (_ , i) = (_ , iS i)

    notin[] : {A C : Set} {x : A} -> x ∈ [] -> C
    notin[] () 

    in-map : {A B : Set} {x : A} {l : List A} {f : A -> B} -> x ∈ l -> f x ∈ map f l
    in-map i0 = i0
    in-map (iS i) = iS (in-map i)

    in-map2 : {A B : Set} {y : B} (l : List A) -> (f : A -> B) -> (i : (y ∈ (map f l))) -> Σ (\ (x : A) -> (x ∈ l) × (Id (f x) y))
    in-map2 {A} {B} (l1 :: ls) f i0 = l1 , i0 , Refl
    in-map2 {A} {B} (l1 :: ls) f (iS i) = _ , iS (fst (snd (in-map2 ls f i))) , snd (snd (in-map2 ls f i))
    in-map2 [] f ()

    commute-map-remove : {A B : Set} {f : A -> B} {x : A} (l : List A) (i : x ∈ l) -> Id (map f (remove l i)) (remove (map f l) (in-map i))
    commute-map-remove [] () 
    commute-map-remove (x :: xs) i0 = Refl
    commute-map-remove {f = f} (x :: xs) (iS i) = Id.substeq (\l -> (f x) :: l) (commute-map-remove xs i)

    find-in : {A : Set} -> (p : (A -> Bool)) -> (l : List A) -> Maybe (Σ \ (x : A) -> (x ∈ l) × Check (p x))
    find-in f [] = None
    find-in f (x :: xs) with check(f x)
    ...                    | Inl c = Some (x , i0 , c)
    ...                    | Inr _ with find-in f xs
    ...                               | Some (_ , i , p) = Some (_ , iS i , p)
    ...                               | None = None

    must-find : {A : Set} -> (p : (A -> Bool)) -> (l : List A) 
                -> {x : A} -> x ∈ l -> Check (p x)
                -> Σ \ y -> Σ \ (i : y ∈ l) -> Σ \ ch -> Id (find-in p l) (Some (y , i , ch))
    must-find p [] () _
    must-find f (x :: xs) i0 ch with check(f x)  
    ...                            | Inl c    = x , i0 , c , Refl
    ...                            | Inr p    = Sums.abort (check-noncontra (f x) ch (check-id-not p))  
    must-find f (x :: xs) (iS i) ch with check(f x)
    ...                                | Inl c  = x , i0 , c , Refl
    ...                                | Inr p  with (find-in f xs)          | must-find f xs i ch 
    ...                                            | .(Some (y' , i' , ch')) | (y' , i' , ch' , Refl) = y' , iS i' , ch' , Refl 

    in-all : {A : Set} {l : List A} -> (p : (A -> Bool)) -> Check (all p l) -> ({x : A} -> x ∈ l -> Check (p x))
    in-all p ch i0 = fst (check-andE ch) 
    in-all {_} {x :: l} p ch (iS i) = in-all p (snd (check-andE{p x} ch)) i 

    every-to-checkall : {A : Set} (l : List A) -> (p : (A -> Bool)) -> ({x : A} -> x ∈ l -> Check (p x)) -> Check (all p l)
    every-to-checkall [] p ev = _ 
    every-to-checkall (x :: l) p ev = check-andI (ev i0) (every-to-checkall l p (\ x' -> ev (iS x')))

    -- analogue of Everywehre's E:: when everywhere is defined elementwise
    ::-every : forall {A y} { P : A -> Set} {l : List A} -> ({x : A} -> x ∈ l -> P x) -> P y -> ({x : A} -> x ∈ (y :: l) -> P x)
    ::-every f p i0 = p
    ::-every f p (iS i) = f i

    remove/append : ∀ {A : Set} (l1 : List A) {l2 : List A} {x : A} (i : x ∈ l2) -> Id (l1 ++ (l2 - i)) ((l1 ++ l2) - skip l1 i)
    remove/append [] l2 = Refl
    remove/append (x :: xs) l2 = Id.substeq2 _::_ Refl  (remove/append xs l2)

    remove/middle : ∀ {A : Set} (l1 : List A) {l2 : List A} {x : A} -> Id (remove (l1 ++ (x :: l2)) (skip l1 i0)) (l1 ++ l2)
    remove/middle [] = Refl
    remove/middle (y :: xs) = Id.substeq2 _::_ Refl (remove/middle xs) 

    split-at : ∀ {A} {l : List A} {x : A} (i : x ∈ l) -> List A × List A
    split-at {A} {_ :: l} i0 = l , []
    split-at {A} {x :: l} (iS i) = fst (split-at i) , x :: (snd (split-at i))
    split-at {A} {[]} ()
  
    before : ∀ {A} {l : List A} {x : A} (i : x ∈ l) -> List A 
    before i = fst (split-at i)
  
    after : ∀ {A} {l : List A} {x : A} (i : x ∈ l) -> List A 
    after i = snd (split-at i)
  
    split-at-combine : ∀ {A} {l : List A} {x : A} (i : x ∈ l) -> Id l ((snd (split-at i)) ++ (x :: (fst (split-at i))))
    split-at-combine i0 = Refl
    split-at-combine {_}{x :: _} (iS i) = Id.substeq (\ xs -> x :: xs) (split-at-combine i)
  
    split-at-remove : ∀ {A} {l : List A} {x : A} (i : x ∈ l) -> Id (remove l i) ((snd (split-at i)) ++ (fst (split-at i)))
    split-at-remove i0 = Refl
    split-at-remove{l = x' :: _} (iS i) = Id.substeq (\ xs -> x' :: xs) (split-at-remove i)
  
    split-at/map : ∀ {A B}  {l : List A} {x : A} (i : x ∈ l) {f : A -> B} -> 
                Id (map f (fst (split-at i))) (fst (split-at (in-map{_}{_}{_}{_}{f} i)))
              × Id (map f (snd (split-at i))) (snd (split-at (in-map{_}{_}{_}{_}{f} i)))
    split-at/map i0 = Refl , Refl
    split-at/map {l = x :: _} (iS i) {f} =  fst (split-at/map i) , Id.substeq (\ l -> f x :: l) (snd (split-at/map i)) 
   

  module Replace {A : Set} (eq : (x y : A) -> Maybe (Id x y)) where
    open In

    replace : {x : A} -> {Γ : List A} -> (y : A) -> ( x ∈ Γ ) -> (List A)
    replace {x} {.x :: Γ } y i0 = y :: Γ
    replace {x} {x' :: Γ} y (iS i) = x' :: (replace y i)
    replace {_} {[]} _ () 

    data Replace : ( x y : A) -> (L1  L2 : List A) -> Set where
      rep : ∀ {x y L1 L2} -> (i : x ∈ L1) -> (Id (replace y i) L2) -> Replace x y L1 L2 

    private
      proveReplaceTl : ∀ {l l'} -> (x y : A ) (ls ls' : List A) 
               -> Maybe (Replace x y ls ls')
               -> Maybe (Replace x y (l :: ls) (l' :: ls'))
      proveReplaceTl x y  ls ls' None = None
      proveReplaceTl {l}{l'} x y  ls ls' (Some (rep i p)) with (eq l l') 
      ... | (Some p1) = Some (rep (iS i) (Id.substeq2 _::_ p1 p))
      ... | None = None
    
      proveReplaceE : (x y : A ) (L1 L2 : List A) -> Maybe (Replace x y L1 L2)
      proveReplaceE x y  L1 [] = None
      proveReplaceE x y  [] L2 = None
      proveReplaceE x y  (l :: ls) (l' :: ls')  with (eq x l) | eq y l' 
      proveReplaceE x y  (.x :: ls) (.y :: ls') | Some Refl | Some Refl with (listeq-semidec eq ls ls')
      ...                                                          | None = proveReplaceTl x y  ls ls' (proveReplaceE x y  ls ls') 
      proveReplaceE x y  (.x :: ls) (.y :: .ls) | Some Refl | Some Refl | Some Refl = Some (rep i0 Refl)
      proveReplaceE x y  (l :: ls) (l' :: ls') | _ | _  = proveReplaceTl x y  ls ls' (proveReplaceE x y  ls ls')
  

    proveReplace : {x y : A} {L1 L2 : List A} -> Maybe (Replace x y L1 L2)
    proveReplace {x} {y} {L1} {L2} = proveReplaceE x y L1 L2

    ∈replace : {y : A} {l : List A} {x : A} (i : x ∈ l) -> y ∈ (replace y i)
    ∈replace i0 = i0
    ∈replace (iS i) = iS (∈replace i)

    double-replace : {l : List A} {x y : A} (i : x ∈ l) 
                   -> Id l (replace x (∈replace{y} i))
    double-replace i0 = Refl
    double-replace (iS{x} i) = Id.substeq (\ l -> x :: l) (double-replace i) 
    
    replace-sym : ∀ {x y l1 l2} -> Replace x y l1 l2 -> Replace y x l2 l1
    replace-sym (rep i Refl) = rep (∈replace i) (Id.sym (double-replace i))
    
    forgetLemma : ∀ { x y} -> Check (Sums.forgetMaybe2 eq x y) -> Id x y
    forgetLemma {x} {y} c with (eq x y)
    ... | Some g = g
    ... | None = Sums.abort c
  
    make-replace : ∀ {x y l1} -> Maybe (Σ \ l2 -> Replace x y l1 l2 )
    make-replace {x} {y} {l1} with find-in (Sums.forgetMaybe2 eq x) l1 
    ... | None = None
    ... | Some index with (forgetLemma (snd (snd index)))
    make-replace {x} {y} {l1} | Some (.x , i , c) | Refl = Some (replace y i , rep i Refl)



  module Subset where
    open In

    _⊆_    : {A : Set} -> List A -> List A -> Set
    _⊆_ {A} f f' = ({a : A} -> a ∈ f -> a ∈ f')
      
    _⊆o_ : {A : Set} {l1 l2 l3 : List A} -> (l2 ⊆ l3) -> (l1 ⊆ l2) -> (l1 ⊆ l3)
    _⊆o_ l23 l12 inl1 = l23 (l12 inl1)
  
    ⊆[] : {A : Set} {l : List A} -> ([] ⊆ l)
    ⊆[] () 
  
    ⊆refl : {A : Set} {l : List A} -> (l ⊆ l)
    ⊆refl inl = inl 
  
    ⊆trans : {A : Set} {l1 l2 l3 : List A} -> (l1 ⊆ l2) -> (l2 ⊆ l3) -> (l1 ⊆ l3)
    ⊆trans s12 s23 in1 = s23 (s12 in1) 

    ⊆append-left : {A : Set} {l : List A} {l' : List A} (ll : List A) -> (l ⊆ l') -> (l ⊆ (ll ++ l'))
    ⊆append-left ll lell' inl = iSmany _ ll (lell' inl)
  
    ⊆append-swap : {A : Set} {l : List A} {l2 : List A} (l1 : List A) -> (l ⊆ (l1 ++ l2)) -> (l ⊆ (l2 ++ l1))
    ⊆append-swap l1 le12 inl = iswapapp _ l1 (le12 inl)
    
    ⊆append-right : {A : Set} {l' : List A} {l : List A} (ll : List A) -> (l ⊆ l') -> (l ⊆ (l' ++ ll))
    ⊆append-right ll sll' = ⊆append-swap ll (⊆append-left ll sll')
  
    ⊆append-cong : {A : Set} {l1 l1' l2 l2' : List A} -> (l1 ⊆ l1') -> (l2 ⊆ l2') -> ((l1 ++ l2) ⊆ (l1' ++ l2'))
    ⊆append-cong {A} {l1} {l1'} {l2} {l2'} s1 s2 inapp 
      with splitappend l1 _ inapp
    ...  | Inl in1 = iswapapp l1' l2' (iSmany l1' l2' (s1 in1))
    ...  | Inr in2 = iSmany l2' l1' (s2 in2)

    ⊆both : {A : Set} {l1 l2 l3 : List A} -> (l1 ⊆ l3) -> (l2 ⊆ l3) -> ((l1 ++ l2) ⊆ l3)
    ⊆both {A} {l1} {l1'} {l3} s1 s2 inapp 
      with splitappend l1 _ inapp
    ...  | Inl in1 = s1 in1  
    ...  | Inr in2 = s2 in2

    ⊆single : {A : Set} {l : List A} {b : A} -> (b ∈ l) -> ([ b ] ⊆ l) 
    ⊆single i i0 = i
    ⊆single _ (iS ())

    ⊆-::-cong : ∀ {A x} {Ω Ω' : List A} -> Ω ⊆ Ω' -> (x :: Ω ⊆ x :: Ω')
    ⊆-::-cong w i0 = i0
    ⊆-::-cong w (iS i) = iS (w i)

    extend⊆ : ∀ {A x} {Ω Ω' : List A} -> Ω ⊆ Ω' -> (x :: Ω ⊆ x :: Ω')
    extend⊆ = ⊆-::-cong

    ⊆insert-middle : {A : Set} {a' : A} (l1 : List A) ( l2 : List A) 
                     -> (l2 ++ l1) ⊆ (l2 ++ (a' :: l1))
    ⊆insert-middle l1 l2 = iS-app-right l1 l2

    ⊆remove : {a : Set} {x : a} {l : List a} -> (i : x ∈ l) -> (remove l i) ⊆ l
    ⊆remove {l = []} () _
    ⊆remove {l = x :: xs} i0 i = (iS i)
    ⊆remove {l = x :: xs} (iS i) (iS i') = iS (⊆remove i i')
    ⊆remove {l = x :: xs} (iS i) i0 = i0

    _≡set_ : {A : Set} -> List A -> List A -> Set
    l ≡set l' = l ⊆ l' × l' ⊆ l

    ≡set-refl : {A : Set} {l : List A} -> (l ≡set l)
    ≡set-refl = ((\ {_} i -> ⊆refl i) , (\ {_} i -> ⊆refl i))

    ≡set-::-cong : {A : Set} {a : A} {l l' : List A} -> l ≡set l' -> (a :: l) ≡set (a :: l')
    ≡set-::-cong {a = a} (l , g) = ((\{a'} i -> ⊆append-cong (⊆refl {_} {a :: []}) l i), 
                                    \{a'} i -> ⊆append-cong (⊆refl {_} {a :: []}) g i )

    ≡set-append-cong : {A : Set} {l1 l1' l2 l2' : List A} -> l1 ≡set l1' -> l2 ≡set l2' -> (l1 ++ l2) ≡set (l1' ++ l2')
    ≡set-append-cong (eq1 , eq1') (eq2 , eq2') = ((\{a'} i -> ⊆append-cong eq1 eq2 i) , 
                                                  (\{a'} i -> ⊆append-cong eq1' eq2' i))

    ⊆Eq : {A : Set} {Ω Ω' : List A} -> (f1 f2 : Ω ⊆ Ω') -> Set
    ⊆Eq {A}{Ω} f1 f2 = {x : A} -> (i : x ∈ Ω) -> Id (f1 i) (f2 i)

    _∘⊆_ : ∀ {A} {Ω1 Ω2 Ω3 : List A} -> (w2 : Ω2 ⊆ Ω3) -> (w1 : Ω1 ⊆ Ω2) -> Ω1 ⊆ Ω3
    g ∘⊆ f = \ x -> g (f x)

    extend⊆-ext : ∀ {A x} {Ω Ω' : List A} -> {w1 w2 : Ω ⊆ Ω'} -> ⊆Eq w1 w2 -> ⊆Eq (extend⊆{_}{x} w1) (extend⊆ w2)
    extend⊆-ext wid i0 = Refl
    extend⊆-ext wid (iS i) = Id.substeq iS (wid i)

    extend⊆-compose : ∀ {A x} {Ω1 Ω2 Ω3 : List A} -> {w2 : Ω2 ⊆ Ω3} {w1 : Ω1 ⊆ Ω2} 
                    -> ⊆Eq (extend⊆{_}{x} (w2 ∘⊆ w1)) ((extend⊆ w2) ∘⊆ (extend⊆ w1))
    extend⊆-compose i0 = Refl
    extend⊆-compose (iS i) = Refl

    ⊆-map : ∀ {A B} {Ψ Ψ' : List A} -> (f : A -> B) -> Ψ ⊆ Ψ' -> (map f Ψ) ⊆ (map f Ψ')
    ⊆-map w lt i with In.in-map2 _ _ i
    ... | (_ , oldx , Refl) = In.in-map (lt oldx)

  module Weakening {A : Set} (P : List A -> Set) where
    open Subset

    Wkn : Set
    Wkn = ∀ {Ω Ω'} -> Ω ⊆ Ω' -> P Ω -> P Ω'
    
    module Properties(wkn : Wkn) where
      Ext : Set
      Ext = ∀ {Ω Ω'} {w1 w2 : Ω ⊆ Ω'} -> ⊆Eq w1 w2 -> (t : P Ω) -> Id (wkn w1 t) (wkn w2 t)

      Compose : Set
      Compose = ∀ {Ω1 Ω2 Ω3} -> (w2 : Ω2 ⊆ Ω3) (w1 : Ω1 ⊆ Ω2) -> (A : P Ω1) -> Id (wkn (\{_} -> w2 ∘⊆ w1) A) (wkn w2 (wkn w1 A))

  module SW where
  
    data Somewhere {A : Set} (P : A -> Set) : List A -> Set where
      s0 : {x : A} {xs : List A} -> P x -> Somewhere P (x :: xs)
      sS : {x : A} {xs : List A} -> Somewhere P xs -> Somewhere P (x :: xs) 

    fromin : {A : Set} {P : A -> Set} {l : List A} {a : A} -> a ∈ l -> P a -> Somewhere P l
    fromin i0 p = s0 p
    fromin (iS i) p = sS (fromin i p)

    toin : {A : Set} {P : A -> Set} {l : List A} -> Somewhere P l -> (Σ \a -> (a ∈ l) × P a)
    toin (s0 p) = _ , i0 , p
    toin (sS sw) with toin sw 
    ...             | _ , i , p = _ , iS i , p

    mapsw : {A : Set} {P : A -> Set} {Q : A -> Set} {l : List A} -> ({a : A} -> P a -> Q a) -> Somewhere P l -> Somewhere Q l
    mapsw f (s0 pf) = s0 (f pf)
    mapsw f (sS s) = sS (mapsw f s)

    here? : {A : Set} {P : A -> Set} {l : List A} {x : A} -> (i : x ∈ l) -> Somewhere P l 
          -> Either (P x) (Somewhere P (In.remove l i))
    here? i sw with toin sw
    ...           | _ , j , p with In.indeq i j
    ...                                   | Inl Refl = Inl p
    ...                                   | Inr pf2 = Inr (fromin pf2 p)

  module EW where
    open In

    -- equivalent characterization of Everywhere based on universal quantification:
    fromall : {A : Set} {P : A -> Set} {l : List A} 
            -> ({a : A} -> a ∈ l -> P a) -> Everywhere P l
    fromall {l = []}      _ = E[]
    fromall {l = x :: xs} f = (f i0) E:: (fromall (\i -> f (iS i)))

    there : {A : Set} {P : A -> Set} {l : List A} -> Everywhere P l -> ({a : A} -> a ∈ l -> P a)
    there E[] ()
    there (_E::_ phere pthere) i0 = phere
    there (_E::_ phere pthere) (iS i) = there pthere i

    -- list-indexed list
    IList : {A : Set} (P : A -> Set) -> List A -> Set
    IList = Everywhere

    appendew : {A : Set} {P :  A -> Set} {l1 l2 : List A} -> Everywhere P l1 -> Everywhere P l2 -> Everywhere P (append l1 l2)
    appendew E[] e = e
    appendew (_E::_ h t) e = _E::_ h (appendew t e)
    
    splitew : {A : Set} {P :  A -> Set} (l1 l2 : List A) -> Everywhere P (append l1 l2) -> Everywhere P l1 × Everywhere P l2
    splitew [] l2 e = E[] , e
    splitew (a :: l1) l2 (_E::_ h t) with splitew l1 l2 t
    ...                              | e1 , e2 = _E::_ h e1 , e2
    
    mapew : {A : Set} {P Q :  A -> Set} {l : List A} -> ({a : A} -> P a -> Q a) -> Everywhere P l -> Everywhere Q l
    mapew f E[] = E[]
    mapew f (_E::_ h t) = _E::_ (f h) (mapew f t)

    -- allows the indices to change
    mapewi : {I1 : Set} {I2 : Set} {El1 : I1 -> Set} {El2 : I2 -> Set} 
         -> (if : I1 -> I2) -> ({i1 : I1} -> El1 i1 -> El2 (if i1)) 
         -> {is1 : List I1} -> IList El1 is1 -> IList El2 (map if is1)
    mapewi _ f E[] = E[]
    mapewi if f (x E:: xs) = f x E:: (mapewi if f xs)

    removeew : {A : Set} {P : A -> Set} {l : List A} {a : A} -> Everywhere P l -> (i : a ∈ l) 
              -> Everywhere P (remove l i)
    removeew E[] ()
    removeew (_E::_ here there) i0 = there
    removeew (_E::_ here there) (iS i) = _E::_ here (removeew there i)

    zipew : {A : Set} {P : A -> Set} {l : List A} -> Everywhere P l -> List (Σ \ a -> P a)
    zipew E[] = []
    zipew (p E:: ew) = (_ , p) :: zipew ew

    data _I∈_ {I : Set} {El : I -> Set} {i : I} (x : El i): {is : List I} -> IList El is -> Set where
      I∈0 : {is : List I} {l : IList El is} -> x I∈ (x E:: l)
      I∈S : {is : List I} {l : IList El is} {i' : I} {y : El i'}
          -> x I∈ l -> x I∈ (y E:: l)

    -- to and from check
    from-checkall : {A : Set} (l : List A) {p : A -> Bool} -> Check (all p l) -> Everywhere (\ x -> Check (p x)) l
    from-checkall [] _ = E[]
    from-checkall (x :: xs) {p} ch = (fst (check-andE{p x} ch)) E:: (from-checkall xs (snd (check-andE{p x} ch)))

    to-checkall : {A : Set} {l : List A} {p : A -> Bool} -> Everywhere (\ x -> Check (p x)) l -> Check (all p l)
    to-checkall E[] = _
    to-checkall (p E:: ps) = check-andI p (to-checkall ps)

    -- Q holds everywhere on an everywhere (= indexed list)
    data IEverywhere {I : Set} {P : I -> Set} (Q : {i : I} -> P i -> Set) : {is : List I} -> Everywhere P is -> Set where
      IE[] : IEverywhere Q E[]
      _IE::_ : {i : I} {x : P i} {is : List I} {xs : Everywhere P is} -> Q x -> IEverywhere Q xs -> IEverywhere Q (x E:: xs)

    infixr 98 _IE::_

    lookupByIn : {I : Set} {El : I -> Set} {is : List I} {i : I} 
                  -> i ∈ is -> (ls : IList El is)
                  -> Σ \(x : El i) -> x I∈ ls
    lookupByIn i0 (x E:: _) = x , I∈0
    lookupByIn (iS i) (x E:: xs) = _ , I∈S (snd (lookupByIn i xs))

    ithere : {I : Set} {El : I -> Set} {is : List I} {i : I} {x : El i} {P : {i : I} -> El i -> Set}
        -> {l : IList El is} -> x I∈ l -> IEverywhere P l -> P x
    ithere I∈0 (p IE:: _) = p
    ithere (I∈S i) (_ IE:: ps) = ithere i ps

    forget : {A : Set} {B : Set} {l : List A} -> Everywhere (\ _ -> B) l -> List B
    forget E[] = []
    forget (x E:: xs) = x :: (forget xs)

    joinEW : {A : Set} {B : A -> Set} {xs : List A}
           -> Everywhere (\ x -> Maybe (B x)) xs
           -> Maybe (Everywhere B xs)
    joinEW E[] = Some E[] 
    joinEW (Some x E:: xs) = mapMaybe (\ xs' -> x E:: xs') (joinEW xs)
    joinEW (None E:: _) = None

    module Properties where
      lookup-of-map : {I : Set} {El1 : I -> Set} {El2 : I -> Set} 
                 (f : ({i1 : I} -> El1 i1 -> El2 i1))
                 -> {is : List I} 
                 -> (xs : Everywhere El1 is)
                 -> {i : I} (ind : i ∈ is)
                 -> Id (fst (lookupByIn ind (mapew f xs))) (f (fst (lookupByIn ind xs)))
      lookup-of-map f E[] ()
      lookup-of-map f (x E:: xs) i0 = Refl
      lookup-of-map f (x E:: xs) (iS i) = lookup-of-map f xs i
  
      fuse-mapew : {I : Set} {El1 : I -> Set} {El2 : I -> Set} {El3 : I -> Set} 
                 (f : ({i1 : I} -> El2 i1 -> El3 i1))
                 (g : ({i1 : I} -> El1 i1 -> El2 i1))
                 -> {is : List I} 
                 -> (xs : Everywhere El1 is)
                 -> Id (mapew f (mapew g xs)) (mapew (\x -> f ( g x)) xs)
      fuse-mapew f g E[] = Refl 
      fuse-mapew f g (x E:: xs) = substeq (\xs -> f (g x) E:: xs) (fuse-mapew f g xs)
  
      -- this will only really be useful when El2 is a positive type
      map-eq : {I : Set} {El1 : I -> Set} {El2 : I -> Set} 
                 (f : ({i1 : I} -> El1 i1 -> El2 i1))
                 (g : ({i1 : I} -> El1 i1 -> El2 i1))
                 -> ((i : I) (x : El1 i) -> Id (f x) (g x))
                 -> {is : List I} 
                 -> (xs : Everywhere El1 is)
                 -> Id (mapew f xs) (mapew g xs)
      map-eq f g eq E[] = Refl 
      map-eq f g eq (x E:: xs) with (f x)  | eq _ x | mapew f xs    | map-eq f g eq xs
      ...                         | .(g x) | Refl   | .(mapew g xs) | Refl = Refl 
  
      map-compose-eq : {I : Set} {El1 : I -> Set} {El2 : I -> Set} {El2' : I -> Set} {El3 : I -> Set} 
                     (f : ({i1 : I} -> El1 i1 -> El2 i1))
                     (f' : ({i1 : I} -> El1 i1 -> El2' i1))
                     (g : ({i1 : I} -> El2 i1 -> El3 i1))
                     (g' : ({i1 : I} -> El2' i1 -> El3 i1))
                     -> ((i : I) (x : El1 i) -> Id (g (f x)) (g' (f' x)))
                     -> {is : List I} 
                     -> (xs : Everywhere El1 is)
                     -> Id (mapew g (mapew f xs)) (mapew g' (mapew f' xs))
      map-compose-eq f f' g g' id xs = Id.trans (Id.trans fuse1 comp) fuse2  where
        fuse1 = fuse-mapew g f xs
        fuse2 = Id.sym (fuse-mapew g' f' xs)
        comp  = map-eq _ _ id xs

      remove-map : {I : Set} {El1 : I -> Set} {El2 : I -> Set} 
                   (f : ({i1 : I} -> El1 i1 -> El2 i1))
                   {is : List I} {i : I} 
                  -> (ind : i ∈ is) -> (xs : Everywhere El1 is)
                  -> Id (removeew (mapew f xs) ind) (mapew f (removeew xs ind))
      remove-map f i0 (x E:: xs) = Refl 
      remove-map f (iS i) (x E:: xs) = substeq (\xs -> f x E:: xs) (remove-map f i xs) 

      map-id : {I : Set} {El1 : I -> Set}  
             -> {is : List I} 
             -> (xs : Everywhere El1 is)
             -> Id (mapew (\x -> x) xs) xs
      map-id E[] = Refl
      map-id (x E:: xs) = Id.substeq (\xs -> x E:: xs) (map-id xs)

  module EW2 where
    open In

    data Everywhere2 {A : Set} (P : A -> A -> Set) : List A -> List A -> Set where
      E2[] : Everywhere2 P [] []
      _E2::_ : forall {x y xs ys} -> P x y -> Everywhere2 P xs ys -> Everywhere2 P (x :: xs) (y :: ys) 

    appendew : {A : Set} {P :  A -> A -> Set} {l1 l2 l1' l2' : List A} -> Everywhere2 P l1 l1' -> Everywhere2 P l2 l2' -> Everywhere2 P (append l1 l2) (append l1' l2')
    appendew E2[] e = e
    appendew (_E2::_ h t) e = _E2::_ h (appendew t e)

    ew-[]-is-[]/left : {A : Set} (P : A -> A -> Set) {l : List A} -> Everywhere2 P [] l -> Id l []
    ew-[]-is-[]/left P {[]} E2[] = Refl
    ew-[]-is-[]/left P {(_ :: _)} ()

  module InLists where
    open SW 

    _∈∈_ : {A : Set} -> A -> Lists A -> Set 
    a ∈∈ ls = Somewhere (\ l -> a ∈ l) ls    

  module Subsets where 
    open In
    open InLists
    open SW
    open Subset

    -- S for Lists
    -- L for List

    _⊆SS_ : {A : Set} -> Lists A -> Lists A -> Set
    _⊆SS_ {A} f f' = ({a : A} -> a ∈∈ f -> a ∈∈ f')
    
    _⊆LS_    : {A : Set} -> List A -> Lists A -> Set
    _⊆LS_ {A} f r = ({a : A} -> a ∈ f -> a ∈∈ r)
    
    shiftwv : {A : Set} { r1 r2 : Lists A } -> r1 ⊆SS r2 -> (l : List A) -> (l :: r1) ⊆SS (l :: r2)
    shiftwv wv new (s0 inl) = s0 inl
    shiftwv wv new (sS inr1) = sS (wv inr1)
    
    ⊆SSlast : {A : Set} {l : List A} {l' : List A} {f : Lists A} -> (l ⊆ l') -> (l :: f) ⊆SS (l' :: f)
    ⊆SSlast inl' (s0 h) = s0 (inl' h) 
    ⊆SSlast inl' (sS i) = sS i
    
    ⊆SSlast-append-left : {A : Set} {l1 : List A} {l2 : List A} {f : Lists A}
                      -> (l2 :: f) ⊆SS ((l1 ++ l2) :: f)
    ⊆SSlast-append-left {_} {l1} {l2} = ⊆SSlast (iSmany l2 l1)
    
    ⊆SSlast-append-right : forall { A l1 l2 f } -> (l1 :: f) ⊆SS ((l1 ++ l2) :: f)
    ⊆SSlast-append-right {A} {l1} {l2} = ⊆SSlast help where
      help : ({a : A} -> a ∈ l1 -> a ∈ append l1 l2)
      help inl1 = iswapapp l1 l2 (iSmany l1 l2 inl1)

    ⊆SSlast-append-left-left : forall { A l0 l1 l2 f } -> ((l1 ++ l0) :: f) ⊆SS (((l2 ++ l1) ++ l0) :: f)
    ⊆SSlast-append-left-left {A} {l0} {l1} {l2} = ⊆SSlast help
      where help : ({a : A} -> a ∈ (l1 ++ l0) -> a ∈ ((l2 ++ l1) ++ l0))
            help i with In.splitappend l1 _ i
            ...       | Inl in1 = iSmany-right _ l0 (iSmany l1 l2 in1)
            ...       | Inr in0 = iSmany l0 (l2 ++ l1) in0

    ⊆SSlast-append-left-right : forall { A l0 l1 l2 f } -> ((l1 ++ l0) :: f) ⊆SS (((l1 ++ l2) ++ l0) :: f)
    ⊆SSlast-append-left-right {A} {l0} {l1} {l2} = ⊆SSlast help
      where help : ({a : A} -> a ∈ (l1 ++ l0) -> a ∈ ((l1 ++ l2) ++ l0))
            help i with In.splitappend l1 _ i
            ...       | Inl in1 = iSmany-right _ l0 (iSmany-right l1 l2 in1)
            ...       | Inr in0 = iSmany l0 (l1 ++ l2) in0
    
    ⊆LSappend : {A : Set} {f1 : List A} {f2 : List A} {r : Lists A} 
                -> f1 ⊆LS r -> f2 ⊆LS r -> (f1 ++ f2) ⊆LS r
    ⊆LSappend {_} {f1} {f2} if1 if2 inapp with splitappend f1 f2 inapp 
    ...                                      | Inl in1 = if1 in1
    ...                                      | Inr in2 = if2 in2 

-- conditional order-preserving embedding
  module CondOPE where
    data Embed {A : Set} (P : A -> Set) : List A -> List A -> Set where
      Done : Embed P [] []
      Keep : forall {a l l'} -> Embed P l l' -> Embed P (a :: l) (a :: l')
      Skip : {a : A} {l l' : List A} 
           -> Embed P l l'  ->   P a
           -> Embed P (a :: l) l'
  
    embedid : forall {A P} (l : List A) -> Embed P l l 
    embedid [] = Done
    embedid (a :: l) = Keep (embedid l)
  
    _comp_ : {A : Set} {P : A -> Set} {l1 l2 l3 : List A} -> Embed P l2 l3 -> Embed P l1 l2 -> Embed P l1 l3
    Done         comp Done = Done
    f            comp (Skip g sub1) = Skip (f comp g) sub1
    (Keep f)     comp (Keep g) = Keep (f comp g)
    (Skip f sub) comp (Keep g) = Skip (f comp g) sub 
  
    embed⊆ : {A : Set} {P : A -> Set} {l l' : List A} -> Embed P l l' -> Subset._⊆_ l' l
    embed⊆ Done ()
    embed⊆ (Keep em) i0 = i0
    embed⊆ (Keep em) (iS i) = iS (embed⊆ em i)
    embed⊆ (Skip em _) i = iS (embed⊆ em i)

    weaken-embed : {A : Set} {P Q : A -> Set} {l1 l2 :  List A} 
                 -> ({a : A} -> P a -> Q a) -> Embed P l1 l2 -> Embed Q l1 l2 
    weaken-embed f Done = Done
    weaken-embed f (Keep e) = Keep (weaken-embed f e)
    weaken-embed f (Skip e pf) = Skip (weaken-embed f e) (f pf) 

    embed∈ : {A : Set} {x : A} {P : A -> Set} {l l' : List A} -> (P x -> Void) -> Embed P l l' -> x ∈ l -> x ∈ l'
    embed∈ e Done ()
    embed∈ e (Keep f) i0 = i0
    embed∈ e (Keep f) (iS g) = iS (embed∈ e f g)
    embed∈ e (Skip f g) i0 = abort (e g)
    embed∈ e (Skip f g) (iS h) = embed∈ e f h


  module Permute where
    -- open In
  
    _∼_ : {A : Set} -> List A -> List A -> Set
    _∼_ {A} f f' = (∀{a} → a ∈ f → a ∈ f') × (∀{a} → a ∈ f' → a ∈ f)

  -- Conditional property preserving embedding
  -- the extension of the bigger state satisfies some predicate
  module CondPPE where
    open Permute    
    open Subset 

    Embed : {A : Set} (P : A -> Set) -> List A -> List A -> Set
    Embed P l l' = (∀{a} → a ∈ l → Either (a ∈ l') (P a)) × 
                   (∀{a} → a ∈ l' → a ∈ l)
                   

    embedid : forall {A P} (l : List A) -> Embed P l l 
    embedid l = (λ x → Inl x) , (λ x → x)
  
    embed⊆ : {A : Set} {P : A -> Set} {l l' : List A} -> Embed P l l' -> l' ⊆ l
    embed⊆ (x , y) = y

    weaken-embed : {A : Set} {P Q : A -> Set} {l1 l2 :  List A} 
                 -> ({a : A} -> P a -> Q a) -> Embed P l1 l2 -> Embed Q l1 l2 
    weaken-embed f (x , y) 
      = (λ x' → case (x x') (λ x0 → Inl x0) (λ x0 → Inr (f x0))) , λ x' → y x'

    embed∈ : {A : Set} {x : A} {P : A -> Set} {l l' : List A} -> (P x -> Void) -> Embed P l l' -> x ∈ l -> x ∈ l'
    embed∈ p e i = case (fst e i) (λ x → x) (λ x → abort (p x))

  -- the difference between the two sets satisfies a predicate
  module CondSet where
    Diff : {A : Set} (P : A -> Set) → List A -> List A -> Set
    Diff {A} P l l' =
      ({x : A} → x ∈ l → Either (P x) (x ∈ l')) × 
      ({x : A} → x ∈ l' → Either (P x) (x ∈ l))

    diffid : ∀ {A P} (l : List A) -> Diff P l l
    diffid l = (λ x' → Inr x') , (λ x' → Inr x')
 
    diffsymm : ∀ {A P} (l l' : List A) -> Diff P l l' -> Diff P l' l
    diffsymm l l' (A , B) = (λ x' → B x') , λ x' → A x'

    wkd-helper : {A : Set} {x : A} (P Q : A -> Set) {l :  List A} 
                 -> ({a : A} -> P a -> Q a) 
                  -> Either (P x) (x ∈ l) -> Either (Q x) (x ∈ l)
    wkd-helper P Q e (Inl y) = Inl (e y)
    wkd-helper P Q e (Inr y) = Inr y

    weaken-diff : {A : Set} {P Q : A -> Set} {l1 l2 :  List A} 
                 -> ({a : A} -> P a -> Q a) -> Diff P l1 l2 -> Diff Q l1 l2 
    weaken-diff {P = P} {Q = Q} e (f , g) = 
      (λ x' → wkd-helper P Q e (f x')) , λ x' → wkd-helper P Q e (g x')

  -- the difference between two lists satisifies a predicate
  module CondDiff where
    data Diff {A : Set} (P : A -> Set) : List A -> List A -> Set where
      Done : Diff P [] []
      Keep : forall {a l l'} -> Diff P l l' -> Diff P (a :: l) (a :: l')
      Skip : {a : A} {l l' : List A} 
           -> Diff P l l'  ->   P a
           -> Diff P (a :: l) l'
      Add : {a : A} {l l' : List A} 
           -> Diff P l l'  ->   P a
           -> Diff P l (a :: l')
  
    drefl : forall {A P} (l : List A) -> Diff P l l 
    drefl [] = Done
    drefl (a :: l) = Keep (drefl l)

    dsym : forall {A P} {l l' : List A} -> Diff P l l' -> Diff P l' l
    dsym Done = Done
    dsym (Keep f) = Keep (dsym f)
    dsym (Skip f p) = Add (dsym f) p
    dsym (Add f p) = Skip (dsym f) p
  
    _dtrans_ : {A : Set} {P : A -> Set} {l1 l2 l3 : List A} -> Diff P l2 l3 -> Diff P l1 l2 -> Diff P l1 l3
    Done         dtrans Done = Done
    f            dtrans (Skip g sub1) = Skip (f dtrans g) sub1
    (Keep f)     dtrans (Keep g) = Keep (f dtrans g)
    (Skip f sub) dtrans (Keep g) = Skip (f dtrans g) sub 
    (Add f pf)   dtrans g = Add (f dtrans g) pf 
    (Keep f)     dtrans (Add g pf) = Add (f dtrans g) pf 
    (Skip f _)   dtrans (Add g _) = f dtrans g

    fromOPE : {A : Set} {P : A -> Set} {l l' : List A} -> CondOPE.Embed P l l' -> Diff P l l'
    fromOPE CondOPE.Done = Done
    fromOPE (CondOPE.Keep f) = Keep (fromOPE f)
    fromOPE (CondOPE.Skip f pf) = Skip (fromOPE f) pf

    weaken-diff : {A : Set} {P Q : A -> Set} {l1 l2 :  List A} 
                 -> ({a : A} -> P a -> Q a) -> Diff P l1 l2 -> Diff Q l1 l2 
    weaken-diff f Done = Done
    weaken-diff f (Keep e) = Keep (weaken-diff f e)
    weaken-diff f (Skip e pf) = Skip (weaken-diff f e) (f pf) 
    weaken-diff f (Add e pf) = Add (weaken-diff f e) (f pf) 

    fromRemove : {A : Set} {P : A -> Set} {l : List A} {a : A} -> (i : a ∈ l) -> P a -> Diff P (In.remove l i) l
    fromRemove {l = []} () pf
    fromRemove {l = x :: xs} i0 pf = Add (drefl xs) pf    
    fromRemove {l = x :: xs} (iS i) pf = Keep (fromRemove i pf)