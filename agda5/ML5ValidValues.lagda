\begin{code}
open import lib.Prelude hiding ([_])
open import agda5.Agda5 

module agda5.ML5ValidValues where

  data Type5 : Set where
    _⇀_  : Type5 -> Type5 -> Type5
    _∧_  : Type5 -> Type5 -> Type5
    ⊤    : Type5
    _∨_  : Type5 -> Type5 -> Type5
    ⊥    : Type5
    ∀₅   : (World -> Type5) -> Type5
    ∃₅   : (World -> Type5) -> Type5
    _at_ : Type5 -> World -> Type5
    ref  : Type5 -> Type5
    ⌘   : (World -> Type5) -> Type5 

  infix 100 _[_] -- more tightly than ::
  infix 10 _⊢_ -- pretty loose
  infix 101 _⇀_ -- more tightly than [ ] 
  infix 102 _∨_ -- more tightly than [ ] 
  infix 103 _∧_ -- more tightly than [ ] 
  infix 104 _at_ -- more tightly than [ ] 

  data LocType : Set where
    _[_] : Type5 -> World -> LocType
  unLoc : LocType -> Type5 × World
  unLoc (A [ w ]) = A , w

  data Hyp : Set where
    value : LocType -> Hyp
    valid : (World -> Type5) -> Hyp

  data Conc : Set where
    exp  : LocType -> Conc
    valid : (World -> Type5) -> Conc
    value : LocType -> Conc

  Ctx = List Hyp

  data Mobile5 : Type5 -> Set where
    mat5 : ∀ {A w} -> Mobile5 (A at w)
    m⌘5 : ∀ {A} -> Mobile5 (⌘ A)
    -- not in ML5    m⇀  : ∀ {A B} -> Mobile5 A -> Mobile5 B -> Mobile5 (A ⇀ B)
    m∧5  : ∀ {A B} -> Mobile5 A -> Mobile5 B -> Mobile5 (A ∧ B)
    m∨5  : ∀ {A B} -> Mobile5 A -> Mobile5 B -> Mobile5 (A ∨ B)
    m⊤5  : Mobile5 ⊤
    m⊥5  : Mobile5 ⊥
    m∀5  : ∀ {A} -> ((w' : _) -> Mobile5 (A w')) -> Mobile5 (∀₅ A)
    m∃5  : ∀ {A} -> ((w' : _) -> Mobile5 (A w')) -> Mobile5 (∃₅ A)

  mutual
    data _⊢_ (Γ : Ctx) : Conc -> Set where
      -- values
      ▹   : ∀ {L} -> value L ∈ Γ -> Γ ⊢ value L
      vval : ∀ {A w} -> Γ ⊢ valid A -> Γ ⊢ value ((A w) [ w ])
      lam : ∀ {A B w} -> (value (A [ w ]) :: Γ) ⊢ (exp (B [ w ])) -> Γ ⊢ value (A ⇀ B [ w ])
      pair  : ∀ {A B w} -> Γ ⊢ value (A [ w ]) -> Γ ⊢ value (B [ w ]) -> Γ ⊢ value (A ∧ B [ w ])
      mt    : ∀ {w} -> Γ ⊢ value (⊤ [ w ])
      inl  : ∀ {A B w} -> Γ ⊢ value (A [ w ]) -> Γ ⊢ value (A ∨ B [ w ])
      inr  : ∀ {A B w} -> Γ ⊢ value (B [ w ]) -> Γ ⊢ value (A ∨ B [ w ])
      hold  : ∀ {A w w'} -> Γ ⊢ value (A [ w' ]) -> Γ ⊢ value ((A at w') [ w ]) -- non-local
      wlam  : ∀ {A w} -> ((w' : _) -> Γ ⊢ value ((A w') [ w ])) -> Γ ⊢ value (∀₅ A [ w ]) -- gratuitous value restriction?
      wpair   : ∀ {A w} -> (w' : _) -> Γ ⊢ value ((A w') [ w ]) -> Γ ⊢ value ((∃₅ A) [ w ])
      sham  : ∀ {A w} -> Γ ⊢ valid A -> Γ ⊢ value (⌘ A [ w ])

      -- valid values
      ▹valid : ∀ {A} -> valid A ∈ Γ -> Γ ⊢ valid A
      valv   : ∀ {A} -> ((w : World) -> Γ ⊢ value ((A w) [ w ])) -> Γ ⊢ valid A

      -- expressions
      val  : ∀ {L} -> Γ ⊢ value L -> Γ ⊢ exp L
      lete : ∀ {A C w} -> Γ ⊢ exp (A [ w ]) -> (value (A [ w ]) :: Γ ⊢ exp (C [ w ])) -> Γ ⊢ exp (C [ w ])
      get5 : ∀ {A w w'} -> Γ ⊢ exp (A [ w' ]) -> Mobile5 A -> Γ ⊢ exp (A [ w ])
      put  : ∀ {A C w} -> Γ ⊢ exp (A [ w ]) -> Mobile5 A -> (valid (\ _ -> A) :: Γ) ⊢ exp (C [ w ]) -> Γ ⊢ exp (C [ w ])
      _:=5_  : ∀ {A w} -> Γ ⊢ exp ((ref A) [ w ]) -> Γ ⊢ exp (A [ w ]) -> Γ ⊢ exp (⊤ [ w ])
      !5     : ∀ {A w} -> Γ ⊢ exp ((ref A) [ w ]) -> Γ ⊢ exp (A [ w ])
      new5   : ∀ {A w} -> Γ ⊢ exp ((ref A) [ w ])
      app : ∀ {A B w} -> Γ ⊢ exp (A ⇀ B [ w ]) -> Γ ⊢ exp (A [ w ]) -> Γ ⊢ exp (B [ w ])
      wapp  : ∀ {A w} ->  Γ ⊢ exp (∀₅ A [ w ]) -> (w' : World) -> Γ ⊢ exp ((A w') [ w ])
      -- non-local left rules on positive values
      casev  : ∀ {A B L w} -> Γ ⊢ value (A ∨ B [ w ]) -> (value (A [ w ]) :: Γ ⊢ exp L) -> (value (B [ w ]) :: Γ ⊢ exp L) -> Γ ⊢ exp L
      splitv : ∀ {A B C w w'} -> Γ ⊢ value (A ∧ B [ w ]) -> (value (B [ w ]) :: (value (A [ w ])) :: Γ ⊢ exp (C [ w' ])) -> Γ ⊢ exp (C [ w' ])
      abortv : ∀ {C w w'} -> Γ ⊢ value (⊥ [ w ]) -> Γ ⊢ exp (C [ w' ])
      wunpackv : ∀ {A w C w''} -> Γ ⊢ value ((∃₅ A) [ w ]) -> ((w' : _) -> (value ((A w') [ w ]) :: Γ ⊢ exp (C [ w'' ]))) -> Γ ⊢ exp (C [ w'' ])
      letav  : ∀ {A w w' C w''} -> Γ ⊢ value ((A at w') [ w ]) -> (value (A [ w' ]) :: Γ ⊢ exp (C [ w'' ])) -> Γ ⊢ exp (C [ w'' ])
      letsv  : ∀ {A C w w'} -> Γ ⊢ value (⌘ A [ w ]) -> (valid A :: Γ ⊢ exp (C [ w' ])) -> Γ ⊢ exp (C [ w' ])

  -- expression left-rules can be a derived form without communication when the worlds match
{-
  split : ∀ {Γ A B C w} -> Γ ⊢ exp (A ∧ B [ w ]) -> (value (B [ w ]) :: (value (A [ w ])) :: Γ ⊢ exp (C [ w ])) -> Γ ⊢ exp (C [ w ])
  split e e' = lete e (splitv (▹ i0) {! weaken ? e' !})

  case : ∀ {Γ A B C w} -> Γ ⊢ exp (A ∨ B [ w ]) -> (value (A [ w ]) :: Γ ⊢ exp (C [ w ])) -> (value (B [ w ]) :: Γ ⊢ exp (C [ w ])) -> Γ ⊢ exp (C [ w ])
  case = {!!}

  abort : ∀ {Γ C w} -> Γ ⊢ exp (⊥ [ w ]) -> Γ ⊢ exp (C [ w ])
  abort = {!!}
  
  wunpack : ∀ {Γ A w C} -> Γ ⊢ exp ((∃₅ A) [ w ]) -> ((w' : _) -> (value ((A w') [ w ]) :: Γ ⊢ exp (C [ w ]))) -> Γ ⊢ exp (C [ w ])
  wunpack = {!!}
  
  leta  : ∀ {Γ A w w' C} -> Γ ⊢ exp ((A at w') [ w ]) -> (value (A [ w' ]) :: Γ ⊢ exp (C [ w ])) -> Γ ⊢ exp (C [ w ])
  leta = {!!}
  
  lets  : ∀ {Γ A C w} -> Γ ⊢ exp (♣ A [ w ]) -> (valid A :: Γ ⊢ exp (C [ w ])) -> Γ ⊢ exp (C [ w ])
  lets = {!!}

  -- and with communication even when they don't

  lete' : ∀ {Γ A C w w''} -> Γ ⊢ exp (A [ w ]) -> (value (A [ w ]) :: Γ ⊢ exp (C [ w'' ])) -> Γ ⊢ exp (C [ w'' ])
  lete' e e' =  lete (get5 (lete e (val (hold (▹ i0)) )) mat) (letav (▹ i0) {! weaken ? e'!})

  split'' : ∀ {Γ A B C w w''} -> Γ ⊢ exp (A ∧ B [ w ]) -> (value (B [ w ]) :: (value (A [ w ])) :: Γ ⊢ exp (C [ w'' ])) -> Γ ⊢ exp (C [ w'' ])
  split'' e e' = lete' e (splitv (▹ i0) {!weaken ? e'!}) 
-}

  -- derived forms
  bool : Type5
  bool = ⊤ ∨ ⊤

  □ : Type5 -> Type5
  □ A = ∀₅ \ w -> (⊤ ⇀ A) at w

  box : ∀ {A w' Γ} -> ((w : World) -> (value (⊤ [ w ]) :: Γ) ⊢ exp(A [ w ])) -> Γ ⊢ value (□ A [ w' ]) -- FIXME cut the unit assum/
  box e = wlam \ w -> hold (lam (e w))

  module Translate where
  
    eff : Type5 -> Type
    eff (A ⇀ B) = eff A ⊃ ◯ (eff B)
    eff (A ∨ B) = eff A ∨ eff B
    eff (A ∧ B) = eff A ∧ eff B
    eff ⊤ = ⊤
    eff ⊥ = ⊥
    eff (∀₅ A) = ∀₅ \ w -> (eff (A w)) -- no ○ because of the value restriction
    eff (∃₅ A) = ∃₅ \ w -> eff (A w)
    eff (A at w) = (eff A) at w 
    eff (ref A) = ref (eff A)
    eff (⌘ A) = ∀₅ \ w -> ((eff (A w)) at w)

    interp-hyp : Hyp -> Set
    interp-hyp (value L) = (eff (fst (unLoc L))) < (snd (unLoc L)) >
    interp-hyp (valid A) = (w : _) -> (eff (A w)) < w > 

    interp-conc : Conc -> Set
    interp-conc (value L) = interp-hyp (value L) 
    interp-conc (valid A) = interp-hyp (valid A) 
    interp-conc (exp L) = ◯ (eff (fst (unLoc L))) < (snd (unLoc L)) >

    eff-mobile : ∀ {A} -> Mobile5 A -> Constant (eff A)
    eff-mobile (mat5{A}{w}) {w1}{w2} = iat{eff A}{w}{w1}{w2}
    eff-mobile (m∧5{A}{B} y y') = i∧ {eff A}{eff B} (eff-mobile y) (eff-mobile y')
    eff-mobile (m∨5{A}{B} y y') = i∨ {eff A}{eff B} (eff-mobile y) (eff-mobile y')
    eff-mobile m⊤5 {w1}{w2} = i⊤{w1}{w2}
    eff-mobile m⊥5 {w1}{w2} = i⊥{w1}{w2}
    eff-mobile (m∀5{A} y) = i∀{\ w -> eff (A w)} \ w → (eff-mobile (y w))
    eff-mobile (m∃5{A} y) = i∃{\ w -> eff (A w)} \ w → (eff-mobile (y w))
    eff-mobile (m⌘5{A}) {w1}{w2} = (i∀{\ w -> eff (A w) at w} \w → iat{eff (A w)}{w}{w1}{w2}) {w1}{w2}

    eval : ∀ {Γ L} -> Γ ⊢ L -> Everywhere interp-hyp Γ -> interp-conc L
    eval (▹ x) σ = (List.EW.there σ x)
    eval (vval s) σ = (eval s σ) _ 
    eval (lam e) σ = (\ x ->  eval e (x E:: σ) )
    eval (pair v1 v2) σ = eval v1 σ , eval v2 σ
    eval mt σ = <>
    eval (inl v) σ = Inl (eval v σ)
    eval (inr v) σ = Inr (eval v σ)
    eval (hold v) σ = (eval v σ)
    eval (wlam v) σ = (\ w -> eval (v w) σ)
    eval (wpair w v) σ = w , eval v σ
    eval (sham v) σ = \ w' -> (eval v σ) w'
    eval (▹valid x) σ = (List.EW.there σ x)
    eval (valv v) σ = \ w' -> eval (v w') σ
    eval (val v) σ = return (eval v σ)
    eval (lete e1 e2) σ = eval e1 σ >>= \ x -> eval e2 (x E:: σ)
    eval (app e1 e2) σ =  (eval e1 σ) >>= \ f -> eval e2 σ >>= \ a -> f a 
    eval (wapp e w) σ = eval e σ >>= \ f -> return (f w) -- need return because of value restriction
    eval (get5 e mob) σ = get (eval e σ) >>= \ v -> return (coerce (eff-mobile mob) v)
    eval (put e mob e') σ = eval e σ >>= \ v -> eval e' ((\ w' -> coerce (eff-mobile mob) v) E:: σ)
    eval (e1 :=5 e2) σ = eval e1 σ >>= \ r -> eval e2 σ >>= \ v -> r := v
    eval (!5 e) σ = eval e σ >>= !
    eval new5 σ = new
    -- non-local left rules can be run without gets!
    eval (casev v e1 e2) σ = docase (eval v σ) where
      docase : Either _ _ -> _
      docase (Inl x) = eval e1 (x E:: σ)
      docase (Inr y) = eval e2 (y E:: σ)
    eval (splitv v e1) σ = let p = (eval v σ) in eval e1 (snd p E:: fst p E:: σ) 
    eval (abortv v) σ = Sums.abort (eval v σ)
    eval (wunpackv v e') σ = let p = eval v σ in eval (e' (fst p)) (snd p E:: σ)
    eval (letav v e') σ = eval e' (eval v σ E:: σ)
    eval (letsv v e') σ = eval e' (eval v σ E:: σ)

  module SemanticPreserv where
    open Translate

    postulate 
      --FIXME not really true because of intensionality...
      eq-refl : ∀ {A w} (x : A < w >) -> Eq A x x 

  module Test where
    open Translate

    -- motivation for validity; tom's thesis, page 50
    vmconc = exp ((bool ⇀ (□ bool)) [ server ])
    vm : [] ⊢ vmconc
    vm = val (lam (val (box (\ w -> get5 (val (▹ (iS i0))) (m∨5 m⊤5 m⊤5)))))

    ivmconc = interp-conc vmconc 
    -- = ◯ server (Either Unit Unit → ◯ server ((w' : World) → Unit → ◯ w' (Either Unit Unit)))
    evm : ivmconc
    evm = eval vm E[]
    -- = return (λ x → return (λ w _ → get (return x) >>= λ v → return (get* (m∨ m⊤ m⊤) v)))
    -- note: the get* is a no-op for the ML5 fragment of mobile types

    -- in the embedding, can write it with no communication
    vmdirect : ivmconc
    vmdirect = return \x -> return \ w _ -> return x

    -- and the shamrock version does?
    vtestconc = exp ((bool ⇀ (⌘ \ _ -> bool)) [ server ])
    vtest : [] ⊢ vtestconc
    vtest = val (lam (put ((val (▹ i0))) (m∨5 m⊤5 m⊤5) (val (sham (▹valid i0)))))

    ivtestconc = interp-conc vtestconc
    -- = ◯ server (Either Unit Unit → ◯ server ((w' : World) → Either Unit Unit))
    evtest : ivtestconc 
    evtest = eval vtest E[]
    -- = return (λ x → return x >>= λ v → return (λ w' → get* (m∨ m⊤ m⊤) v))
    -- note that get* bool v = v
    
\end{code}