\section{Revised ML5}

In this section, we simplify and generalize the ML5 source language
based on the above semantics.  First, our analysis has shown that
\ttt{Mobile5 A} really means that \ttt{A [ w ]} and \ttt{A [ w' ]} are
equal types for any \ttt{w} and \ttt{w'}.  We can internalize this
principle as a value coercion \ttt{vshift} in
Figure~\ref{fig:ml5-revised}.  This makes it possible to implement some
additional programs without communication.  For example, consider a
function

\noagda \begin{code}
move : ∀ {A w w'} → Mobile5 A → (value (A [ w ]) :: []) ⊢ exp (A [ w' ])
move m =  (get5 (val (▹ i0)) m)
\end{code}
%
Operationally, this is quite inefficient: it sends the value of the
variable from \ttt{w'} to \ttt{w}, as the environment of the \ttt{val (▹
i0)} closure, and \ttt{w} then returns this value back to \ttt{w'}.
This whole process is unnecessary, as the value was available at
\ttt{w'} to begin with!  However, it does not seem possible to implement
this function without communication in ML5.
In our revised ML5, as in HL5, it can be implemented as a simple type
coercion:

\noagda \begin{code}
move : ∀ {A w w'} → Mobile5 A → (value (A [ w ]) :: []) ⊢ exp (A [ w' ])
move m = val (vshift (▹ i0) m)
\end{code}

Second, in HL5, the worlding of values always "gets out of the way"
because it commutes with type constructors down to \ttt{ref} and
\ttt{◯}.  In Figure~\ref{fig:ml5-revised}, we add these non-local
elimination rules for values of each connective to the source.  For
example, we add the untethered case rule for values of sum type and a
projective elimination rule for \ttt{at} and ∀₅ values.  

We could additionally add elimination rules like \ttt{case},
\ttt{split}, etc. to the syntactic class of "values"---i.e. we could
admit that we are really dealing with a syntactic class of pure terms:
\noagda \begin{code}
 casev/val : ∀ {A B C w' w} → Γ ⊢ value (A ∨ B [ w ])  
   → (Γ ,, value (A [ w ]) ⊢ val (C [ w' ])) → (Γ ,, value (B [ w ]) ⊢ val (C [ w' ])) 
   → Γ ⊢ val (C [ w' ])
\end{code}
%
However, in an operational semantics where worlds and types are erased
at run-time, \ttt{wappv} and \ttt{unatv} will not create any real
redexes at run-time, whereas \ttt{casev/val} will.  Thus a reasonable
design choice for ML5 would be to allow \ttt{wappv} and \ttt{unatv} but
not the corresponding \ttt{case} rule.

\begin{figure}[t]
\ignore{
\begin{code}
open import lib.Prelude hiding ([_])
open import agda5.Agda5 

module agda5.ML5Revised where

  data Type5 : Set where
    _∧_ _⊃_ _∨_  : Type5 → Type5 → Type5
    ⊤ ⊥  : Type5
    ∀₅ ∃₅ : (World → Type5) → Type5
    _at_ : Type5 → World → Type5
    ref  : Type5 → Type5

  infix 100 _[_] -- more tightly than ::
  infix 10 _⊢_ -- pretty loose
  infix 101 _⊃_ -- more tightly than [ ] 
  infix 102 _∨_ -- more tightly than [ ] 
  infix 103 _∧_ -- more tightly than [ ] 
  infix 104 _at_ -- more tightly than [ ] 

  data Mobile5 : Type5 → Set where
    mat5 : ∀ {A w} → Mobile5 (A at w)
    ---- no rule for ⊃ in ML5
    m∧5  : ∀ {A B} → Mobile5 A → Mobile5 B → Mobile5 (A ∧ B)
    m∨5  : ∀ {A B} → Mobile5 A → Mobile5 B → Mobile5 (A ∨ B)
    m⊤5  : Mobile5 ⊤
    m⊥5  : Mobile5 ⊥
    m∀5  : ∀ {A} → ((w' : _) → Mobile5 (A w')) → Mobile5 (∀₅ A)
    m∃5  : ∀ {A} → ((w' : _) → Mobile5 (A w')) → Mobile5 (∃₅ A)

  LocType : Set 
  LocType = Type5 × World

  _[_] : Type5 → World → LocType
  _[_] = _,_ 

  data Hyp : Set where
    value : LocType → Hyp

  data Conc : Set where
    exp  : LocType → Conc
    value : LocType → Conc

  Ctx = List Hyp
  _,,_ : ∀ {A} → List A → A → List A
  Γ ,, A = A :: Γ
  infixl 10 _,,_

  data _⊢_ (Γ : Ctx) : Conc → Set where

    ---- values
    ▹ : ∀ {A w} 
     → value (A [ w ]) ∈ Γ 
     → Γ ⊢ value (A [ w ])

    lam : ∀ {A B w} 
     → (Γ ,, value (A [ w ])) ⊢ exp (B [ w ])
     → Γ ⊢ value (A ⊃ B [ w ])

    pair : ∀ {A B w} 
     → Γ ⊢ value (A [ w ])
     → Γ ⊢ value (B [ w ]) 
     → Γ ⊢ value (A ∧ B [ w ])

    mt : ∀ {w} 
     → Γ ⊢ value (⊤ [ w ])

    inl : ∀ {A B w} 
     → Γ ⊢ value (A [ w ])
     → Γ ⊢ value (A ∨ B [ w ])

    inr : ∀ {A B w} 
     → Γ ⊢ value (B [ w ])
     → Γ ⊢ value (A ∨ B [ w ])

    hold : ∀ {A w w'}
     → Γ ⊢ value (A [ w' ])
     → Γ ⊢ value ((A at w') [ w ])

    wlam : ∀ {A w}
     → ( (w' : _) → Γ ⊢ value ((A w') [ w ]) )
     → Γ ⊢ value (∀₅ A [ w ]) 

    wpair : ∀ {A w} 
     → (w' : World) 
     → Γ ⊢ value ((A w') [ w ]) 
     → Γ ⊢ value ((∃₅ A) [ w ])
\end{code}}
\noindent New value rules:
\begin{code}
    vshift : ∀ {A w w'} → Γ ⊢ value (A [ w ]) →  Mobile5 A → Γ ⊢ value (A [ w' ])
    wappv : ∀ {A w} → Γ ⊢ value (∀₅ A [ w ])  →  (w' : World) → Γ ⊢ value ((A w') [ w ])
    unatv : ∀ {A w w'} → Γ ⊢ value ((A at w') [ w ]) → Γ ⊢ value (A [ w' ])
\end{code}
\ignore{
\begin{code}
    ----- expressions

    val : ∀ {L} 
     → Γ ⊢ value L 
     → Γ ⊢ exp L

    lete : ∀ {A C w} 
     → Γ ⊢ exp (A [ w ]) 
     → (Γ ,, value (A [ w ])) ⊢ exp (C [ w ])
     → Γ ⊢ exp (C [ w ])

    -- or just make it admissible?
    letv : ∀ {L J} 
     → Γ ⊢ value L
     → (value L :: Γ) ⊢ J
     → Γ ⊢ J 

    get5 : ∀ {A w w'} 
      → Γ ⊢ exp (A [ w' ])  →  Mobile5 A 
      → Γ ⊢ exp (A [ w ])

    app : ∀ {A B w} 
      → Γ ⊢ exp (A ⊃ B [ w ])  →  Γ ⊢ exp (A [ w ])
      → Γ ⊢ exp (B [ w ])

    splitv : ∀ {A B L w} → Γ ⊢ value (A ∧ B [ w ]) 
      → Γ ,, value (A [ w ]) ,, value (B [ w ]) ⊢ exp L → Γ ⊢ exp L

    abortv : ∀ {w L} → Γ ⊢ value (⊥ [ w ]) → Γ ⊢ exp L
\end{code}}
\noindent New expression rules:
\begin{code}
    casev : ∀ {A B L w} → Γ ⊢ value (A ∨ B [ w ])  
      → (Γ ,, value (A [ w ]) ⊢ exp L) → (Γ ,, value (B [ w ])  ⊢ exp L) 
      → Γ ⊢ exp L
    wunpackv : ∀ {A w L} → Γ ⊢ value ((∃₅ A) [ w ]) 
             → ((w' : _) → Γ ,, value ((A w') [ w ]) ⊢ exp L) → Γ ⊢ exp L
\end{code}

Remove rules \ttt{put}, \ttt{▹v}, \ttt{lets}, \ttt{sham}, \ttt{wapp},
\ttt{leta}, \ttt{case}, \ttt{wunpack}.
\caption{Revised ML5}
\label{fig:ml5-revised}
\smallskip
\hrule
\end{figure}
\ignore{
\begin{code}
  module Semantics where

    eff : Type5 → Type
    eff (A ⊃ B) = eff A ⊃ ◯(eff B)
    eff (A ∨ B) = eff A ∨ eff B
    eff (A ∧ B) = eff A ∧ eff B
    eff ⊤ = ⊤
    eff ⊥ = ⊥
    eff (∀₅ A) = ∀₅ \ w → (eff (A w)) -- no ◯ because of the value restriction
    eff (∃₅ A) = ∃₅ \ w → eff (A w)
    eff (A at w) = (eff A) at w 
    eff (ref A) = ref (eff A)
  
    eff-mobile : ∀ {A} → Mobile5 A → Constant (eff A)
    eff-mobile (mat5{A}{w}) {w1}{w2} = iat{eff A}{w}{w1}{w2}
    eff-mobile (m∧5{A}{B} y y') = i∧ {eff A}{eff B} (eff-mobile y) (eff-mobile y')
    eff-mobile (m∨5{A}{B} y y') = i∨ {eff A}{eff B} (eff-mobile y) (eff-mobile y')
    eff-mobile m⊤5 {w1}{w2} = i⊤{w1}{w2}
    eff-mobile m⊥5 {w1}{w2} = i⊥{w1}{w2}
    eff-mobile (m∀5{A} y) = i∀{\ w -> eff (A w)} \ w → (eff-mobile (y w))
    eff-mobile (m∃5{A} y) = i∃{\ w -> eff (A w)} \ w → (eff-mobile (y w))
  
    interp-hyp : Hyp → Set
    interp-hyp (value L) = (eff (fst L)) < (snd L) >
  
    interp-conc : Conc → Set
    interp-conc (value L) = interp-hyp (value L) 
    interp-conc (exp L) = ◯ (eff (fst L)) < (snd L) >

    eval : ∀ {Γ L} → Γ ⊢ L → Everywhere interp-hyp Γ → interp-conc L
    eval (▹ x) σ = (List.EW.there σ x)
    eval (lam e) σ = (\ x →  eval e (x E:: σ) )
    eval (pair v1 v2) σ = eval v1 σ , eval v2 σ
    eval mt σ = <>
    eval (inl v) σ = Inl (eval v σ)
    eval (inr v) σ = Inr (eval v σ)
    eval (hold v) σ = (eval v σ)
    eval (wlam v) σ = (\ w → eval (v w) σ)
    eval (wpair w v) σ = w , eval v σ
    eval (val v) σ = return (eval v σ)
    eval (letv v e) σ = eval e (eval v σ E:: σ)
    eval (lete e1 e2) σ = eval e1 σ >>= \ x → eval e2 (x E:: σ)
    eval (app e1 e2) σ =  (eval e1 σ) >>= \ f → eval e2 σ >>= \ a → f a 
    eval (get5 e mob) σ = get (eval e σ) >>= \ v → return (coerce (eff-mobile mob) v)
    -- non-local left rules can be run without gets!
    eval (splitv v e1) σ = let p = (eval v σ) in eval e1 (snd p E:: fst p E:: σ) 
    eval (abortv v) σ = Sums.abort (eval v σ)
\end{code}}

It is simple to extend the semantics to these new constructs, as they
were derived from it:

\begin{code}
    eval (vshift e m) σ = coerce (eff-mobile m) (eval e σ)
    eval (wappv e w') σ = eval e σ w'
    eval (unatv e ) σ = eval e σ
    eval (casev v e1 e2) σ = docase (eval v σ) where
      docase : Either _ _ → _
      docase (Inl x) = eval e1 (x E:: σ)
      docase (Inr y) = eval e2 (y E:: σ)
    eval (wunpackv v e') σ = let p = eval v σ in eval (e' (fst p)) (snd p E:: σ)
\end{code}

\ignore{\begin{code}
    evalc : ∀ {L} → [] ⊢ L → interp-conc L
    evalc e = eval e E[] 
\end{code}}

\paragraph{Derived Forms}

Once we have added the aforementioned rules, we can remove rules
\ttt{put}, \ttt{▹v}, \ttt{lets}, \ttt{sham}, \ttt{wapp}, \ttt{leta},
\ttt{case}, \ttt{wunpack}, which become derivable.  Shamrock is defined
using \ttt{∀₅} and \ttt{at} in the straightforward way: \ttt{⌘ A = ∀₅ (λ
w → A w at w)}. Validity is defined as a value assumption of shamrock
type: \ttt{valid A = value ((⌘ A) [ dummy ])}, where \ttt{dummy} is any
arbitrary world---\ttt{⌘ A} is mobile, and therefore constant,
but because all value assumptions are worlded, we must pick one.

\ignore{
\begin{code}
  module Derived where
   open List.Subset 

   postulate
     weaken : ∀ {Γ Γ' J} → Γ ⊆ Γ' → Γ ⊢ J → Γ' ⊢ J

   dummy : World
   dummy = client

   ⌘ : (World → Type5) → Type5
   ⌘ A = ∀₅ (\ w → A w at w)
 
   valid : (World → Type5) → Hyp
   valid A = value ((⌘ A) [ dummy ])
\end{code}}

The term \ttt{▹v}, which represents a use of a valid hypothesis, is
derived by eliminating a shamrock.  The term \ttt{put} is derived by
introducing a shamrock, using \ttt{vshift} to retype the assumption in
the body---we use \ttt{letv} to refer to the substitution principle
plugging a value in for a variable, and we use \ttt{weaken} for
weakening in the de Bruijn syntax.

\begin{code} 
   ▹v : ∀ {Γ A C w} → valid A ∈ Γ  →  Id C (A w) → Γ ⊢ value (C [ w ])
   ▹v i Refl = unatv (wappv (▹ i) _)
   
   put : ∀ {Γ A C w} → Γ ⊢ exp (A [ w ])  →  Mobile5 A 
       → (Γ ,, valid (\ _ → A)) ⊢ exp (C [ w ]) → Γ ⊢ exp (C [ w ])
   put e m e' = lete e (letv (wlam (\ w' → hold (vshift (▹ i0) m))) (weaken (extend⊆ iS) e'))
 \end{code}
%
The remaining derivabilities show that the old rules for the
connectives are derivable using the generalized ones.

\ignore{
\begin{code}  
   lets : ∀ {Γ A w C} 
     → Γ ⊢ exp (⌘ A [ w ])
     → (Γ ,, valid A ⊢ exp (C [ w ]))
     → Γ ⊢ exp (C [ w ])
   lets e1 e2 = lete e1 (letv (vshift (▹ i0) (m∀5 (\ _ → mat5))) (weaken (extend⊆ iS) e2))
 
   sham : ∀ {Γ A w'} 
    → ((w : _) → Γ ⊢ value (A w [ w ])) 
    → Γ ⊢ value (⌘ A [ w' ])
   sham v = wlam (\w' → hold (v w'))

   move : ∀ {Γ A wirr2} → (Γ ,, valid A) ⊢ value (∀₅ (\ w → (A w) at w) [ wirr2 ])
   move = wlam (\ w → hold (▹v i0 Refl))
 
   wapp : ∀ {Γ A w} 
    → Γ ⊢ exp (∀₅ A [ w ])  →  (w' : World) 
    → Γ ⊢ exp ((A w') [ w ])
   wapp e1 w' = lete e1 (val (wappv (▹ i0) w'))

   leta : ∀ {Γ A w w' C} 
     → Γ ⊢ exp ((A at w') [ w ])  
     → (Γ ,, value (A [ w' ]) ⊢ exp (C [ w ]))
     → Γ ⊢ exp (C [ w ])
   leta e1 e2 = lete e1 (letv (unatv (▹ i0)) (weaken (List.Subset.extend⊆ iS) e2))

   -- expression left-rules can be a derived form without communication when the worlds match
 
   split : ∀ {Γ A B C w} → Γ ⊢ exp (A ∧ B [ w ]) → (value (B [ w ]) :: (value (A [ w ])) :: Γ ⊢ exp (C [ w ])) → Γ ⊢ exp (C [ w ])
   split e e' = lete e (splitv (▹ i0) ( weaken (extend⊆ (extend⊆ iS)) e' ))
 
   case : ∀ {Γ A B C w} → Γ ⊢ exp (A ∨ B [ w ]) → (value (A [ w ]) :: Γ ⊢ exp (C [ w ])) → (value (B [ w ]) :: Γ ⊢ exp (C [ w ])) → Γ ⊢ exp (C [ w ])
   case e e1 e2 = lete e (casev (▹ i0) (weaken (extend⊆ iS) e1) (weaken ((extend⊆ iS)) e2)) 
 
   abort : ∀ {Γ C w} → Γ ⊢ exp (⊥ [ w ]) → Γ ⊢ exp (C [ w ])
   abort e = lete e (abortv (▹ i0))
   
   wunpack : ∀ {Γ A w C} → Γ ⊢ exp ((∃₅ A) [ w ]) → ((w' : _) → (value ((A w') [ w ]) :: Γ ⊢ exp (C [ w ]))) → Γ ⊢ exp (C [ w ])
   wunpack e e' = lete e (wunpackv (▹ i0) (\ w' → (weaken (extend⊆ iS) (e' w')))) 
   
   -- and with communication even when they don't
 
   lete' : ∀ {Γ A C w w''} → Γ ⊢ exp (A [ w ]) → (value (A [ w ]) :: Γ ⊢ exp (C [ w'' ])) → Γ ⊢ exp (C [ w'' ])
   lete' e e' =  lete (get5 (lete e (val (hold (▹ i0)) )) mat5) (letv (unatv (▹ i0)) (weaken (extend⊆ iS) e'))
 
   split'' : ∀ {Γ A B C w w''} → Γ ⊢ exp (A ∧ B [ w ]) → (value (B [ w ]) :: (value (A [ w ])) :: Γ ⊢ exp (C [ w'' ])) → Γ ⊢ exp (C [ w'' ])
   split'' e e' = lete' e (splitv (▹ i0) (weaken (extend⊆ (extend⊆ iS)) e')) 

   move-revised : ∀ {A w w'} → Mobile5 A → (value (A [ w ]) :: []) ⊢ exp (A [ w' ])
   move-revised m = val (vshift (▹ i0) m)
\end{code}}


