\ignore{
\begin{code}
open import lib.Prelude hiding ([_])
open import agda5.Agda5 

open import agda5.ML5Valid

module agda5.ML5Valid-Semantics where
\end{code}}

\section{Semantics}

Our semantics explains the meaning of an ML5 program by translation into
HL5.  As discussed above, our translation clarifies the essential
difference between the role that the world plays in the judgements
\ttt{value (A [ w ])} and \ttt{exp (A [ w ])}: a value hypothesis or
conclusion \ttt{value (A [ w ])} is interpreted as a \emph{pure term} of
HL5 type \ttt{(eff A) < w >}, where \ttt{eff A} is a monadic translation
of \ttt{A}.  Thus, the role of the world \ttt{w} is only to describe
where the resources in \ttt{A} may be used and where the computations
must be run.  On the other hand, an expression \ttt{exp (A [ w ])} is
interpreted as a \emph{monadic computation} of type \ttt{(◯ (eff A)) < w
>}, so the world determines both the site at which the effectful
computation must be run and where the resources/computations in \ttt{A}
may be used.

\subsection{Type Translation}

The type translation from ML5 types to HL5 translates ⌘ to HL5 □, adds a ◯
to the codomain of ⇀ (as in any monadic
translation~\citep{moggi91monad}), and is defined compositionally otherwise.  The
ML5 connective \ttt{∀₅} has a value-restriction, so there is no ◯
inserted in its body.  Note that Agda allows datatype constructors to be
overloaded, so we can have both ML5 types and HL5 types in scope at once.

\begin{code}
  eff : Type5 → Type
  eff (A ⇀ B) = eff A  ⊃  ◯(eff B)
  eff (A ∨ B) = eff A ∨ eff B
  eff (∀₅ A) = ∀₅ (λ w → (eff (A w)))
  eff (∃₅ A) = ∃₅ (λ w → eff (A w))
  eff (A at w) = (eff A) at w 
  eff (ref A) = ref (eff A)
  eff (⌘ A) = ∀₅ (λ w → ((eff (A w)) at w))
\end{code}  
\ignore{
\begin{code}
  eff (A ∧ B) = eff A ∧ eff B
  eff ⊤ = ⊤
  eff ⊥ = ⊥
\end{code}}

A simple induction verifies that mobile ML5 types translate to constant
HL5 types:

\begin{code}
  eff-mobile : ∀ {A} → Mobile5 A → Constant (eff A)
\end{code}

\ignore{
\begin{code}
  eff-mobile (mat5{A}{w}) {w1}{w2} = iat{eff A}{w}{w1}{w2}
  eff-mobile (m∧5{A}{B} y y') = i∧ {eff A}{eff B} (eff-mobile y) (eff-mobile y')
  eff-mobile (m∨5{A}{B} y y') = i∨ {eff A}{eff B} (eff-mobile y) (eff-mobile y')
  eff-mobile m⊤5 {w1}{w2} = i⊤{w1}{w2}
  eff-mobile m⊥5 {w1}{w2} = i⊥{w1}{w2}
  eff-mobile (m∀5{A} y) = i∀{\ w -> eff (A w)} \ w → (eff-mobile (y w))
  eff-mobile (m∃5{A} y) = i∃{\ w -> eff (A w)} \ w → (eff-mobile (y w))
  eff-mobile (m⌘5{A}) {w1}{w2} = (i∀{\ w -> eff (A w) at w} \w → iat{eff (A w)}{w}{w1}{w2}) {w1}{w2}
\end{code}}

\subsection{Term translation}

Next, we interpret hypotheses and conclusions.  Values and expressions
are interpreted as described above (note that for \ttt{L = A [ w ]},
\ttt{fst L = A} and \ttt{snd L = w}).  A valid hypothesis is interpreted
as the Agda set \ttt{(w : World) → (interp-hyp (value (A w [ w ])))},
though to appease the termination checker we have to unroll the
definiton of \ttt{interp-hyp}.

\begin{code}
  interp-hyp : Hyp → Set
  interp-hyp (value L) = (eff (fst L)) < (snd L) >
  interp-hyp (valid A) = (w : World) → (eff (A w)) < w >

  interp-conc : Conc → Set
  interp-conc (value L) = interp-hyp (value L) 
  interp-conc (exp L) = (◯ (eff (fst L))) < (snd L) >
\end{code}

Next, we interpret the syntax (Figure~\ref{fig:interp}).  The Agda type
\ttt{Everywhere P xs} represents a list with one element of type \ttt{P
x} for each element \ttt{x} in \ttt{xs}; we use this to represent a
substitution of semantic values for syntactic variables.  The usual
propositional connectives are interpreted in the standard way, by
sequencing evaluation if necessary and then applying the corresponding
Agda introduction or elimination form.  Subexpressions that are under
bound variables are interpreted in an extended context (e.g. \ttt{e} in
\ttt{lam e}).  \ttt{List.EW.there} looks up a de Bruijn index into Γ in
a substitution of type \ttt{Everywhere P Γ}.  

\ttt{sham} is interpreted as an Agda function, which is applied in the
translation of the \ttt{▹v} rule for using valid variables.  There are
no Agda term constructors for \ttt{at}, so the translation simply
proceeds inductively.  The quantifiers are interpreted by supplying the
world arguments in the syntax, rather than by extending the substitution
(recall that the proof terms \ttt{wlam} and \ttt{wunpack} contain Agda
functions).  Recall that the body of \ttt{wlam} is already a value, so
no further evaluation is necessary.

\ttt{val} and \ttt{lete} are interpreted directly as return and bind.
\ttt{get5} is translated as a \ttt{get} in the target, followed by a
coercion by the mobility proof.  \ttt{put e} extends the substitution
with the value of \ttt{e}, applying the mobility proof to the value so
it can be used at any other world.

Agda verifies that the interpretation is type correct and total,
establishing that the interpretation is total and type-preserving.  

\begin{figure}[t]
\begin{code}
  eval : ∀ {Γ L} → Γ ⊢ L → Everywhere interp-hyp Γ → interp-conc L
  ---- usual connectives
  eval (▹ x) σ = (Listm.EW.there σ x)
  eval (lam e) σ = λ x → eval e (x E:: σ)
  eval (app e1 e2) σ =  (eval e1 σ) >>= λ f → (eval e2 σ) >>= λ a → f a 
  eval (inl v) σ = Inl (eval v σ)
  eval (inr v) σ = Inr (eval v σ)
  eval (case e e1 e2) σ = eval e σ >>= docase where
    docase : Either _ _ → _
    docase (Inl x) = eval e1 (x E:: σ)
    docase (Inr y) = eval e2 (y E:: σ)
  ---- ⌘ 
  eval (▹v{w} x Refl) σ =  (Listm.EW.there σ x) w
  eval (sham v) σ =  λ w' → (eval (v w') σ)
  eval (lets e e') σ = eval e σ >>= λ x → eval e' (x E:: σ)
  ---- at
  eval (hold v) σ = eval v σ
  eval (leta e e') σ = eval e σ >>= λ x → eval e' (x E:: σ)
  ---- ∀ and ∃
  eval (wlam v) σ = λ w → eval (v w) σ
  eval (wapp e w) σ = eval e σ >>= λ f → return (f w)
  eval (wpair w v) σ = w , eval v σ
  eval (wunpack e e') σ = eval e σ >>= λ p → eval (e' (fst p)) (snd p E:: σ)
  --- monad operations and world movement
  eval (val v) σ = return (eval v σ)
  eval (lete e1 e2) σ = eval e1 σ >>= λ x → eval e2 (x E:: σ)
  eval (get5{A} e mob) σ =  get (eval e σ) >>= λ v → return (coerce (eff-mobile mob) v) 
  eval (put e mob e') σ = eval e σ >>= λ v → eval e' ((λ w' -> coerce (eff-mobile mob) v) E:: σ)
\end{code}
\ignore{
\begin{code}
  eval (pair v1 v2) σ = eval v1 σ , eval v2 σ
  eval (split e e1) σ = (eval e σ) >>= λ p → eval e1 (snd p E:: fst p E:: σ) 
  eval mt σ = <>
  eval (abort e) σ = (eval e σ) >>= Sums.abort

  evalc : ∀ {L} → [] ⊢ L → interp-conc L
  evalc e = eval e E[]
\end{code}}

\caption{Interpretation of the syntax}
\label{fig:interp}
\smallskip
\hrule
\end{figure}

\ignore{
\begin{code}
  module Test where

    move : ∀ {A w w'} -> Mobile5 A -> (value (A [ w ]) :: []) ⊢ exp (A [ w' ])
    move m = (get5 (val (▹ i0)) m)

    moveSem : ∀ {A w w'} -> Mobile5 A -> (interp-hyp (value (A [ w ]))) -> (interp-conc (exp (A [ w' ])))
    moveSem {A} m v = return (coerce (eff-mobile m) v)

    -- derived forms
    bool : Type5
    bool = ⊤ ∨ ⊤
  
    □ : Type5 → Type5
    □ A = ∀₅ \ w → (⊤ ⇀ A) at w
  
    box : ∀ {A w' Γ} → ((w : World) → (value (⊤ [ w ]) :: Γ) ⊢ exp(A [ w ])) → Γ ⊢ value (□ A [ w' ]) 
    box e = wlam \ w → hold (lam (e w))

    -- motivation for validity; tom's thesis, page 50
    vmconc = exp ((bool ⇀ (□ bool)) [ server ])
    vm : [] ⊢ vmconc
    vm = val (lam (val (box (\ w → get5 (val (▹ (iS i0))) (m∨5 m⊤5 m⊤5)))))

    ivmconc = interp-conc vmconc 
    -- = ◯ server (Either Unit Unit → ◯ server ((w' : World) → Unit → ◯ w' (Either Unit Unit)))
    evm : ivmconc
    evm = eval vm E[]
    -- = return (λ x → return (λ w _ → get (return x) >>= λ v → return (wrap (m∨ m⊤ m⊤) v)))
    -- note: the wrap is a no-op for the ML5 fragment of mobile types

    -- in the embedding, can write it with no communication
    vmdirect : ivmconc
    vmdirect = return \x → return \ w _ → return x

    -- and the shamrock version does?
    vtestconc = exp ((bool ⇀ (⌘ \ _ → bool)) [ server ])
    vtest : [] ⊢ vtestconc
    vtest = val (lam (put ((val (▹ i0))) (m∨5 m⊤5 m⊤5) (val (sham \ _ → (▹v i0 Refl)))))

    ivtestconc = interp-conc vtestconc
    -- = ◯ server (Either Unit Unit → ◯ server ((w' : World) → Either Unit Unit))
    evtest : ivtestconc 
    evtest = eval vtest E[]
    -- = return (λ x → return x >>= λ v → return (λ w' → wrap (m∨ m⊤ m⊤) v))
    -- note that wrap bool v = v
\end{code}}
           
           
           
