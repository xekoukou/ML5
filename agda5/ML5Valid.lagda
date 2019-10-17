\ignore{
\begin{code}
open import lib.Prelude hiding ([_])
open import agda5.Agda5 

module agda5.ML5Valid where
\end{code}}

\section{ML5}

In this section, we give inductive definitions of the syntactic
apparatus of ML5: First, we define the syntax of types.  Next, we
represent programs using an \emph{intrinsic encoding}, which represents
only well-typed syntax (i.e. typing derivations or natural deduction
proofs).  Variables are represented as well-scoped de Bruijn
indices---pointers into a typing context, which is an explicit parameter
to the typing judgements.  The static semantics requires an auxiliary
definition of a \emph{mobility} judgement on types, which is defined
below.

\subsection{Types}

\begin{code}
  data Type5 : Set where
    _⇀_ _∨_  : Type5 → Type5 → Type5
    ∀₅ ∃₅ : (World → Type5) → Type5
    _at_ : Type5 → World → Type5
    ref  : Type5 → Type5
    ⌘   : (World → Type5) → Type5 
\end{code}
%
\ignore{
\begin{code}
    _∧_ : Type5 → Type5 → Type5
    ⊤ ⊥  : Type5
\end{code}}
%
The type \cd{⇀} represents partial functions, and the type \cd{∨}
represents sums.  The types \ttt{∀₅} \cd{∃₅} cd{at} and \cd{ref} are the
same as in HL5.  There is an additional type constructor "shamrock",
rendered here as ⌘, which a □-like modality, but its rules in the ML5
proof theory are subtly different than the rules for \ttt{∀₅ (λ w → A at
w)}.

We represent types with free world variables as Agda functions from
worlds to types.  This is permissible because \ttt{World} is defined
prior to type (i.e. we are using Weak HOAS\cite{despeyroux+95hoascoq}).
If \ttt{World} is chosen to be a base type in Agda, then it adequately
represents ML5 types as in \citet{murphy08thesis}.  If instead
\ttt{World} is chosen to be an inductive type, this representation
yields a language with type-level case analysis over worlds---i.e. one
could define types whose structure varies depending on their world, such
as \ttt{∃₅ (λ w → if w = server then nat else bool)}; we leave an
exploration of the practical uses of this alternative to future work.

\ignore{
\begin{code}
  infix 100 _[_] -- more tightly than ::
  infix 10 _⊢_ -- pretty loose
  infix 101 _⇀_ -- more tightly than [ ] 
  infix 102 _∨_ -- more tightly than [ ] 
  infix 103 _∧_ -- more tightly than [ ] 
  infix 104 _at_ -- more tightly than [ ] 
\end{code}}

\subsection{Mobility}

ML5's notion of mobility identifies constant functions, analogously to
the \ttt{Constant} relation on HL5 types above.

\begin{code}
  data Mobile5 : Type5 → Set where
    mat5 : ∀ {A w} → Mobile5 (A at w)
    m⌘5 : ∀ {A} → Mobile5 (⌘ A)
    ---- no rule for ⇀ or refs 
    m∨5  : ∀ {A B} → Mobile5 A → Mobile5 B → Mobile5 (A ∨ B)
    m∀5  : ∀ {A} → ((w' : _) → Mobile5 (A w')) → Mobile5 (∀₅ A)
    m∃5  : ∀ {A} → ((w' : _) → Mobile5 (A w')) → Mobile5 (∃₅ A)
\end{code}
\ignore{
\begin{code}
    m∧5  : ∀ {A B} → Mobile5 A → Mobile5 B → Mobile5 (A ∧ B)
    m⊤5  : Mobile5 ⊤
    m⊥5  : Mobile5 ⊥
\end{code}}
%
To foreshadow the interpretation: ⌘ is always mobile, essentially
because ∀₅ (λ w → (A w) at w) is constant.  Functions are never mobile,
because they hide a ◯ in their domain, and ◯ is not constant.

\subsection{Typing judgements}

ML5 judgements have the form 
\cd{Γ ⊢ e : A [ w ]} and 
\cd{Γ ⊢ v :: A [ w ]}.
These judgements mean that the expression \ttt{e} and the value \ttt{v}
are well-formed with modal type \ttt{A} at world \ttt{w}.
Here Γ contains assumptions \ttt{x:A[w]} and \ttt{u $\sim$ w.A}.  
The former, a \emph{value hypothesis}, means that \ttt{x} stands for a
value of type \ttt{A} at world \ttt{w}.  The latter, a \emph{valid
hypothesis}, means that \ttt{u} stands for a value of type \ttt{A} that
makes sense at all worlds (\ttt{w} is bound in \ttt{A}).  
In the operational semantics, we will substitute a proof of the judgement
\ttt{w:world ⊢ v :: (A w)[ w ]} for a valid variable.  

We combine both of the above judgements into one Agda type, defining a
relation \ttt{Γ ⊢ γ}.  Here Γ is a list of hypotheses, which are either
\ttt{value (A [ w ])} or \ttt{valid (w.A)} and γ is a conclusion, which
is either \ttt{exp (A [ w ])} (for expressions) or \ttt{value (A [ w ])}
(for values).  As in the syntax of types, \ttt{w.A} is represented by an
Agda function from worlds to types.

We define the notation \ttt{A [ w ]} to mean the pair of \ttt{A} and
\ttt{w}, and we define sum types for hypotheses and conclusions as
follows:

\ignore{
\begin{code}
  LocType : Set 
  LocType = Type5 × World

  _[_] : Type5 → World → LocType
  _[_] = _,_ 
\end{code}}

\begin{code}
  data Hyp : Set where
    value : (Type5 × World) → Hyp
    valid : (World → Type5) → Hyp

  data Conc : Set where
    exp  : (Type5 × World) → Conc
    value : (Type5 × World) → Conc

  Ctx = List Hyp
\end{code}

Term variables \ttt{x} and \ttt{u} are represented by
well-scoped de Bruijn indices---pointers into Γ:

\noagda \begin{verbatim}
data _∈_ {A : Set} : A → List A → Set where
 i0 : {α : A}   {Γ : List A} → α ∈ (α :: Γ)
 iS : {α α' : A} {Γ : List A} → α ∈ Γ → α ∈ (α' :: Γ)
\end{verbatim}

The typing rules are defined in Figure~\ref{fig:ml5-typing}.  The first
rule says that \ttt{(▹ x)} is a value if \ttt{x} is a de Bruijn index
for a value assumption in Γ.  The next rule represents the application
of a valid assumption in Γ to a world \ttt{w}; we use propositional
equality \ttt{Id} to state that the conclusion type is \ttt{A w} because
otherwise the higher-order conclusion blocks pattern-matching.
\ttt{lam} takes an expression in an extended context to a value of
function type; this rule expresses the idea that a function of type
\ttt{A ⇀ B} in a world \ttt{w} is an expression of type \ttt{B} at
\ttt{w}, hypothetically in a variable standing for a value of type
\ttt{A} at \ttt{w}.  Sums are introduced by commuting the world with the
connective.  \ttt{hold} switches worlds to introduce an \ttt{at};
\ttt{wlam} and \ttt{wpair} introduce quantifiers in the usual way; the
world in the conclusion does not change (also, note the parentheses,
which in Agda's notation for datatype constructors are the only
difference between the two rules: the premise of \ttt{wlam} is a
function, whereas \ttt{wpair} has two premises).  However, note that the
body of a \ttt{wlam} is a value, not an expression---ML5 has a value
restriction on world quantification, to support type inference in the
style of ML.  \ttt{sham} both quantifies over a new world and switches
the world of the conclusion---indeed, this is the derived intro rule
that one would expect for \ttt{⌘ A = ∀₅ (λ w → (A w) at w)}.

\ttt{val} injects values into expressions, whereas \ttt{let} sequences
the evaluation of two expressions.  \ttt{put} runs an expression of
mobile type and then binds the resulting value as a valid assumption.
\ttt{app} and \ttt{wapp} eliminate functions and universals, with the
world along for the ride.  The remaining rules are
pattern-matching-style elimination rules. In these rules, the world in
the conclusion \ttt{C [ w ]} is \emph{tethered} to the world in the
principal premise, as discussed in the introduction.

This system is the ML5 internal language described in Section 4.3 of
\citep{murphy08thesis} with one minor change: we have eliminated the
syntactic class of valid values, which allowed validity to appear as a
conclusion as well as as a hypothesis---valid values are unnecessary
because validity is invertible on the right.  An alternate formalization
with valid values is included in the companion code.

\begin{figure}
\begin{footnotesize}
\begin{multicols}{2}
\ignore{
\begin{code}
  _,,_ : ∀ {A} → List A → A → List A
  Γ ,, A = A :: Γ
  infixl 11 _,,_
\end{code}}
\begin{code}
  data _⊢_ (Γ : Ctx) : Conc → Set where

    ---- values
    ▹ : ∀ {A w} 
     → value (A [ w ]) ∈ Γ 
     → Γ ⊢ value (A [ w ])

    ▹v : ∀ {w A C} 
     → valid A ∈ Γ  →  Id C (A w) 
     → Γ ⊢ value (C [ w ])

    lam : ∀ {A B w} 
     → (Γ ,, value (A [ w ])) ⊢ exp (B [ w ])
     → Γ ⊢ value (A ⇀ B [ w ])
\end{code}
\ignore{
\begin{code}
    pair : ∀ {A B w} 
     → Γ ⊢ value (A [ w ])
     → Γ ⊢ value (B [ w ]) 
     → Γ ⊢ value (A ∧ B [ w ])

    mt : ∀ {w} 
     → Γ ⊢ value (⊤ [ w ])
\end{code}}
\begin{code}
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

    sham : ∀ {A w'} 
     → ((w : _) → Γ ⊢ value (A w [ w ])) 
     → Γ ⊢ value (⌘ A [ w' ])

    ----- expressions

    val : ∀ {L} 
     → Γ ⊢ value L 
     → Γ ⊢ exp L

    lete : ∀ {A C w} 
     → Γ ⊢ exp (A [ w ]) 
     → (Γ ,, value (A [ w ])) ⊢ exp (C [ w ])
     → Γ ⊢ exp (C [ w ])

    get5 : ∀ {A w w'} 
      → Γ ⊢ exp (A [ w' ])  →  Mobile5 A 
      → Γ ⊢ exp (A [ w ])

    put : ∀ {A C w} 
      → Γ ⊢ exp (A [ w ])  →  Mobile5 A 
      → (Γ ,, valid (\ _ → A)) ⊢ exp (C [ w ])
      → Γ ⊢ exp (C [ w ])

    app : ∀ {A B w} 
      → Γ ⊢ exp (A ⇀ B [ w ])  →  Γ ⊢ exp (A [ w ])
      → Γ ⊢ exp (B [ w ])

    wapp : ∀ {A w} 
      → Γ ⊢ exp (∀₅ A [ w ])  →  (w' : World) 
      → Γ ⊢ exp ((A w') [ w ])

    case : ∀ {A B C w} 
      → Γ ⊢ exp (A ∨ B [ w ])  
      → (Γ ,, value (A [ w ]) ⊢ exp (C [ w ])) 
      → (Γ ,, value (B [ w ])  ⊢ exp (C [ w ])) 
      → Γ ⊢ exp (C [ w ])
\end{code}
\ignore{
\begin{code}
    split : ∀ {A B C w} 
      → Γ ⊢ exp (A ∧ B [ w ]) 
      → Γ ,, value (A [ w ]) ,, value (B [ w ]) 
          ⊢ exp (C [ w ])
      → Γ ⊢ exp (C [ w ])

    abort : ∀ {w C} 
      → Γ ⊢ exp (⊥ [ w ])
      → Γ ⊢ exp (C [ w ])
\end{code}}
\begin{code}
    wunpack : ∀ {A w C} 
      → Γ ⊢ exp ((∃₅ A) [ w ])
      → ((w' : _) → 
         Γ ,, value ((A w') [ w ]) ⊢ exp (C [ w ]))
      → Γ ⊢ exp (C [ w ])

    leta : ∀ {A w w' C} 
      → Γ ⊢ exp ((A at w') [ w ])  
      → (Γ ,, value (A [ w' ]) ⊢ exp (C [ w ])) 
      → Γ ⊢ exp (C [ w ])

    lets : ∀ {A w C} 
      → Γ ⊢ exp (⌘ A [ w ])
      → (Γ ,, valid A ⊢ exp (C [ w ])) 
      → Γ ⊢ exp (C [ w ])
\end{code}
\end{multicols}
\end{footnotesize}

\caption{ML5 Static Semantics}
\label{fig:ml5-typing}

\end{figure}
