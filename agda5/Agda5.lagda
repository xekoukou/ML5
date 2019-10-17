\newcommand{\noagda}[0]{}
\newcommand{\ignore}[1]{}

\ignore{
\begin{code}
open import lib.Prelude hiding ([_])

module agda5.Agda5 where

  postulate 
\end{code}}

\section{L5}

In this section, we define an interface for distributed programming in
Agda, based on lax logic~\citep{curry52lax,benton+98lax}.  We define a
type of worlds and a family of monads \ttt{IO w S} indexed by worlds,
which represent an effectful computation that runs at world \cd{w} and
produces a value of type \cd{S}.

\begin{code}
    World : Set 
    server : World
    client : World

    IO     : World → Set → Set
    return : ∀ {w S} → S → IO w S
    _>>=_    : ∀ {w S S'} → IO w S → (S → IO w S') → IO w S'
    get    : ∀ {w' w S} → IO w' S → IO w S

    Ref : World → Set → Set
    _:=_ : ∀ {w S} → Ref w S → S → IO w Unit
    !    : ∀ {w S} → Ref w S → IO w S
    new  : ∀ {w S} → IO w (Ref w S)
\end{code}
\ignore{
\begin{code}
    Run : ∀ {w S} → IO w S → S → Set
    Run/return  : ∀ {w S} {v : S} → Run{w} (return v) v
    Run/bind    : ∀ {w S S' e e'} {v : S} {v' : S'} → Run{w} e v → Run (e' v) v' → Run (e >>= e') v'
    Run/get     : ∀ {w w' S v} {e : IO w S} → Run e v → Run{w'} (get e) v
\end{code}}
The definitions are parametrized by a type of worlds, which we here
assume to contain client and server.  \cd{IO w S} is axiomatized as a
monad, with \cd{return} and bind (\cd{>>=}), along with an additional
operation \cd{get} that allows the computation to switch to a different
world.  The command \ttt{get} can be thought of as a remote procedure
call, which goes to \ttt{w'}, runs the given command, and then brings
the resulting value back to \ttt{w}.  Next, we define a type \ttt{Ref w
S} of heap references located at world \ttt{w}.  The operations for
setting (\ttt{:=}), getting (\verb|!|), and creating (\ttt{new})
references require the reference to be at the same world as the
computation.

Because these types are embedded in Agda, they may interact freely with
the host language types---e.g., a computation may return value of any
Agda \ttt{Set}, and we can use Agda Π and Σ types to quantify over
worlds.

In Agda, we use the \emph{postulate} keyword to assume an implementation
of this interface.  Under the hood, these operations can be implemented
using foreign-function calls, e.g. interpreting \ttt{IO k A} as the
\ttt{IO} monad in Haskell.  A trivial implementation of this interface
may run all computations in a single executable on a single machine.  A
more realistic implementation would require compiler support for (a)
compiling a single program to run on multiple hosts and (b) marshaling
and unmarshaling all values; both of these are provided by the ML5
compiler.  We also give a high-level abstract operational semantics for
computations in Section~\ref{sec:soundness}.

%% ENH: immutable refs

L5 satisfies the design goals of ML5: it ensures that resources are only
used by a computation running at the appropriate world, and it also
makes all communication explicit via \ttt{get}. 

\paragraph{Example}
The following example computation illustrates the use of \ttt{get} in Agda:

\begin{code}
  update : (Ref server (IO server Unit))  →  IO client Unit  →  IO client Unit
  update l clicomp = get{server} (l := (get{client} clicomp)) 
\end{code}

\noindent This function takes a pointer to a callback, represented as a
\ttt{Ref server (IO server Unit)}, and a computation \ttt{clicommp} that
runs on the client.  It creates a computation that start running on the
client, goes to the server, and updates the callback ref to point to a
computation that goes back to the client and runs the \ttt{clicomp}.  In
fact, there is nothing about the code that is tied to the worlds
\ttt{client} and \ttt{server}: we could make the computation polymorphic
in the worlds, using Agda dependent functions to quantify over them:

\begin{code}
  update' : ((w1 : World) (w2 : World) → Ref w2 (IO w2 Unit) → IO w1 Unit → IO w1 Unit)
  update' w1 w2 l comp1 = get{w2} (l := (get{w1} comp1))
\end{code}

\section{HL5}

A disadvantage of L5 is that types can be somewhat verbose, as they they
repeat the same world multiples times (e.g. both \ttt{client} and
\ttt{server} occur twice in the type of \ttt{update}).  A hybrid modal
type system, as in ML5, permits more concise specifications: one writes
a modal type \ttt{A}, which for the most part does not mention worlds,
and then interprets it relative to a world at the outside by writing
\ttt{A < w >}.  In this section, we define HL5, which is a hybrid type
system constructed on top of the above lax logic.  We define HL5 by
semantic embedding into L5 (which itself is just a library in Agda): we
define a syntax of HL5 types, and then an interpretation function
mapping HL5 types to functions from worlds to Agda \ttt{Set}s (or,
thinking constructively, predicates on worlds).  

\subsection{HL5 Types} The datatype of HL5 types is defined as follows
(note that Agda allows multiple datatype constructors per line):

\begin{code}
  data Type : Set where
    _⊃_ _∨_ : Type → Type → Type
    ∀₅ ∃₅ : (World → Type) → Type
    _at_ : Type → World → Type
    ◯    : Type → Type
    ref  : Type → Type
\end{code}
\ignore{
\begin{code}
    ↓₅ : (World → Type) → Type
    _∧_ : Type → Type → Type
    ⊤ ⊥ : Type
    list : Type → Type
\end{code}}
%
The types \cd{⊃} and \ttt{∨} represent functions and sums (the notation
\verb|_∨_| allows ∨ to be used infix).  The types \ttt{∀₅} and \cd{∃₅}
represent quantifiers over worlds.  Next, \cd{at} is a connective of
hybrid logic, which allows types to set the world at which the type is
interpreted.  Finally, \cd{◯} and \cd{ref} represent monadic
computations and references; note that they are \emph{not} indexed by a
world. Box and diamond can be defined using quantifiers and \cd{at}:
\cd{□ A = ∀₅ (λ w → A at w)} and \cd{◇ A = ∃₅ (λ w → A at w)}.

\paragraph{Example} Below we define the interpretation function \ttt{A <
w >}, which takes a modal type and a world and produces an Agda
\ttt{Set}.  Using modal types, we can rewrite the type of \ttt{update}
as follows:

\noagda \begin{verbatim}
  update  : (((ref (◯ ⊤)) at server)  ⊃  ◯ ⊤  ⊃  ◯ ⊤) < client >
\end{verbatim}
%
The type \ttt{((ref (◯ ⊤)) at server) ⊃ ◯ ⊤ ⊃ ◯ ⊤} says that
\ttt{update} takes a reference to a computation, located at the server,
along with a computation, and produces a computation. The Agda function
\ttt{A < w >} takes a \ttt{Type} and a \ttt{World} and produces a
\ttt{Set}; here, it is used to say that the whole type is interpreted
relative to the client.

The above polymorphic \ttt{update'} is typed as follows: 

\noagda \begin{verbatim}
  update' : (□(∀₅ (λ w2 → ref (◯ ⊤) at w2  ⊃  ◯ ⊤ ⊃ ◯ ⊤))) <*>
\end{verbatim}
%
where the postfix symbol \ttt{<*> : Type → Set} means that the
proposition is true in all worlds (i.e. \ttt{A <*>} means the Agda type
\ttt{{w : World} → A < w >}).  The outer \ttt{□} binds the "client"
world (i.e. the world for the computations in \ttt{◯ ⊤ ⊃ ◯ ⊤}); the
inner ∀₅ binds the "server" world (i.e. the world of the \ttt{ref (◯
⊤)}.

\ignore{
\begin{code}
  infix 100 _<_> -- more tightly than ::
  infixr 101 _⊃_ -- more tightly than [ ] 
  infixr 102 _∨_ -- more tightly than [ ] 
  infixr 103 _∧_ -- more tightly than [ ] 
  infix 104 _at_ -- more tightly than [ ] 
\end{code}}

\subsection{Interpretation}

We define an interpretation function \cd{A < w >} interpreting a type
\ttt{A} and a world \ttt{w} as an Agda classifier (a \ttt{Set}).  Then
the proof of an HL5 judgement \ttt{A1 < w1 > ... ⊢ C < w >} is an Agda
function of type \ttt{A1 < w1 > ... → C < w >}.  This interpretation is
a \emph{constructive Kripke semantics}---i.e. a Kripke semantics of an
intuitionistic modal logic in intuitionistic first-order logic, relative
to the Kripke structure given by the type
\ttt{World}.\footnote{Technically, we omit two of the pieces of a Kripke
structure: \ttt{World} is the set of states, but because we are
representing S5, we can elide the accessibility relation, and because we
do not have uninterpreted base \ttt{Type}s, we do not need an
interpretation of them.}  The interpretation is defined as as follows:

\begin{code}    
  _<_> : Type → World → Set
  (ref A) < w > = Ref w (A < w >)
  (◯ A) < w > = IO w (A < w >)
  (A at w') < _ > = A < w' >
  (A ⊃ B) < w > = A < w > → B < w >
  (A ∨ B) < w > = Either (A < w >) (B < w >)
  (∀₅ A) < w >   = (w' : World)  →  (A w') < w >
  (∃₅ A) < w >   = Σ \ (w' : World)  →  (A w') < w >
\end{code}
\ignore{
\begin{code}
  (A ∧ B) < w > = A < w > × B < w >
  ⊤ < w >       = Unit
  ⊥ < w >       = Void
  (list A) < w > = List (A < w >)
  (↓₅ A) < w >   = (A w) < w >
\end{code}}
%
The main action of the translations is to annotate \ttt{ref} and \ttt{◯}
with the world at which the type is being interpreted.  The hybrid
connective \cd{at} interprets its body at the specified world, ignoring
the current world.  Otherwise, the translation interprets each
connective as the corresponding Agda \ttt{Set}-former, with the
translation applied recursively.  Note
that the interpretation of \ttt{⊃} is simply \ttt{→}: when giving a
Kripke semantics for intuitionistic logic in a \emph{classical}
meta-language, it is necessary to interpret \ttt{A ⊃ B} as if it were
boxed, by quantifying over future worlds; but because our meta-language is
intuitionistic, this is not necessary here.  

%  Finally, in \ttt{◯ A} and \ttt{ref A}, the world plays two roles:
%   \ttt{◯ A < w >} is a computation that runs at \ttt{w} and produces a
%   result specified by interpreting \ttt{A} at \ttt{w}; \ttt{ref A < w
%   > } is a reference located at \ttt{w} to a value specified by
%   interpreting \ttt{A} relative to \ttt{w}.

The function \ttt{<*> : Type → Set} is defined to be the Agda set \cd{\{w
: World\} → A < w >}---\ttt{A} is true in all worlds, with the world
itself an implicit argument to the function.  Agda verifies that the
modal types of \ttt{update} and \ttt{update'} reduce to the explicit
types given above.

This formalization has several benefits: we can immediately use Agda to
program in the modal logic, and existing Agda code can be used at modal
types.  For example, some of the characteristic axioms of intuitionistic
S5 are implemented as follows (the remainder can be found in the
corresponding Agda code):

\ignore{
\begin{code}
  module Axioms where

    infix 104 □_ -- more tightly than [ ] 
    infix 104 ◇_ -- more tightly than [ ] 

    ⊞_ : (World → Type) → Type
    ⊞_ A = ∀₅ (\ w → (A w) at w)

    □_ : Type → Type
    □_ A = ∀₅ (\ w → A at w)

    ◇_ : Type → Type
    ◇_ A = ∃₅ (\ w → A at w)

    _<*> : Type → Set
    _<*> A = ∀ {w} → A < w >

    □refl : ∀ {A} → (□ A ⊃ A) <*>
    □refl {A} {w} = \ f → f w

    K : ∀ {A B} → (□ (A ⊃ B) ⊃ □ A ⊃ □ B) <*>
    K f x w = f w (x w) 
\end{code}}

\begin{code}
    ◇∨ : ∀ {A B} → (◇ (A ∨ B) ⊃ ◇ A ∨ ◇ B) <*>
    ◇∨ (w , Inl e) = Inl (w , e)
    ◇∨ (w , Inr e) = Inr (w , e)

    ◇5 : ∀ {A} → (◇ □ A ⊃ □ A) <*>
    ◇5 (w , boxed) = boxed
\end{code}

\ignore{
\begin{code}
    curry : ∀ {A B} → ((◇ A ⊃ □ B) ⊃ □ (A ⊃ B)) <*>
    curry = \ f w' x → f (w' , x) w'

    □trans : ∀ {A} → ((□ A) ⊃ (□ □ A)) <*>
    □trans = \ f → \ _ w' → f w'

    ◇refl : ∀ {A} → (A ⊃ ◇ A) <*>
    ◇refl {A} {w} = \ x → w , x

    ◇trans : ∀ {A} → ((◇ ◇ A) ⊃ (◇ A)) <*>
    ◇trans = snd

    K◇ : ∀ {A B} → (□ (A ⊃ B) ⊃ ◇ A ⊃ ◇ B) <*>
    K◇ f x = (fst x) , (f (fst x) (snd x))

    ◇⊥ : (◇ ⊥ ⊃ ⊥) <*>
    ◇⊥ = snd

    □5 : ∀ {A} → (◇ A ⊃ □ ◇ A) <*>
    □5 = \ x _ → x

    update2  : (((ref (◯ ⊤)) at server)  ⊃  ◯ ⊤  ⊃  ◯ ⊤) < client >
    update2 l clicomp = get{server} (l := (get{client} clicomp)) 

    update2' : (w : World) → (∀₅ (λ w' → (ref (◯ ⊤) at w') ⊃ ◯ ⊤ ⊃ ◯ ⊤)) < w >
    update2' w w' l clicomp = get{w'} (l := (get{w} clicomp))
\end{code}}

\noindent Indeed, one can check that this definition validates all of
the rules of intuitionistic S5~\citep{simpson93thesis}, by implementing
the proof that the Simpson rules are sound for the Kripke semantics.
For example, the untethered elimination rule for disjunction and a
projective elimination rule for \ttt{at} are defined as follows:

\begin{code}
    casev : ∀ {A B C w w'} →  A ∨ B < w >
          → (A < w > → C < w' >)  →  (B < w > → C < w' >)
          → C < w' >
    casev (Inl e) b1 b2 = b1 e
    casev (Inr e) b1 b2 = b2 e

    unatv : ∀ {A w w'}  →  (A at w') < w >  →  A < w' >
    unatv x = x
\end{code}

Additionally, we can see that the return and bind operations on the
monad have their expected types at any world:

\begin{code}
    hl5ret : ∀ {A} → A ⊃ ◯ A <*>
    hl5ret = return

    hl5bind : ∀ {A B} → ◯ A ⊃ (A ⊃ ◯ B) ⊃ ◯ B <*>
    hl5bind =  _>>=_ 
\end{code}
%
The type of bind insists that all three ◯'s be at the same world:
sequencing tethers the premise to the conclusion.
 
Having considered return and bind, it is natural to ask what hybrid type
can we ascribe to the \ttt{get} operation on the indexed monad \ttt{IO w
A}. If we try defining

\noagda \begin{verbatim}
    hl5get : ∀ {A w1 w2} → ((◯ A) at w1) ⊃ ((◯ A) at w2) <*>
\end{verbatim}
%
we see that \ttt{hl5get} must transform \ttt{IO w1 (A < w1 >)} into \ttt{IO
w2 (A < w2 >)}.  L5 \ttt{get} satisfies this requirement if \ttt{A} is a
\emph{constant function} of its world argument, in which case \ttt{A < w1 >} is the same Agda 
\ttt{Set} as \ttt{A < w2 >}.

\ignore{
\begin{code}
  open Axioms

  data EqSet : (A B : Set) → Set1 where
    eq→ : ∀ {A1 A2 B1 B2 : Set} → EqSet B1 A1 → EqSet A2 B2 → EqSet (A1 → A2) (B1 → B2)
    eq× : ∀ {A1 A2 B1 B2 : Set} → EqSet A1 B1 → EqSet A2 B2 → EqSet (A1 × A2) (B1 × B2)
    eqEither : ∀ {A1 A2 B1 B2 : Set} → EqSet A1 B1 → EqSet A2 B2 → EqSet (Either A1 A2) (Either B1 B2)
    eqΠ : ∀ {A : Set} {B1 B2 : A → Set} → ((x : A) → EqSet (B1 x) (B2 x)) → EqSet ((x : A) → B1 x) ((x : A) → B2 x)
    eqΣ : ∀ {A} {B1 B2 : A → Set} → ((x : A) → EqSet (B1 x) (B2 x)) → EqSet (Σ \ (x : A) → B1 x) (Σ \ (x : A) → B2 x)
    eqRefl : ∀ {A} → EqSet A A

  coerce : ∀ {A B} → EqSet A B → A → B
  coerce (eq→ y y') v = \ x → coerce y' (v (coerce y x))
  coerce (eqEither y y') (Inl y0) = Inl (coerce y y0)
  coerce (eqEither y y') (Inr y0) = Inr (coerce y' y0)
  coerce (eqΠ y) v = \ x → coerce (y x) (v x)
  coerce (eqΣ y) (x , y') = x , coerce (y x) y'
  coerce (eq× x y) (x1 , y1) = coerce x x1 , coerce y y1
  coerce eqRefl v = v
\end{code}}

We characterize constant modal types by the property that they yield the
same \ttt{Set} for any two arguments:

\begin{code}  
  Constant : Type → Set1
  Constant A = ∀ {w w'} → EqSet (A < w >) (A < w' >)
\end{code}
%
Here \ttt{EqSet} is an Agda relation expressing that the two \ttt{Set}s
are equal classifiers (in fact, we need a notion of equality that
compares the bodies of Π and Σ on all arguments, which we borrow from
OTT~\citep{altenkirch+07ott}); it is equipped with an operation
\ttt{coerce : ∀ \{A B\} → EqSet A B → A → B}.
It is simple to prove that \ttt{A at w} is constant, and that the
connectives ∨ ⊃ ∀₅ ∃₅ preserve constantness.  Neither \ttt{ref} nor ◯ is
constant, as their interpretation directly mentions the world.  Thus,
the constant types are those where all \ttt{ref}s and ◯'s are guarded by
an \ttt{at}.

\ignore{
\begin{code}
  iat : ∀ {A w} → Constant (A at w)
  iat = eqRefl
  
  i∨ : ∀ {A B} → Constant A → Constant B → Constant (A ∨ B)
  i∨ i1 i2 = eqEither i1 i2

  i∧ : ∀ {A B} → Constant A → Constant B → Constant (A ∧ B)
  i∧ i1 i2 = eq× i1 i2

  i⊃  : ∀ {A B} → Constant A → Constant B → Constant (A ⊃ B)
  i⊃ i1 i2 = eq→ i1 i2

  i∀  : ∀ {A} → ((w' : _) → Constant (A w')) → Constant (∀₅ A)
  i∀ iA = eqΠ (\ w → iA w)

  i∃  : ∀ {A} → ((w' : _) → Constant (A w')) → Constant (∃₅ A)
  i∃ iA = eqΣ (\ w → iA w)

  i⊤ : Constant ⊤
  i⊤ = eqRefl

  i⊥ : Constant ⊥
  i⊥ = eqRefl

  -- can't
  --   i◯  : ∀ {A} → Constant A → Constant (◯ A)
  --   i◯ ia = {!!}
\end{code}}

Now, we can ascribe \ttt{get} the following monadic type:
\begin{code}
  hl5get : ∀ {A w1 w2} → Constant A → ((◯ A) at w1) ⊃ ((◯ A) at w2) <*>
  hl5get con e = get e >>= \ v → return (coerce con v)
\end{code}
\ttt{hl5get} is equivalent to \ttt{get}, using the monad laws and the
fact that coercion based on a proof of \ttt{EqSet} is the identity (at
least up to extensional equality),

\ignore{
%% true but not helpful to the story
Semantically, we express mobility of a type \ttt{A} as \ttt{A ⊃ □ A}. We
can show that various types are mobile; computationally, this wraps a
value with a coercion from the world \ttt{wFrom} to the world \ttt{wTo}:

\begin{code}
  Boxable : Type → Set
  Boxable A = (A ⊃ □ A) <*>
  
  mat : ∀ {A w} → Boxable (A at w)
  mat e wTo = e 

  ---- no rule for ref's 

  m⊃  : ∀ {A B} → Boxable A → Boxable B → Boxable (A ⊃ B)
  m⊃ mA mB {wFrom} f wTo = \ x → mB (f (mA x wFrom)) wTo

  m∨  : ∀ {A B} → Boxable A → Boxable B → Boxable (A ∨ B)
  m∨ mA mB (Inl e) wTo = Inl (mA e wTo)
  m∨ mA mB (Inr e) wTo = Inr (mB e wTo)

  m∀  : ∀ {A} → ((w' : _) → Boxable (A w')) → Boxable (∀₅ A)
  m∀ mA f wTo = \ w → (mA w) (f w) wTo

  m∃  : ∀ {A} → ((w' : _) → Boxable (A w')) → Boxable (∃₅ A)
  m∃ mA (w , e) wTo = w , (mA w) e wTo

  m◯  : ∀ {A} → Boxable A → Boxable (◯ A)
  m◯ mA e wTo = (get e) >>= λ x → return (mA x wTo)
\end{code}
\ignore{
\begin{code}
  m∧  : ∀ {A B} → Boxable A → Boxable B → Boxable (A ∧ B)
  m∧ mA mB (e1 , e2) wTo = mA e1 wTo , mB e2 wTo

  m⊤  : Boxable ⊤
  m⊤ a wTo = <>

  m⊥  : Boxable ⊥
  m⊥ () _

  mlist : ∀ {A} → Boxable A → Boxable (list A)
  mlist mA l wTo = Listm.map (\ x → mA x wTo) l
\end{code}}
%

The interesting cases are as follows: \cd{at} is always mobile (because
the interpretation of \cd{at} is independent of the world).  The
implementation for \ttt{at} is the identity, because \cd{(A at w0) <
wFrom >} and \cd{A at w0 < wTo >} are the same proposition.  On the
other hand, \ttt{ref}'s are not mobile by definition: the point of the
type system is to ensure that resources are only used at the correct
location.  Otherwise a type is mobile iff its components are; the
implementation commutes with the structure of values.  Note that the
case for ⊃ has a contravariant twist: the recursive call \cd{(mobilize
mA x wFrom)} transports the argument backwards from \emph{wTo} to
\emph{wFrom}---this works in S5 because of symmetry.  For similar
reasons, this analysis suggests that \ttt{◇ A} would not be mobile in
modal logics other than S5: \ttt{◇ A ⊃ □ ◇ A} is true in S5 but not
other modal logics.

We can additionally prove that ◯ is mobile in A5: our goal is to
transform \cd{IO wFrom (A < wFrom >)} to \cd{IO wTo (A < wTo >)}: the
resulting computation first does a \ttt{get} and then recursively
transforms the value that comes back.  However, because this coercion
includes a \ttt{get}, we would not want it to be inserted automatically
by the compiler.

It is convenient to define an alternate version of mobility where
\ttt{wTo} is an implicit argument; we call this function \ttt{wrap}:
\begin{code}
  wrap : ∀ {A w w'} → Boxable A → A < w > → A < w' >
  wrap m e = m e _ 
\end{code}
}

\ignore{
\begin{code}
  -- alias so we don't break the other code
  get* : ∀ {A w w'} → Boxable A → A < w > → A < w' >
  get* {A} m e = wrap{A} m e

  -- would just be propositional equality if that were extensional
  Eq : (A : Type) → {w : World} → A < w > → A < w > → Set
  Eq (A at w) e1 e2 = Eq A e1 e2
  Eq (A ⊃ B) e1 e2 = (x y : _) → Eq A x y → Eq B (e1 x) (e2 y) 
  Eq (A ∧ B) p1 p2 = Eq A (fst p1) (fst p2) × Eq B (snd p1) (snd p2)
  Eq (A ∨ B) (Inl x) (Inl y) = Eq A x y
  Eq (A ∨ B) (Inr x) (Inr y) = Eq B x y
  Eq (A ∨ B) _ _ = Void
  Eq (list A) [] [] = Unit
  Eq (list A) (x :: xs) (y :: ys) = Eq A x y × Eq (list A) xs ys
  Eq (list A) _ _ = Void
  Eq ⊤ _ _ = Unit
  Eq ⊥ () ()
  Eq (∀₅ A) e1 e2 = (w : _) → Eq (A w) (e1 w) (e2 w)
  Eq (∃₅ A){w} e1 e2 =  Σ \ (p : Id (fst e1) (fst e2)) → Eq (A (fst e1)) (snd e1) (Idm.subst (\ x → A x < w >) (Idm.sym p) (snd e2)) 
    -- kinda cludgey 
  Eq (↓₅ A) e1 e2 = Eq (A _) e1 e2 
  Eq (◯ A) e1 e2 = Id e1 e2 -- punt
  Eq (ref A) e1 e2 = Id e1 e2 -- punt
\end{code}}
