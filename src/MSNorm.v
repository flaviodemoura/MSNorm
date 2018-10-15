(** * Introduction *)

(** It is well-known that termination is not a modular property for
    rewrite systems %\cite{toyama87}%.  A property $P$ of reduction
    relation systems is modular if given two systems $A$ and $B$, the
    property $P$ holds for the combined system built from $A$ and $B$
    whenever $P$ holds for both $A$ and $B$.  In other words, the
    union of terminating rewrite systems is not necessarily
    terminating.  Nevertheless, under certain restrictions, modularity
    of termination can be recovered %~\cite{Gramlich12}%.

    On the other hand, the preservation of strong normalisation
    property (PSN) is known to be not satisfied for some calculi with
    explicit substitutions %\cite{Mellies95,Gu99}%. A calculus with
    explicit substitutions %\cite{Lins86,ACCL91,kes09}% presents some
    formalisation for the substitution operation, defined as a
    meta-operation in the $\lambda$-calculus. In other words, for
    rule $(\lambda{x}. M) N \to_{\beta} M [x:=N]$ in such a calculus, $M [x:=N]$
    represents a term where the substitution is
    defined through a small-step semantics. PSN property in this
    context guarantees that any strongly normalising,
    i.e. terminating, term in the $\lambda$-calculus is also strongly
    normalising in the calculus with explicit substitutions.
 
    The Modular Strong Normalisation Theorem states the conditions for
    the union of two reduction relations over a set $A$ to be PSN
    through its relation of simulation to a reduction relation over
    some set $B$ (cf. %~\cite{LengrandPhD,kes09}%). In particular,
    when the reduction relation over $B$ is terminating and the
    simulation relation is complete, the theorem guarantees that both
    reductions over $A$ are terminating and so its union, i.e. that
    termination is modular.

    We present in this work a constructive proof of the Modular Strong
    Normalisation Theorem in the Coq Proof Assistant
    %~\cite{CoqTeam}%. The proof is entirely constructive in the sense
    that no classical reasoning is used, i.e. the law of excluded
    middle, proofs by contradiction or any equivalent inference
    rule. This is interesting from the computational point of view
    since the algorithmic content of proofs can automatically be
    extracted as certified code %~\cite{Let2008}%. Eventhough no code
    extraction is executed in the present work, it takes part in a
    project to certify the proofs of %~\cite{kes09}%, aiming to
    extract certified code. The choice of Coq as the formalisation
    tool is natural since the underlying logic behind the calculus of
    inductive constructions, the theory over which Coq is developed,
    is also constructive %\cite{Paulin93,wernerPhD}%.

    A constructive proof of the Modular Strong Normalisation Theorem
    is presented by S. Lengrand in %\cite{LengrandPhD}% and some of
    the basic notions used in this proof, such as strong
    normalisation, is already formalised in Coq
    %\cite{lengrand-nt}%. In a certain sense, this work can be seen as
    a non-trivial expansion of the normalisation theory formalised by
    Lengrand. In fact, the strong normalisation property defined in
    %\cite{LengrandPhD}% uses a specialized inductive principle that
    should hold for all predicates, i.e. through a second order
    formula. On the other hand, in this work we use only the standard
    inductive definition of the strong normalisation property
    (cf. %\cite{kes09,LengrandPhD,Raams-phd}%), and we also prove the
    equivalence between these definitions. In this way, we understand
    that we achieved a simpler and straightforward formalisation. The
    proof of the Modular Strong Normalisation Theorem follows the
    ideas in Lengrand's PhD thesis, but to the best of our knowledge,
    this is the first formalisation of this theorem.

    The contributions of this work are summarised below.

    %\begin{itemize}

      \item We provide a complete formalisation of the constructive
      normalisation theory based on the simulation technique developed
      in \cite{LengrandPhD}. In particular:

      \begin{itemize}

      \item We built a constructive proof of the
            Modular Strong Normalisation Theorem, and

      \item We proved the equivalence between Lengrand's definition of
            strong normalisation and the standard inductive definition
            of strong normalisation.
            
      \end{itemize} \end{itemize}%

     This paper is built up from a Coq script where some code is
     hidden for the sake of clarity of this document. The
     formalisation is compatible with Coq 8.8.0. All the files
     concerning this work are freely available in the repository %{\tt
     https://github.com/flaviodemoura/MSNorm}%. *)


(** * The Modular Strong Normalisation Theorem *)

(** In this section, we present the Modular Strong Normalisation
    Theorem whose formalisation is detailed in the next section. This
    is an abstract theorem about termination of reduction relations
    through the well-known simulation technique%~\cite{BN98}%. In
    order to fix notation, let [A] and [B] be sets. A relation from
    [A] to [B] is a subset of $A\times B$. If $R$ is a relation from
    [A] to [B] then we write $R\ a\ b$ instead of $(a,b) \in R$ and,
    in this case, we say that $a$ %{\it reduces}% to $b$ or that $b$
    is a $R$-%{\it reduct}% of $a$. Using arrows to denote relations
    and $\to$ being a relation from [A] to [B] then $\leftarrow$
    denotes the inverse relation from [B] to [A]. If $\to_1$ is a
    relation from $A$ to $B$ and $\to_2$ is a relation from $B$ to
    $C$, then the composition of $\to_1$ with $\to_2$, written
    $\to_1 \# \to_2$, is a relation from $A$ to $C$. A relation from
    a set to itself is a %{\it reduction relation over a set}%, i.e. a
    reduction relation over A is a subset of $A\times A$. If $\to_A$
    is a reduction relation over $A$, then a %{\it reduction
    sequence}% is a sequence of the form $a_0 \to_A a_1 \to_A a_2
    \to_A \ldots$ A reduction sequence $a_0 \to_A a_1 \to_A a_2 \to_A
    \ldots \to_A a_n\ (n\geq 0)$ is a $n$-step reduction from $a_0$. A
    reduction sequence is finite if it is a $n$-step reduction for
    some $n \in \mathbb{N}$, and infinite otherwise. We write
    $\to_A^+$ (resp. $\to_A^*$) for the transitive (resp. reflexive
    transitive) closure of $\to_A$.
    
    An element $a\in A$ is %{\it strongly normalising}% w.r.t. $\to_A$
    if every reduction sequence starting from $a$ is finite, and in
    this case we write $a \in SN^{\to_A}$. Usually, this idea is
    expressed inductively as follows: %\begin{equation}\label{def:sn}
    a \in {SN}^{\to_A} \mbox{ iff } \forall b, (a \to_A b \mbox{
    implies } b \in {SN}^{\to_A}) \end{equation}% *)
(*
%\noindent% whose Coq code is given by
[[
Inductive SN_ind {A:Type} (red: Red A) (a:A): Prop :=
  | sn_acc: (forall b, red a b -> SN_ind red b) -> SN_ind red a.
]]
A few comments about Coq are at a place. In the above definition, [Inductive] is the reserved word for inductive definitions. It is followed by the name of the definition, which in our case is [SN_ind], and it has three arguments: [{A:Type}], [(red:Red A)] and [(a:A)]. The first argument appears between curly brackets, which means that it is  %{\it implicit}%. Implicit arguments are types of polymorphic functions that can be inferred from the context. The second argument corresponds to a reduction relation [red] over [A], and the third argument is an element of [A]. This definition has one constructor named [sn_acc] whose content corresponds exactly to the definition given in (%\ref{def:sn}%). In this way, in order to prove that a certain element [a:A] is strongly normalising w.r.t. a reduction relation $\to_r$, one has to build a proof of the formula $\forall b, a \to_r b \to SN\_ind \to_r b$.*)

(** In order to present the theorem, we need to define the notions of
strong and weak simulation. In the following definitions $A$ and $B$
are arbitrary sets:

    %\begin{definition}\label{def:sws} Let $\to$ be a relation from
     $A$ to $B$, $\to_A$ be a reduction relation over $A$ and $\to_B$
     be a reduction relation over $B$. The reduction relation $\to_B$
     {\it strongly} (resp. {\it weakly}) simulates $\to_A$ through
     $\to$ if $(\leftarrow \# \to_A) \subseteq (\to_B^+ \#
     \leftarrow)$ (resp. $(\leftarrow \# \to_A) \subseteq (\to_B^*
     \# \leftarrow)$).

    \begin{tikzpicture}[scale=.45] \draw[ultra thick,myblue] (0,0)
    circle [x radius=1.5cm, y radius=4cm] (6,0) circle [x
    radius=1.5cm, y radius=4cm];
                     
    \node[font=\color{myblue}\Large\bfseries] at (0,5) {A};
    \node[font=\color{myblue}\Large\bfseries] at (6,5) {B};
 
    \node (a1) at (0,2) {a}; \node (a2) at (0,0) {a'};
 
    \node[circle] (b1) at (6,2) {b}; \node[circle] (b2) at (6,-2)
    {b'}; \node[above= 0.0001cm of b2] (aux) {};

    \node[left= 0.00002cm of aux] (aux2) {}; \node[right= 0.000002cm
    of aux2, red] (aux3) {+};
 
    \draw[->] (a1.east) .. controls +(up:0cm) and +(left:1cm)
    .. node[above,sloped] {} (b1.west);

    \draw[->,red] (a2.east) .. controls +(up:0cm) and +(left:1cm)
    .. node[above,sloped] {} (b2.west);

    \draw[->] (a1.south) .. controls +(up:0cm) and +(left:0cm)
    .. node[left] {\scriptsize A} (a2.north);

    \draw[->,red] (b1.south) .. controls +(up:0cm) and +(left:0cm)
    .. node[left] {\scriptsize B} (b2.north);

    \draw[ultra thick,myblue] (12,0) circle [x radius=1.5cm, y
    radius=4cm] (18,0) circle [x radius=1.5cm, y radius=4cm];
                     
    \node[font=\color{myblue}\Large\bfseries] at (12,5) {A};

    \node[font=\color{myblue}\Large\bfseries] at (18,5) {B};
 
    \node (a1) at (12,2) {a}; \node (a2) at (12,0) {a'};
 
    \node[circle] (b1) at (18,2) {b}; \node[circle] (b2) at (18,-2)
    {b'};

    \node[above= 0.0001cm of b2] (aux) {}; \node[left= 0.000002cm of
    aux] (aux2) {}; \node[right= 0.000002cm of aux2, red] (aux3) {*};


    \draw[->] (a1.east) .. controls +(up:0cm) and +(left:1cm)
    .. node[above,sloped] {} (b1.west);

    \draw[->,red] (a2.east) .. controls +(up:0cm) and +(left:1cm)
    .. node[above,sloped] {} (b2.west);

    \draw[->] (a1.south) .. controls +(up:0cm) and +(left:0cm)
    .. node[left] {\scriptsize A} (a2.north);

    \draw[->,red] (b1.south) .. controls +(up:0cm) and +(left:0cm)
    .. node[left] {\scriptsize B} (b2.north); \end{tikzpicture}
    \end{definition}%

    In what follows, we present the Modular Strong Normalisation
    Theorem and a draft of its proof. In addition, we highligth in
    %{\color{blue}blue}% the names of the corresponding results
    established in the formalisation, detailed in the next section.

    %\begin{theorem}[Modular Strong Normalisation Theorem]
      
      \noindent Let $\to$ be a relation from $A$ to $B$, $\to_1$ and
      $\to_2$ be two reduction relations over $A$, and $\to_B$ be a
      reduction relation over $B$. Suppose that:

      \begin{enumerate}

        \item\label{hip:one} $\to_B$ strongly simulates $\to_1$
                             through $\to$;

        \item\label{hip:two} $\to_B$ weakly simulates $\to_2$ through
                             $\to$;
      
        \item\label{hip:three} $A \subseteq SN^{\to_2}$.

      \end{enumerate}

      Then $\leftarrow ({SN}^{\to_B}) \subseteq {SN}^{\to_1 \cup
      \to_2}$. In other words, $$\forall a:A, a\in\, \leftarrow
      ({SN}^{\to_B}) \mbox{ implies } a \in {SN}^{\to_1\cup \to_2}.$$
      \end{theorem}%

      %\begin{proof}
      This proof follows the lines of \cite{LengrandPhD}, but using
      the standard $SN$ definition in (\ref{def:sn}). First of all,
      hypothesis \ref{hip:one} and \ref{hip:two} allow us to
      conclude that the composition $(\to_2^* \# \to_1)$ is
      strongly simulated by $\to_B$: in fact, from hypothesis
      \ref{hip:two} we have that $\to_2^*$ is weakly simulated by
      $\to_B$ {\color{blue}({\it SimulWeakReflTrans})}.  In
      addition, the composition of two reduction relations that are,
      respectively, strongly and weakly simulated by the same
      reduction relation is strongly simulated by this reduction
      relation {\color{blue}({\it WeakStrongSimul})}. Therefore,
      $(\to_2^* \# \to_1)$ is strongly simulated by $\to_B$ through
      $\to$ {\color{blue}({\it RCSimul})}, that together with the
      fact that $a\in \leftarrow({SN}^{\to_B})$ allow us to conclude
      that $a \in {SN}^{\to_2^* \# \to_1}$ {\color{blue}({\it
      SNbySimul})}.  Now, from hypothesis \ref{hip:three}, we have
      $a \in {SN}^{\to_2}$, and we conclude from the fact that
      ${SN}^{\to_2^* \# \to_1} \cap {SN}^{\to_2} = {SN}^{\to_1\cup
      \to_2}$ {\color{blue}({\it SNunion})}. \hfill$\Box$
      \end{proof}%

      *)

(** * The Formalisation *)

(** In this section we present the formalisation details of the
    Modular Strong Normalisation Theorem in the Coq Proof
    Assistant. The first important point is that our proof is
    constructive, i.e. it does not use classical reasoning such as the
    law of excluded middle, double negation elimination or proof by
    contradiction.

    In terms of notation, sets are coded as arbitrary types in such a
    way that the membership relation $a \in A$ ($a$ is an element of
    the set $A$) is represented as $a:A$ ($a$ has type $A$). Also,
    n-ary predicates and functions are defined in a curryfied version
    (cf. %\cite{Geu09}%).

    We start with some basic definitions in order to make Coq notation
    clear%\footnote{This paper is written directly from a Coq script
    file, therefore, the Coq code presented is the real code of the
    formalisation.}%. A relation from $A$ to $B$ is defined as a
    binary predicate: *)

Definition Rel (A B : Type) := A -> B -> Prop.
(** %\noindent% In this definition, [Rel] receives two types as
    arguments, and return the signature of a relation from $A$ to $B$,
    i.e. the type [A -> B -> Prop]. As mentioned before, if $A=B$ then we
    have a %{\it reduction relation}%: *)

Definition Red (A : Type) := Rel A A.
(** Given two relations [R1] and [R2] from [A] to [B], if every pair
    of elements in [R1] is also in [R2] then we say that [R1] is a
    subrelation of [R2]: *)

Definition Sub {A B} (R1 R2: Rel A B) : Prop := forall a b, R1 a b -> R2 a b.
(** In the above definition, [A] and [B] first appear between curly
    brackets, meaning that these arguments are %{\it
    implicit}%. Implicit arguments are the types of polymorphic
    functions which can be inferred from the context. Therefore, [Sub]
    requires two relations as explicit arguments while Coq
    automatically infers its type. More convenient notations can be
    easily defined for objects we are constructing. For instance, in
    the [Sub] predicate case we define an infix notation as follows:
    *)

Notation "R1 <# R2" := (Sub R1 R2) (at level 50).
(** Now one can write [R1 <# R2] instead of [Sub R1 R2]. In addition,
    in order to avoid parsing ambiguity, a precedence level ranging
    from 0 to 100 can be provided.

    Given two relations, say [red1] from [A] to [B] and [red2] from
    [B] to [C], one can build a new relation from [A] to [C] by
    composing its steps: *)

Inductive comp {A B C} (red1: Rel A B)(red2: Rel B C) : Rel A C :=
  compose: forall a b c,  red1 a b -> red2 b c -> comp red1 red2 a c.
Notation "R1 # R2" := (comp R1 R2) (at level 40).
(* begin hide *)
Arguments compose {A B C red1 red2} _ _ _ _ _ .
(* end hide *)
(** %\noindent% Note that [comp] is inductively defined with just one
    constructor, named [compose], that explicitly builds the composite
    relation from [A] to [C] from the given relations [red1] and
    [red2]. In addition, it is important to know that Coq
    automatically generates an inductive principle for every inductive
    definition. For instance, the natural numbers %{\tt nat}% are
    inductively defined as: 

    %\begin{alltt} 

    Inductive nat : Set := 
      O : nat | S : nat \(\to\) nat 

    \end{alltt}%

    %\noindent% The corresponding induction principle, named %{\tt
    nat\_ind}\footnote{The name of the automatic induction principle
    generated follows the pattern {\tt name\_ind}, i.e. the name of
    the inductive definition followed by the string {\tt \_ind}.}%, is
    given by %\begin{alltt} forall P : nat \(\to\) Prop, P 0 \(\to\)
    (forall n : nat, P n \(\to\) P (S n)) \(\to\) forall n : nat, P n
    \end{alltt}%

    Therefore, in order to prove that a certain property %{\tt P}%
    holds for all %{\tt n: nat}%, one needs to prove that %{\tt (P
    0)}% holds, and that if %{\tt (P n)}% holds then %{\tt (P (S n))}%
    also holds. In general, if %{\tt def}% is an inductive definition
    with constructors %{\tt c1}%, %{\tt c2}%, %\ldots%, %{\tt ck}%
    then, in order to prove that a property %{\tt P}% holds for every
    element defined by %{\tt def}%, we need to show, in a certain
    sense, that %{\tt P}% is closed for each of its constructors. For
    a more precise and detailed explanation about Coq induction
    principles see %\cite{CoqTeam,BC04,cpdt,Pierce:SF}%.

    The inverse of a relation from [A] to [B] is defined by induction
    as the corresponding relation from [B] to [A]: *)

Inductive inverse {A B} (R: Rel A B) : Rel B A :=
  inverseof: forall a b, R a b -> inverse R b a.

(** The transitive closure of a reduction relation [red] over [A] is
    constructed, as usual, by adding to [red] all possible reductions
    with at least one step starting from each $a\in A$: *)

Inductive trans {A} (red: Red A) : Red A :=
| singl: forall a b,  red a b -> trans red a b
| transit: forall b a c,  red a b -> trans red b c -> trans red a c.
(* begin hide *)
Arguments transit {A} {red} _ _ _ _ _ .
(* end hide *)
(** Therefore, it is straightforward from this definition that a
    reduction relation is included in its transitive closure: *)

Lemma transSub {A:Type} (red: Red A) : red <# (trans red).
(* begin hide *)
Proof.
  unfold Sub.
  intros a b H.
  apply singl; assumption.
Qed.
(* end hide *)
(** The reflexive transitive closure of a reduction relation is
    obtained from its transitive closure just adding reflexivity,
    i.e. by adding the fact that each element of the set reduces to
    itself (in 0 steps): *)

Inductive refltrans {A} (red: Red A) : Red A :=
| reflex: forall a,  refltrans red a a
| atleast1: forall a b,  trans red a b -> refltrans red a b.
(* begin hide *)
Lemma tailtransit {A red}: forall (b a c:A),  trans red a b -> trans red b c -> trans red a c.
Proof.
  intros b a c H1 H2.
  induction H1.
  + apply (transit b).
    * assumption.
    * assumption.
  + apply (transit b).
    * exact H.
    * apply IHtrans in H2; exact H2.
Qed.
(* end hide *)
(** The image of a predicate via a relation is inductively defined as
    follows: *)

Inductive Image {A B} (R:Rel A B)(P: A -> Prop): B -> Prop :=
  image: forall a b, P a -> R a b -> Image R P b.
(* begin hide *)
Arguments image {A B R P} _ _ _ _.
(* end hide *)
(** The notions of weak and strong simulation for reduction relations
    are a straightforward translation to the Coq syntax
    (cf. Definition %\ref{def:sws}%): *)

Definition WeakSimul {A B} (redA: Red A) (redB: Red B) (R: Rel A B) := 
  ((inverse R) # redA) <# ((refltrans redB) # (inverse R)).

Definition StrongSimul {A B} (redA: Red A) (redB: Red B) (R: Rel A B) := 
  ((inverse R) # redA) <# ((trans redB) # (inverse R)).

(** ** Equivalence between strongly normalising definitions *)

(** In this section, we prove the equivalence between Lengrand's
    definition of strong normalisation, denoted by [SN], and the
    inductive definition presented in (%\ref{def:sn}%), here denoted
    by [SN']. In his PhD thesis, Lengrand develops a constructive
    theory of normalisation in the sense that it does not rely on
    classical logic. In this theory, the notion of strong
    normalisation for reduction relations is defined by a second-order
    formula based on a stability predicate called [patriarchal]
    (cf. %\cite{LengrandPhD,lengSNInd05}%). *)

Definition patriarchal {A} (red:Red A) (P:A -> Prop): Prop :=
  forall x, (forall y, red x y -> P y) -> P x.

(** In this way, one says that a predicate [P] over [A] is patriarchal
    w.r.t. a reduction relation [red] over [A], if ([P a]) holds
    whenever ([P b]) holds for every [red]-reduct [b] of [a]. Now, an
    element [a] is strongly normalising w.r.t. to the reduction
    relation [red], when ([P a]) holds for every patriarchal predicate
    [P] w.r.t. reduction relation [red]: *)

Definition SN {A:Type} (red:Red A) (a:A): Prop :=
  forall P, patriarchal red P -> P a.

(** Most of the Coq code presented so far can be found at
%\cite{lengrand-nt}%. Nevertheless, our proof code is different since
library [ssreflect] is not used in the present development.

    The definition below corresponds to the usual inductive
    definition of strong normalisation for reduction relations, given
    in (%\ref{def:sn}%): *)

Inductive SN' {A:Type} (red: Red A) (a:A): Prop :=
  sn_acc: (forall b, red a b -> SN' red b) -> SN' red a.
(** So, given an element [a:A] and a reduction relation [red] over
    [A], [a] is strongly normalising w.r.t. [red] if every one-step
    [red]-reduct [b] of [a] is strongly normalising w.r.t. [red]. This
    means that in order to conclude [SN' red a], one has to prove
    first that [(forall b, red a b -> SN' red b)]. In addition, note that
    predicate [SN' red] is patriarchal hence it is straightforward
    that [SN] implies [SN'], i.e. that [SN' red a] holds whenever ([SN
    red a]) holds. This inductive definition gives only one direction
    of the biconditional in (%\ref{def:sn}%), but the other direction
    is straightforward: *)
  
Lemma SNstable {A} {red: Red A}: forall a, SN' red a ->
                                      forall b, red a b -> SN' red b.
Proof.
  intros a HSN b Hred.
  inversion HSN; clear HSN.
  apply H; assumption. 
Qed.
(** This proof analyses definition [SN'] in order to match the
    hypothesis [SN' red a], labelled [HSN], through the [inversion]
    tactic, that (informally) replaces hypothesis [(SN' red a)] by the
    information it contains. In this case, the known information comes
    from [SN'] definition and exactly what we need to prove. *)

(** The induction principle automatically generated for [SN'], called
    [SN'_ind], is as follows:

    %\begin{alltt} forall (A : Type) (red : Red A) (P : A -> Prop),
    (forall c : A, (forall b : A, red c b -> SN' red b) -> 
    (forall b : A, red c b -> P b) -> P c) -> 
    forall a : A, SN' red a -> P a
    \end{alltt}%

    %\noindent% Then, to conclude that some property [P] holds for any
    strongly normalising element [a], we need to prove that [P] holds
    for any strongly normalising [c], given it holds for every
    [red]-reduct [b] of [c]. In other words, we need to prove that [P]
    is patriarchal and holds for every strongly normalising
    [red]-reduct of [c]. *)

    (* %\dan{(na verdade o que temos no principio de inducao eh,
    supondo *) (* que 'a' seja SN e 'P' seja patriarchal, temos que P
    vale para *) (* a. Como isso se compara com a definicao de SN do
    Lengrand ?)}%. In the proof of theorem [SN'EquivSN], we
    establish the equivalence between these two definitions, and to do
    so, we use this induction principle. *)
(* begin hide *)
Lemma SNTrans {A} {red: Red A}: forall a, SN' red a -> SN' (trans red) a.
Proof.
  induction 1 as [? IHr IHTr]; apply sn_acc; intros ? HTrans;
    induction HTrans as [ ? ? ? | ? ? ? Hr Htr IHtr].
  - auto.
  - apply IHtr; intros; auto.
    + apply IHr in Hr; destruct Hr; auto.
    + apply IHTr in Hr; destruct Hr as [Hr]; apply Hr; constructor; auto.
Qed.
(* end hide *)

(** Equivalence between definitions [SN] and [SN'] is an important
    contribution of this work, we thus comment the proof steps in
    order to explain it in more detail. Comments are given in
    %{\color{blue} blue}% just after proof commands they refer
    to. Note that type [A] and a reduction relation [R] over [A] are
    given as implicit arguments, i.e. they are inferred from the
    context. *)

Theorem SN'EquivSN {A:Type} {R : Red A} : forall t, SN' R t <-> SN R t.
Proof.
  intro t; split. (** %{\color{blue} These proof commands introduces a
                      new skolem constant}% [t] %{\color{blue}to the
                      proof context and splits the bi-implication in
                      two steps. This means we are considering}%
                      [t] %{\color{blue}to be an arbitrary element of
                      set}% [A]%{\color{blue}, or more precisely,
                      let}% [t] %{\color{blue} be an element of type}%
                      [A]. *)
  
  - intro HSN'. (** %{\color{blue} The first implication to be
                       proved is}% [SN' R t -> SN R
                       t]%{\color{blue}, so we assume}% [SN' R t]
                       %{\color{blue} and we label this assumption
                       as}% [HSN']. *)

    apply SN'_ind with R. (** %{\color{blue}We proceed by induction on
                                 the hypothesis}%
                                 [HSN']. %{\color{blue} This
                                 corresponds to the application of the
                                 induction principle}% [SN'_ind]
                                 %{\color{blue} as explained above, in
                                 which reduction relation}% [red]
                                 %{\color{blue} is instantiated with}%
                                 [R]%{\color{blue}, and predicate}%
                                 [P]%{\color{blue}, with}% ([SN
                                 R]). *)
    
    + intros a HredSN' HredSN. (** %{\color{blue} We call}%
                                       [HredSN'] (%{\color{blue}
                                       resp.}% [HredSN])
                                       %{\color{blue}the hypothesis}%
                                       [forall b : A, R a b -> SN' R b]
                                       (%{\color{blue} resp.}% [forall b :
                                       A, R a b -> SN R b]). *)
      
      clear HredSN' HSN'. (** %{\color{blue} Essentially, we need to
                                    prove the predicate}% ([SN R])
                                    %{\color{blue}is patriarchal,
                                    which can be proved from the
                                    hypothesis}%
                                    [HredSN]%{\color{blue}. We then
                                    remove the unnecessary hypothesis
                                    depending on}% [SN']. *)
      
      unfold SN in *. (** %{\color{blue}Unfolding the definition}%
                          [SN]%{\color{blue}, we need to prove that}%
                          [a] %{\color{blue}holds for all}%
                          [R]%{\color{blue}-patriarchal predicates.}%
                          *)

      intros P Hpat. (** %{\color{blue}Let}% [P] %{\color{blue}be a
                         patriarchal predicate.}% *)

      apply Hpat. (** %{\color{blue}Since}% [P] %{\color{blue}is
                      patriarchal, we have that it holds for any}%
                      [R]%{\color{blue}-reduct of}% [a]. *)

      intros b Hred. (** %{\color{blue}Let}% [b] %{\color{blue}be an}%
                         [R]%{\color{blue}-reduct of}% [a]. *)
      
      apply HredSN; assumption. (** %{\color{blue}Therefore, we have that}%
                                    [a] [R]%{\color{blue}-reduces to}%
                                    [b] %{\color{blue}and}% [P]
                                    %{\color{blue}is}%
                                    [R]%{\color{blue}-patriarchal,
                                    which is exactly the content of
                                    the hypothesis}% [HredSN]. *)
      
    + assumption. (** %{\color{blue}We conclude stating}% ([SN' R
                      t])%{\color{blue}, which is an initial
                      hypothesis.}% *)
    
  - intro HSN. (** %{\color{blue} On the other direction, suppose
                   that}% ([SN r t])%{\color{blue}, and call this
                   hypothesis}% [HSN]. %{\color{blue}We need to prove
                   that}% ([SN' R]) %{\color{blue}is}%
                   [R]%{\color{blue}-patriarchal.}% *)
    
    apply HSN. (** %{\color{blue}Now we can instantiate the
                   universally quantified predicate of the definition
                   of}% [SN] %{\color{blue}with}% ([SN'
                   R])%{\color{blue}. Proving that}% ([SN' R])
                   %{\color{blue}is patriarchal corresponds to prove
                   that}% [forall x : A, (forall y : A, R x y -> SN' R y) -> SN' R
                   x]. *)

    intros x HSN'. (** %{\color{blue}So, let}% [x] %{\color{blue} be
                          an arbitrary element such that}% ([SN' R])
                          %{\color{blue}holds for every}%
                          [R]%{\color{blue}-reduct of}%
                          [x]%{\color{blue}. Call this fact}%
                          [HSN']. *)

    apply sn_acc; assumption. (** %{\color{blue}Now, a proof of}%
                                  ([SN' R x])
                                  %{\color{blue}corresponds, by
                                  definition, to a proof that every}%
                                  [R]%{\color{blue}-reduct}% [y]
                                  %{\color{blue}of}% [x]
                                  %{\color{blue}is such that}% ([SN' R
                                  y]) %{\color{blue}, which is exactly
                                  the content of the hypothesis}%
                                  [HSN']. *)
Qed.

(** ** The Main Theorem *)

(** In this section, we present the formal proof main steps of the
    Modular Strong Normalisation Theorem, including some results the
    proof depends. The first result concerns the composition of weakly
    and strongly simulated reductions. More precisely, if a reduction
    relation [redB] weakly simulates a reduction relation [redA1]
    through [R] and strongly simulates the reduction relation [redA2]
    through [R], then [redB] strongly simulates the composition
    ([redA1 # redA2]) through [R]. Although intuitively clear, the
    proof requires a large amount of details we decided to explain. *)

Lemma WeakStrongSimul {A B} (redA1 redA2:Red A)(redB:Red B)(R:Rel A B):
  WeakSimul redA1 redB R ->
  StrongSimul redA2 redB R ->
  StrongSimul (redA1 # redA2) redB R.
Proof.
  intros Hweak Hstrong. (** %{\color{blue}Let}% [Hweak]
                            (%{\color{blue}resp.}% [Hstrong])
                            %{\color{blue}be the statement that}%
                            [redB] %{\color{blue}weakly
                            (resp. strongly) simulates the reduction
                            relation}% [redA1] (%{\color{blue} resp.}%
                            [redA2]) %{\color{blue}through}% [R]. *)
  
  unfold StrongSimul in *. (** %{\color{blue}By definition of strong
                               simulation, the composition}% [(inverse R)
                               # redA2] %{\color{blue}is a subrelation
                               of the transitive closure of}% [redB]
                               %{\color{blue}composed with}%
                               [(inverse R)].  %{\color{blue}In addition,
                               we have to prove that the composition}%
                               [(inverse R) # (redA1 # redA2)]
                               %{\color{blue}is a subrelation of the
                               transitive closure of}% [redB]
                               %{\color{blue}composed with}%
                               [(inverse R)]. *)
  
  unfold WeakSimul in *. (** %{\color{blue}By definition of weak
                             simulation the composition}% [(inverse R) #
                             redA1] %{\color{blue}is a subrelation of
                             the transitive reflexive closure of}%
                             [redB] %{\color{blue}composed with}%
                             (inverse R). *)
  
  unfold Sub in *. (** %{\color{blue}Therefore, every pair of
                       elements}% [a] %{\color{blue}and}% [b]
                       %{\color{blue}that are related by}% [(inverse R) #
                       (redA1 # redA2)] %{\color{blue}is also related
                       by}% [trans redB # (inverse R)]. *)
  
  intros a b Hcomp. (** %{\color{blue}Let}% [Hcomp] %{\color{blue}be
                        the hypothesis}% [(inverse R # (redA1 #
                        redA2)) a b]%{\color{blue}, i.e.}% [a]
                        %{\color{blue}and}% [b] %{\color{blue}are
                        related by the relation}% [(inverse R) # (redA1 #
                        redA2)]. *)
  
  inversion Hcomp; subst. clear Hcomp. (** %{\color{blue}From the
                                           hypothesis}%
                                           [Hcomp] %{\color{blue} there exists an
                                           element}% [b0]
                                           %{\color{blue}such that}%
                                           [(inverse R) a b0]
                                           %{\color{blue}, call this
                                           fact}% [H]%{\color{blue},
                                           and}% [(redA1 # redA2) b0
                                           b]%{\color{blue}, which we
                                           call}% [H0]. *)
  
  inversion H0; subst. clear H0. (** %{\color{blue}Similarly, the
                                     hypothesis}% [H0] %{\color{blue}
                                     means there exists an element}%
                                     [b1] %{\color{blue}such that}%
                                     [RedA1 b0 b1] %{\color{blue}and}%
                                     [redA2 b1 b]. *)
  
  assert (H': (inverse R # redA1) a b1).
  { apply compose with b0; assumption. } (** %{\color{blue}Therefore,
                                             from}% [H]
                                             %{\color{blue}and}% [H1]
                                             %{\color{blue}we get}%
                                             [((inverse R) # redA1) a
                                             b1]%{\color{blue}, call
                                             this fact}% [H']. *)
  
  apply Hweak in H'. (** %{\color{blue}Since the reduction relation}%
                         [redA1] %{\color{blue}is weakly simulated
                         by}% [redB] %{\color{blue}through}%
                         [R]%{\color{blue}, we get}% [((inverse R) #
                         redA1) a b1] *)
  
  inversion H'; subst. clear H'. (** %{\color{blue}Which, in turn
                                     means that there exists an
                                     element}% [b2] %{\color{blue}such
                                     that}% [refltrans redB a b2]
                                     %{\color{blue}and}% [(inverse R) b2
                                     b1] *)
  
  induction H0. (** %{\color{blue}We proceed by induction on the
                    reflexive transitive closure of}%
                    [redB]%{\color{blue}, i.e. on the hypothesis}%
                    [refltrans redB a b2]. %{\color{blue}The proof is
                    split in two cases corresponding to the two
                    constructors of the definition of the reflexive
                    transitive closure of a reduction relation. The
                    first case corresponds to the reflexive
                    constructor.}% *)
  
  - apply Hstrong. (** %{\color{blue}The strong simulation hypothesis
                       allows us to prove}% [(trans redB # (inverse R))
                       a b] %{\color{blue}by showing that}% [((inverse R)
                       # redA2) a b]. *)
      
    apply compose with b1; assumption. (** %{\color{blue} This
                                           composition can be
                                           constructed with the
                                           element}% [b1]
                                           %{\color{blue}given
                                           above}%. *)
    
  - assert (Hcomp: (trans redB # inverse R) b2 b).
    { apply Hstrong. apply compose with b1; assumption. }
    (** %{\color{blue}The second case of the induction, is proved by
        first observing that}% [(trans redB # (inverse R)) b2 b]
        %{\color{blue}, which can be proved from the strong simulation
        hypothesis}% [Hstrong] %{\color{blue}and noting that}% [b2]
        %{\color{blue}is related to}% [b] %{\color{blue}through the
        relation}% [(inverse R) # redA2] %{\color{blue}via the element}%
        [b1] %{\color{blue}above.}% *)
    
    inversion Hcomp; subst. clear Hcomp. (** %{\color{blue}Therefore,
                                             there exits an element}%
                                             [b3] %{\color{blue}such
                                             that}% [trans redB b2 b3]
                                             %{\color{blue}and}%
                                             [(inverse R) b3 b]. *)
    
    apply compose with b3. (** %{\color{blue}Hence, the element}% [a]
    %{\color{blue}is related to}% [b] %{\color{blue}through}% [b3]
    %{\color{blue}because}% *)

    + apply tailtransit with b2; assumption. (** [a] %{\color{blue}is
                                                 related to}% [b3]
                                                 %{\color{blue}through
                                                 the relation}% [trans
                                                 redB]
                                                 %{\color{blue}via the
                                                 element}% [b2]. *)

    + assumption. (** %{\color{blue}And}% [b3] %{\color{blue}is
                                                 related to}% [b]
                                                 %{\color{blue}through}%
                                                 [(inverse R)]. *)
Qed.

(* begin hide *)
Lemma refltailtransit {A red}: forall (b a c:A),
    refltrans red a b -> refltrans red b c -> refltrans red a c.
Proof.
  intros b a c H1 H2.
  induction H1.
  - assumption.
  - inversion H2; subst.
    + constructor; assumption.
    + constructor.
      apply (tailtransit b); assumption.
Qed. 

Lemma SimulWeakTrans {A B} (redA: Red A) (redB: Red B) (R: Rel A B)
  : WeakSimul redA redB R -> WeakSimul (trans redA) redB R.
Proof.
  unfold WeakSimul.
  unfold Sub in *.
  intros Hip a b H.
  inversion H; subst.
  clear H.
  generalize dependent a.
  induction H1.
  - intros a' H'.
    apply Hip.
    apply compose with a; assumption.
  - intros a' H'.
    assert (H'': (inverse R # redA) a' b).
    { apply compose with a; assumption. }
    apply Hip in H''. clear H'.
    inversion H''; subst.
    apply IHtrans in H2.
    inversion H2; subst.
    apply compose with b1.
    + apply (refltailtransit b0); assumption.
    + assumption.
Qed.

Lemma SimulWeakReflTrans {A B} (redA: Red A) (redB: Red B) (R: Rel A B)
  : WeakSimul redA redB R -> WeakSimul (refltrans redA) redB R.
Proof.
  unfold WeakSimul.
  unfold Sub in *.
  intros Hip a b H.
  inversion H; subst. clear H.
  generalize dependent a.
  induction H1.
  - intros a' H'.
    apply compose with a'.
    + apply reflex.
    + assumption.      
  - intros a' Hinv.
    assert (HWTrans: WeakSimul (trans redA) redB R).
    apply SimulWeakTrans.
    unfold WeakSimul.
    unfold Sub.
    apply Hip.
    apply HWTrans.
    apply compose with a; assumption.
Qed.  
(* end hide *)

(** The next result is a consequence of lemma [WeakStrongSimul]. In
    fact, it is easy to prove that if [redA] is weakly simulated by
    [redB] through [R] then so is its reflexive transitive
    closure(cf. lemma [SimulWeakReflTrans] in the formalisation source
    code). Then, by lemma [WeakStrongSimul] the composition of
    [(refltrans redA)] with [red'A], a strongly simulated reduction
    relation, is also strongly simulated by [redB] through [R]. *)

Corollary RCSimul {A B} {redA red'A: Red A} {redB: Red B} {R: Rel A B}:
  (StrongSimul red'A redB R) ->
  (WeakSimul redA redB R) ->
  (StrongSimul ((refltrans redA) # red'A) redB R).
(* begin hide *)
Proof.
  intros Hst Hwk.
  assert (Hrfl:  WeakSimul (refltrans redA) redB R).
  {
    apply SimulWeakReflTrans; assumption.
  }
  clear Hwk.
  apply WeakStrongSimul; assumption.
Qed.
(* end hide *)

(** The second result is known as strong normalisation by simulation,
    proved in %\cite{lengrand-nt}%. The theorem, here called
    [SNbySimul], states that if a reduction relation over [A], say
    [redA], is strongly simulated by a reduction relation over [B],
    say [redB], through [R] then the pre-image of any element that
    satisfies the predicate ([SN' redB]) also satisfies ([SN'
    redA]). A more detailed explanation of this result can be found in
    %\cite{LengrandPhD}%. *)

Theorem SNbySimul {A B} {redA: Red A} {redB: Red B} {R: Rel A B}:
  StrongSimul redA redB R ->
  forall a, Image (inverse R) (SN' redB) a -> SN' redA a.
(* begin hide *)
Proof.
  intros Hstrong a Hinv.
  inversion Hinv; subst. clear Hinv.
  inversion H0; subst. clear H0. 
  assert (HSNTrans: SN' (trans redB) a0).
  {
    apply SNTrans; assumption.
  }  
  clear H.
  generalize dependent a.
  induction HSNTrans.
  unfold StrongSimul in Hstrong.
  unfold Sub in Hstrong.
  intros a' HR.
  apply sn_acc.
  intros a'' Hred.
  assert (Hcomp: (inverse R # redA) a a'').
  {
    apply compose with a'.
    apply inverseof; assumption.
    assumption.
  }
  apply Hstrong in Hcomp.
  inversion Hcomp; subst. clear Hcomp.
  apply H0 with b.
  - assumption.
  - inversion H2; subst. clear H2.
    assumption.
Qed.

Inductive Id {A} : Red A :=
  identity: forall a:A, Id a a.

Lemma HId {A} (red: Red A): forall a, SN' red a <-> Image (inverse Id) (SN' red) a.
Proof.
  split.
  - intros H.
    apply image with a.
    + assumption.
    + apply inverseof. apply identity.
  - intros H.
    inversion H; subst. clear H.
    inversion H1; subst. clear H1.
    inversion H; subst. clear H.
    assumption.
Qed.
(* end hide *)

(** The union of two reduction relations is inductively defined as
    follows: *)

Inductive union {A} (red1 red2: Red A) : Red A :=
 | union_left: forall a b,  red1 a b -> union red1 red2 a b
 | union_right: forall a b,  red2 a b -> union red1 red2 a b.

Notation "R1 !_! R2" := (union R1 R2) (at level 40).
(* begin hide *)
Lemma UnionStrongSimul {A} {redA red'A: Red A}:
  StrongSimul redA (redA !_! red'A) Id.
Proof.
  unfold StrongSimul.
  unfold Sub.
  intros a b HredA.
  inversion HredA; subst. clear HredA.
  inversion H; subst. clear H.
  inversion H1; subst. clear H1.
  apply compose with b.
  - apply singl.
    apply union_left; assumption.
  - apply inverseof. apply identity.
Qed.

Lemma UnionReflStrongSimul {A} {redA red'A: Red A}:
  StrongSimul ((refltrans redA) # red'A) (redA !_! red'A) Id.
Proof.
  unfold StrongSimul.
  unfold Sub.
  intros a b H.
  inversion H; subst. clear H.
  inversion H1; subst. clear H1.
  generalize dependent a.
  generalize dependent b.
  induction H.
  - intros.
    apply compose with b.
    + constructor.
      inversion H0; subst. clear H0.
      inversion H; subst. clear H.
      constructor; assumption.
    + apply inverseof. apply identity.
  - intros.
    generalize dependent b0.
    inversion H0; subst. clear H0.
    inversion H1; subst. clear H1.
    induction H.
    + intros.
      apply compose with b0.
      * apply transit with b.
        ** constructor; assumption.
        ** constructor; constructor; assumption.
      * apply inverseof. apply identity.
    + intros b0 Hred'A.
      assert (Hone: (redA !_! red'A) a b).
      {
        constructor; assumption.
      }
      apply compose with b0.
      * apply transit with b.
        ** assumption.
        ** apply IHtrans in Hred'A.
           inversion Hred'A; subst. clear Hred'A.
           inversion H2; subst. clear H2.
           inversion H3; subst. clear H3.
           assumption.
      * apply inverseof. apply identity.
Qed.
(* end hide *)

(** The next lemma shows that predicate [SN' (redA !_! red'A)] is
    patriarchal w.r.t. the reduction relation [((refltrans redA) #
    red'A)]. *)

Lemma inclUnion {A} {redA red'A: Red A}:
  forall a, (SN' redA a) ->
       (forall b, (((refltrans redA) # red'A) a b) ->
             SN' (redA !_! red'A) b) ->
       (SN' (redA !_! red'A) a).
Proof.
  intros a HSN. (** %{\color{blue}Given an arbitrary element}%
                    [a]%{\color{blue}, let}% [HSN] %{\color{blue}be
                    the hypothesis}% [SN' redA a]. *)
  
  induction HSN. clear H. (** %{\color{blue}We proceed by induction
                              on}% [HSN]%{\color{blue}. This means
                              we can assume that our goal holds
                              for all one-step}%
                              [redA]%{\color{blue}-reduct of}%
                              [a]%{\color{blue}. Call this
                              assumption}% [H0]. *)
  
  intro H. (** %{\color{blue}Let}% [H] %{\color{blue}be the
               hypothesis}% [forall b : A, (refltrans redA # red'A) a b ->
               SN' (redA !_!  red'A) b] *)
  
  apply sn_acc. (** %{\color{blue}Applying the definition}% [SN']
  %{\color{blue}to our goal}% [SN' (redA !_! red'A) a]%{\color{blue},
  means this property must also be proved for all one-step}%
  [(redA !_!  red'A)]%{\color{blue}-reduct of}% [a] %{\color{blue},
  i.e. we need to prove}% [forall b : A, (redA !_! red'A) a b -> SN' (redA
  !_! red'A) b]. *)
  
  intros b Hunion. (** %{\color{blue}Let}% [b] %{\color{blue}be a
                       one-step}% [(redA !_!
                       red'A)]%{\color{blue}-reduct of}%
                       [a]%{\color{blue}, and}% [Hunion]
                       %{\color{blue}the hypothesis}% [(redA !_!
                       red'A) a b]. *)
  
  inversion Hunion; subst. (** %{\color{blue}Since}% [(redA !_! red'A)
                               a b] %{\color{blue}we have that
                               either}% [redA a b] %{\color{blue}or}
                               [red'A a b]. *)

  - apply H0. (** %{\color{blue}In the first case the hypothesis}%
                  [H0] %{\color{blue}reduces our proof to two
                  subgoals.}% *)
    
    + assumption. (** %{\color{blue}The first one}% [redA a b]
    %{\color{blue}is closed by assumption}% *)
      
    + intros b' Hrefl. (** %{\color{blue}The second subgoal is}% [SN'
                           (redA !_! red'A) b'] %{\color{blue}where}%
                           [b'] %{\color{blue}is a}% [(redA !_!
                           red'A)]%{\color{blue}reduct of}% [b]. *)
      
      apply H. (** %{\color{blue}Applying the hypothesis}%
                   [H]%{\color{blue}, we need to prove}% [(refltrans
                   redA # red'A) a b']. *)

      inversion Hrefl; subst. (** %{\color{blue}From the composition
                                  expressed in hypothesis}%
                                  [Hrefl]%{\color{blue}, we have that
                                  there is an element}% [b0]
                                  %{\color{blue}such that}% [refltrans
                                  redA b b0] %{\color{blue}and}%
                                  [red'A b0 b']. *)

      apply compose with b0. (** %{\color{blue}Similarly, our goal can
                                 be decomposed with the above
                                 element}% [b0]%{\color{blue}, leading
                                 to two subcases:}% *)

      * apply refltailtransit with b. (** %{\color{blue}The first
                                          subcase}% [refltrans redA a
                                          b0] %{\color{blue}is proved
                                          from hypothesis}% [redA a b]
                                          %{\color{blue}and}%
                                          [refltrans redA b b0]. *)
        
        ** apply atleast1.
           apply singl; assumption.
        ** assumption.
      * assumption.
  - apply H.
    apply compose with a.
    + apply reflex.
    + assumption. (** %{\color{blue}The second subcase is closed by
                      assumption.}% *)
Qed.

(* begin hide *)
Lemma stabComp {A} {redA: Red A}: forall a,
    SN' redA a -> forall b, refltrans redA a b -> SN' redA b.
Proof.
  intros a HSN b Hrefl.
  generalize dependent HSN.
  induction Hrefl.
  - trivial.
  - induction H.
    + intros HSN.      
      apply SNstable with a; assumption.
    + intros HSN.
      apply IHtrans.
      apply SNstable with a; assumption. 
Qed.
(* end hide *)

(** The following lemma states the conditions for a union of two
    reduction relations [redA] and [red'A] to be strongly
    normalising. It corresponds to one direction of the bi-implication
    of lemma [SNunion] below. *)

Lemma SNinclUnion {A} {redA red'A: Red A}: (forall b, SN' redA b ->
                               forall c, red'A b c -> SN' redA c) ->
                   (forall a, (SN' ((refltrans redA) # red'A) a) ->
                 (SN' redA a) -> (SN' (redA !_! red'A) a)).
Proof.
  intros Hstable a HSNcomp. (** %{\color{blue} Assume the stability
                               of}% [SN' redA]
                               %{\color{blue}w.r.t. the reduction
                               relation}% [red'A]%{\color{blue}, and
                               call this
                               hypothesis}% [Hstable]%{\color{blue}. In addition, call}%
                               [HSNcomp] %{\color{blue}the
                               assumption}% [(SN' ((refltrans redA) #
                               red'A) a)]%{\color{blue}, for an
                               arbitrary element}% [a]. *)
  
  induction HSNcomp. (** %{\color{blue}We proceed by induction on the
                         hypothesis}%
                         [HSNcomp]. %{\color{blue}Therefore, we need
                         to prove our goal, assuming that it holds for
                         all}% [(refltrans redA #
                         red'A)]%{\color{blue}-reduct of}%
                         [a]%{\color{blue}, and we call}% [H0]
                         %{\color{blue}this fact}%. *)
  
  intros HSN. (** %{\color{blue}Let}% [HSN] %{\color{blue}be the
                  hypothesis}% [SN' redA a]. *)

  apply inclUnion. (** %{\color{blue}By lemma}% [SNinclUnion]
  %{\color{blue} we can prove}% [SN' (redA !_!  red'A) a]
  %{\color{blue}if}% [SN' redA a] %{\color{blue}and}% [(forall b : A,
  (refltrans redA # red'A) a b -> SN' (redA !_! red'A) b)]. *)

  - assumption. (** %{\color{blue}The first fact is the hypothesis}%
                    [HSN] *)
    
  - intros b Hcomp.    
    apply H0. 
    + assumption. (** %{\color{blue}The second fact comes partially
                   from the hypothesis}% [H0]%{\color{blue}, but we
                   also have to prove}% [SN' redA b]. *)
      
    + inversion Hcomp; subst. clear Hcomp.
      assert(H': SN' redA b0).
      {
        apply stabComp with a; assumption.
      }
      apply Hstable with b0; assumption. (** %{\color{blue}We conclude
                                             using the fact that}%
                                             [SN' redA]
                                             %{\color{blue}is stable
                                             w.r.t}% [red'A]. *)

Qed.

(** %\noindent% The next lemma gives a characterisation of the
    predicate [SN' (redA !_! red'A)]. Another important property used
    is called %{\it stability}%. We say a predicate [P] is stable
    w.r.t. the reduction relation [R] when, for all [a] and [b] such
    that [R a b], [P a] implies [P b]. Under hypothesis of stability
    of [(SN' redA)] w.r.t. the reduction relation [red'A], predicate
    [SN' (redA !_!  red'A)] can then be decomposed as the conjunction
    [(SN' ((refltrans redA) # red'A)) /\ (SN' redA)]: *)

Lemma SNunion {A} {redA red'A: Red A}:
  (forall b, SN' redA b -> forall c, red'A b c -> SN' redA c) ->
  forall a, (SN' (redA !_! red'A) a) <->
       (SN' ((refltrans redA) # red'A) a) /\ ((SN' redA) a).
Proof. 
  intros Hstable a; split. (** %{\color{blue}The proof
  is as follows: Suppose that}% ([SN' redA]) %{\color{blue}is stable
  w.r.t. the reduction relation}% [red'A]%{\color{blue}. Call this
  hypothesis}% [Hstable]. %{\color{blue}Split the bi-implication in
  two cases:}% *)
  
  - intro HSN. split. (** %{\color{blue}In the first case, call}%
                          [HSN] %{\color{blue}the hypothesis}% 

                          [SN' (redA !_! red'A) a]. *)
    
    + apply HId in HSN.
      generalize dependent HSN. (** %{\color{blue}In order use lemma}%
                                    [SNbySimul]%{\color{blue}, we
                                    rewrite}% [SN' (redA !_! red'A) a]
                                    %{\color{blue}as}% [Image (inverse
                                    Id) (SN' (redA !_! red'A)) a]. *)

      apply SNbySimul. (** %{\color{blue}By lemma}%
                           [SNbySimul]%{\color{blue}, we then need to
                           prove that}% [(refltrans redA # red'A)]
                           %{\color{blue}is strongly simulated by}%
                           [(redA !_! red'A)] %{\color{blue}through
                           some relation}%. *)

      apply UnionReflStrongSimul. (** %{\color{blue}This fact is
                                      proved in lemma}%
                                      [UnionReflStrongSimul]
                                      %{\color{blue}using the identity
                                      relation over}%
                                      [A]%{\color{blue}, that is}%
                                      [(refltrans redA # red'A)]
                                      %{\color{blue}is strongly
                                      simulated by}% [(redA !_!
                                      red'A)] %{\color{blue}through}%
                                      [Id].  *)

    + apply HId in HSN.
      generalize dependent HSN. (** %{\color{blue}The second component
                                    of the conjunction requires a
                                    similar strategy to use lemma}%
                                    [SNbySimul]. *)
      
      apply SNbySimul.
      apply UnionStrongSimul. (** %{\color{blue} We conclude using
                                   the fact that a reduction relation
                                   is strongly simulated by the union
                                   of itself with any other reduction
                                   relation through the identity
                                   relation, formalised
                                   in lemma}% [UnionStrongSimul]. *)

  - intro Hand.
    destruct Hand as [Hcomp HredA]. (** %{\color{blue}On the other
                                                    direction, call}%
                                                    [Hcomp]
                                                    %{\color{blue}(resp.}%
                                                    [HredA]
                                                    %{\color{blue})
                                                    the hypothesis}%
                                                    [SN' (refltrans
                                                    redA # red'A) a]
                                                    %{\color{blue}(resp.}%
                                                    [SN' redA
                                                    a]%{\color{blue})}%. *)

    generalize dependent HredA.
    generalize dependent a.
    apply SNinclUnion; assumption. (** %{\color{blue}We conclude
                                       that}% [SN' (redA !_! red'A) a]
                                       %{\color{blue}by lemma}%
                                       [SNinclUnion]. *)

Qed.

(** The Modular Strong Normalisation Theorem, here called
    [ModStrNorm], is specified in Coq's syntax as follows: *)

Theorem ModStrNorm {A B: Type} {redA red'A: Red A}
        {redB: Red B} {R: Rel A B}:
  (StrongSimul red'A redB R) ->
  (WeakSimul redA redB R) ->
  (forall b: A, SN' redA b) -> forall a:A, Image (inverse R) (SN' redB) a ->
                                   SN' (redA !_! red'A) a.
Proof.
  (** %{\color{blue} Let}% [A] %{\color{blue}and}% [B]
  %{\color{blue}be types}%, [redA] %{\color{blue}and}% [red'A]
  %{\color{blue}be two reduction relations over}% [A]%{\color{blue},}%
  [redB] %{\color{blue}a reduction relation over}% [B]%{\color{blue},
  and}% [R] %{\color{blue}a relation from}% [A] %{\color{blue}to}%
  [B]. *)
  
  intros Hstrong Hweak HSN a HImage. (** %{\color{blue}Assume that}%
                                         [red'A] %{\color{blue}is
                                         strongly simulated by}%
                                         [redB]
                                         %{\color{blue}through}% [R]
                                         %{\color{blue}(hypothesis}%
                                         [Hstrong]%{\color{blue}),
                                         that}% [redA]
                                         %{\color{blue}is weakly
                                         simulated by}% [redB]
                                         %{\color{blue}through}% [R]
                                         %{\color{blue}(hypothesis}%
                                         [Hweak]%{\color{blue}),
                                         that}% [SN' redA b]
                                         %{\color{blue}holds for
                                         every}% [b:A]
                                         %{\color{blue}(hypothesis}%
                                         [HSN]%{\color{blue}), and
                                         let}% [a:A] %{\color{blue}be
                                         an arbitrary element in the
                                         inverse image of}% [SN'
                                         redB]
                                         %{\color{blue}(hypothesis}%
                                         [HImage]%{\color{blue}). We
                                         need to prove that}% [SN'
                                         (redA !_! red'A)
                                         a]%{\color{blue}. By lemma}%
                                         [SNunion] %{\color{blue}this
                                         is equivalent to prove that}%
                                         [SN' (refltrans redA #
                                         red'A) a /\ SN' redA
                                         a]%{\color{blue}, under the
                                         hypothesis of stability of}%
                                         [SN' redA]
                                         %{\color{blue}w.r.t. the
                                         reduction relation}%
                                         [red'A]%{\color{blue}, which
                                         is trivially obtained from
                                         hypothesis}% [HSN]
                                         %{\color{blue}since every
                                         element of}% [A]
                                         %{\color{blue}satisfies the
                                         predicate}% [SN' redA]. *)

  assert(Hsplit: SN' (redA !_! red'A) a <->
                    SN' (refltrans redA # red'A) a /\ SN' redA a).
  {
    apply SNunion.
    intros b HSN' c Hred.
    apply HSN.
  }
  destruct Hsplit as [H Hunion]; clear H. (** %{\color{blue}Note that
                                              just one direction of
                                              this equivalence is
                                              needed.}% *)

  apply Hunion; split. (** %{\color{blue}The proof of this conjunction
                           is split in two parts. We prove that}%
                           [SN' (refltrans redA # red'A)
                           a]%{\color{blue}, which can be proved by
                           lemma}% [SNbySimul]%{\color{blue}, as long
                           as}% [(refltrans redA # red'A)]
                           %{\color{blue}is strongly simulated by}%
                           [redB] %{\color{blue}through}% [R]. *)

  - generalize dependent HImage.
    apply SNbySimul.
    apply RCSimul; assumption. (** %{\color{blue}Now we need to
                                     prove that}% [(refltrans redA #
                                     red'A)] %{\color{blue}is strongly
                                     simulated by}% [redB]
                                     %{\color{blue}through}%
                                     [R]%{\color{blue}, which is
                                     achieved by lemma}% [RCSimul]. *)

  - apply HSN. (** %{\color{blue}The second part of the conjunction
                   corresponds to the hypothesis}%
                   [HSN]%{\color{blue}, and we conclude.}% *)

Qed.
(* end hide *)

(** * Conclusion *)

(** In this work we presented a constructive formalisation of the
    Modular Strong Normalisation Theorem in the Coq Proof
    Assistant. The proof is constructive in the sense that it does not
    use the principle of excluded middle or any other classical rule,
    such as proof by contradiction. The constructive approach is not
    the standard way to prove termination of a reduction relation. In
    fact, the usual technique to prove termination of a reduction
    relation is showing that it does not have infinite reduction
    sequences through a proof by contradiction
    (cf. %\cite{terese03,BN98}%). For instance, a classical proof of
    the Modular Strong Normalisation Theorem is presented at
    %\cite{kes09}%. Constructive proofs are usually more difficult and
    elaborate than classical ones, but the former are preferred in the
    context of Computer Science.

    The Modular Strong Normalisation Theorem is an abstract result
    that states the conditions for the union of two reduction
    relations to preserve strong normalisation (PSN). It is a
    non-trivial result in abstract reduction systems that uses the
    well-known technique of termination by simulation, i.e. the
    termination of a reduction system is obtained by simulating its
    steps via another reduction relation known to be terminating. The
    theorem is, for instance, applied in %\cite{kes09}% to establish
    the PSN property of a calculus with explicit substitutions.

    The proofs developed in this formalisation follow the ideas
    presented in %\cite{LengrandPhD}%, where a theory of constructive
    normalisation is developed. This theory is based on a different
    definition of strong normalisation. Instead of using Lengrand's
    definition, we used a more standard inductive definition of strong
    normalisation (cf. %\cite{kes09,LengrandPhD,Raams-phd}%). A formal
    proof of the equivalence between these definitions of strong
    normalisation is also provided. In this way, we have a simpler and
    straithforward formalisation of the constructive normalisation
    theory. *)

    (*
       
       An interesting application of the Modular Strong Normalisation
       Theorem is given in %\cite{kes09}% to establish the termination
       of a calculus with explicit substitutions. Termination of
       calculus with explicit substitutions is a challenging problem
       that...

     - This is part of a bigger project.  OK Compatible versions of
     - Coq ? 8.??  General explanation of how to compile and generate
     - documentation. (Github) 

     *)
