(** * Introduction *)

(** It is well known that termination is not a modular property for
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
    meta-operation in the $\lambda$-calculus. In other words, for the 
    rule $(\lambda{x}. M) N \to_{\beta} M [x:=N]$, $M [x:=N]$ represents
    a term in such a calculus where the substitution is defined through a 
    small-step semantics. PSN property in this context
    guarantees that any strongly normalising term, i.e. terminating,
    in the $\lambda$-calculus is also strongly normalising in the
    calculus with explicit substitutions.
 
    The Modular Strong Normalisation Theorem states the conditions for
    the union of two reduction relations over a set $A$ to be PSN
    through its relation of simulation to a reduction relation over
    some set $B$ (cf. %~\cite{LengrandPhD,kes09}%). In particular,
    when the reduction relation over $B$ is terminating 
    %\dan{and the simulation relation is complete}%, the theorem
    guarantees that both reduction over $A$ are terminating and so its
    union, i.e. that termination is modular.

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
    normalisation, is already formalised in Coq %\footnote{
    \scriptsize
    \url{http://www.lix.polytechnique.fr/~lengrand/Work/HDR/Coq/First-order/NormalisationTheory.v}}%. In
    a certain sense, this work can be seen as a non-trivial expansion of
    the normalisation theory formalised by Lengrand. In fact, the
    strong normalisation property defined in %\cite{LengrandPhD}% uses
    a specialized inductive principle that should hold for all
    predicate, i.e. through a second order formula. On the other hand,
    in this work we use only the standard inductive definition of the
    strong normalisation property
    (cf. %\cite{kes09,LengrandPhD,Raams-phd}%), and we also prove the
    equivalence between these definitions. In this way, we understand
    that we achieved a simpler and easier to follow formalisation. The
    proof of the Modular Strong Normalisation Theorem follows the
    ideas in Lengrand's PhD thesis, but to the best of our knowledge,
    this is the first formalisation of this theorem.

    This paper is built up from a Coq script where some code is hidden
    for the sake of clarity of this document. All the files concerning
    this work are freely available in the repository %{\tt
    https://github.com/flaviodemoura/MSNorm}%. The contributions of
    this work can be summarised as follows:

    %\begin{itemize}

      \item A constructive proof of the Modular Strong Normalisation
            Theorem;

      \item An equivalence proof between Lengrand's definition of
            strong normalisation and the standard inductive definition
            of strong normalisation;

      \item

     \end{itemize}% *)

(** * The Modular Strong Normalisation Theorem *)

(** In this section, we present the Modular Strong Normalisation
    Theorem whose formalisation will be detailed in the next
    section. This is an abstract theorem about termination of
    reduction relations through the well known simulation technique
    %\cite{BN98}%. In order to fix notation, let [A] and [B] be
    sets. A relation from [A] to [B] is a subset of $A\times B$. If
    $R$ is a relation from [A] to [B] then we write $R\ a\ b$ instead
    of $(a,b) \in R$, and in this case, we say that $a$ %{\it
    reduces}% to $b$. Using arrows to denote relations and $\to$ being
    a relation from [A] to [B] then $\leftarrow$ denotes the inverse
    relation from [B] to [A]. If $\to_1$ is a relation from $A$ to
    $B$, and $\to_2$ is a relation from $B$ to $C$ then the
    composition of $\to_1$ with $\to_2$, written $\to_1\cdot \to_2$,
    is a relation from $A$ to $C$. A relation from a set to itself is
    a %{\it reduction relation over a set}%, i.e. a reduction relation
    over A is a subset of $A\times A$. If $\to_A$ is a reduction
    relation over $A$, then a %{\it reduction sequence}% is a sequence
    of the form $a_0 \to_A a_1 \to_A a_2 \to_A \ldots$ A reduction
    $a_0 \to_A a_1 \to_A a_2 \to_A \ldots \to_A a_n\ (n\geq 0)$ is a
    $n$-step reduction from $a_0$. A reduction is finite if it is a
    $n$-step reduction for some $n \in \mathbb{N}$, and infinite
    otherwise. We write $\to_A^+$ (resp. $\to_A^*$) for the transitive
    (resp. reflexive transitive) closure of $\to_A$.
    
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
    strong and weak simulation. In the following definitions $A$ and
    $B$ are arbitrary sets:

    %\begin{definition}\label{def:sws} Let $\to$ be a relation from
    $A$ to $B$, $\to_A$ be a reduction relation over $A$ and $\to_B$
    be a reduction relation over $B$. The reduction relation $\to_B$
    {\it strongly} (resp. {\it weakly}) simulates $\to_A$ through
    $\to$ if $(\leftarrow \cdot \to_A) \subseteq (\to_B^+ \cdot
    \leftarrow)$ (resp. $(\leftarrow \cdot \to_A) \subseteq (\to_B^*
    \cdot \leftarrow)$).

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
 
    \draw[<-] (a1.east) .. controls +(up:0cm) and +(left:1cm)
    .. node[above,sloped] {} (b1.west);

    \draw[<-,red] (a2.east) .. controls +(up:0cm) and +(left:1cm)
    .. node[above,sloped] {} (b2.west);

    \draw[->] (a1.south) .. controls +(up:0cm) and +(left:0cm)
    .. node[left] {\scriptsize A} (a2.north);

    \draw[->,red] (b1.south) .. controls +(up:0cm) and +(left:0cm)
    .. node[left] {\scriptsize B} (b2.north);

    \draw[ultra thick,myblue] (12,0) circle [x radius=1.5cm, y
                     radius=4cm] (18,0) circle [x radius=1.5cm, y
                     radius=4cm];
                     
    \node[font=\color{myblue}\Large\bfseries] at (12,5) {A};

    \node[font=\color{myblue}\Large\bfseries] at (18,5) {B};
 
    \node (a1) at (12,2) {a}; \node (a2) at (12,0) {a'};
 
    \node[circle] (b1) at (18,2) {b}; \node[circle] (b2) at (18,-2)
    {b'};

    \node[above= 0.0001cm of b2] (aux) {}; \node[left= 0.000002cm of
    aux] (aux2) {}; \node[right= 0.000002cm of aux2, red] (aux3) {*};


    \draw[<-] (a1.east) .. controls +(up:0cm) and +(left:1cm)
    .. node[above,sloped] {} (b1.west);

    \draw[<-,red] (a2.east) .. controls +(up:0cm) and +(left:1cm)
    .. node[above,sloped] {} (b2.west);

    \draw[->] (a1.south) .. controls +(up:0cm) and +(left:0cm)
    .. node[left] {\scriptsize A} (a2.north);

    \draw[->,red] (b1.south) .. controls +(up:0cm) and +(left:0cm)
    .. node[left] {\scriptsize B} (b2.north); \end{tikzpicture}
    \end{definition}%

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

      This proof follows the lines of
      \cite{LengrandPhD}, but using the standard definition $SN$ in
      (\ref{def:sn}). First of all, hypothesis \ref{hip:one} and
      \ref{hip:two} allow us to conclude that the composition
      $(\to_1^* \cdot \to_2)$ is strongly simulated by $\to_B$: in
      fact, from hypothesis \ref{hip:two} we have that $\to_1^*$ is
      weakly simulated by $\to_B$. In addition, the composition of two
      reduction relations that are, respectively, strongly and weakly
      simulated by the same reduction relation is strongly simulated
      by this reduction relation. Therefore, $(\to_1^* \cdot \to_2)$
      is strongly simulated by $\to_B$ through $\to$, that together
      with the fact that $a\in \leftarrow({SN\_ind}^{\to_B})$ allow us
      to conclude that $a \in {SN\_ind}^{\to_1^* \cdot \to_2}$. Now,
      from hypothesis \ref{hip:three}, we have $a \in
      {SN\_ind}^{\to_1}$, and we conclude from the fact that
      ${SN\_ind}^{\to_1^* \cdot \to_2} \cap {SN\_ind}^{\to_1} =
      {SN\_ind}^{\to_1\cup \to_2}$. *)

(** * The Formalisation *)

(** In this section we present the details of the formalisation of the
    Modular Strong Normalisation Theorem in the Coq Proof
    Assistant. The first important point is that our proof is
    constructive, i.e. it does not use classical reasoning such as the
    law of excluded middle, double negation elimination or proof by
    contradiction. In addition, no additional library other then the
    ones that are automatically loaded during Coq start up are used.

    In terms of notation, sets are coded as arbitrary types in such a
    way that the membership relation $a \in A$ ($a$ is an element of
    the set $A$) is represented as $a:A$ ($a$ has type
    $A$). (cf. %\cite{Geu09}%).

    We start with some basic definitions in order to make Coq notation
    clear. Note that this paper is written directly from a Coq script
    file, therefore, the Coq code presented is the real code of the
    formalisation. A relation from $A$ to $B$ is defined as a binary
    predicate: *)

Definition Rel (A B : Type) := A -> B -> Prop.
(** %\noindent% In this definition, [Rel] receives two types as
    argument, and return the signature of a relation from $A$ to $B$,
    i.e. the type [A -> B -> Prop]. As seen before, if $A=B$ then we have a
    %{\it reduction relation}%: *)

Definition Red (A : Type) := Rel A A.
(** Given two relations [R1] and [R2] from [A] to [B], if every pair
    of elements in [R1] is also in [R2] then we say that [R1] is a
    subrelation of [R2]: *)

Definition Sub {A B} (R1 R2: Rel A B) : Prop := forall a b, R1 a b -> R2 a b.
(** In the above definition, [A] and [B] first appear between curly
    brackets, which means that these arguments are %{\it
    implicit}%. Implicit arguments are types of polymorphic functions
    that can be inferred from the context. Therefore, [Sub] requires
    two relations as arguments, and Coq automatically infers its
    type. A more convenient notation can be easily defined for the
    objects we are constructing. In the case of the predicate [Sub],
    we define an infix notation as follows: *)

Notation "R1 <# R2" := (Sub R1 R2) (at level 50).
(** This means that now one can write [R1 <# R2] instead of [Sub R1
    R2]. In addition, in order to avoid parsing ambiguity, a
    precedence level ranging from 0 to 100 can be provided.

    Given two relations, say [red1] from [A] to [B] and [red2] from
    [B] to [C], one can build a new relation from [A] to [C] by
    composing its steps: *)

Inductive comp {A B C} (red1: Rel A B)(red2: Rel B C) : Rel A C :=
  compose: forall b a c,  red1 a b -> red2 b c -> comp red1 red2 a c.
Notation "R1 # R2" := (comp R1 R2) (at level 40).
(* begin hide *)
Arguments compose {A B C red1 red2} _ _ _ _ _ .
(* end hide *)
(** %\noindent% Note that [comp] is defined inductively. The inductive
    definition [comp] has just one constructor named [compose] that
    explicitly builds the composite relation from [A] to [C] from the
    given relations [red1] and [red2]. In addition, it is important to
    know that Coq automatically generates an inductive principle for
    every inductive definition. For instance, the natural numbers [nat]
    are inductively defined as: %\begin{alltt} Inductive nat : Set :=
    O : nat | S : nat \(\to\) nat \end{alltt}%

    %\noindent% The corresponding induction principle, named %{\tt
    nat\_ind}\footnote{The name of the automatic induction principle
    generated follows the pattern {\tt inductive\_definition\_ind},
    i.e. the name of the inductive definition followed by the string
    {\tt \_ind}.}%, is given by 
    %\begin{alltt} forall P : nat \(\to\)
    Prop, P 0 \(\to\) (forall n : nat, P n \(\to\) P (S n)) \(\to\)
    forall n : nat, P n \end{alltt}%

    So, in order to prove that a certain property %{\tt P}% holds for
    all %{\tt n: nat}%, one needs to prove that %{\tt P 0}% holds, and
    that if %{\tt P n}% holds then %{\tt P (S n)}% also holds. In
    general, if %{\it def}% is an inductive definition with
    constructors %{\tt c1}%, %{\tt c2}%, \ldots, %{\tt ck}% then in
    order to prove that a certain property %{\tt P}% holds for every
    element defined by %{\it def}% then we need to show, in a certain
    sense that, %{\tt P}% is compatible with each of its
    constructors. A more precise and detailed explanation about Coq
    induction principles can be found, for instance, in
    %\cite{CoqTeam,BC04,cpdt,Pierce:SF}%.

    The inverse of a relation from a [A] to [B] is inductively defined
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
    obtained from its transitive closure by adding reflexivity,
    i.e. by adding the fact that each element of the relation reduces
    to itself in 0 steps: *)

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

Inductive Image {A B} (R:Rel A B)(P: A -> Prop): B -> Prop
  := image: forall a b, P a -> R a b -> Image R P b.
(* begin hide *)
Arguments image {A B R P} _ _ _ _.
(* end hide *)
(** The notions of weak and strong simulation of reduction relations,
    as given in Definition %\ref{def:sws}%, are a straightforward
    translation to the Coq language: *)

Definition WeakSimul {A B} (redA: Red A) (redB: Red B) (R: Rel A B) := 
  ((inverse R) # redA) <# ((refltrans redB) # (inverse R)).

Definition StrongSimul {A B} (redA: Red A) (redB: Red B) (R: Rel A B) := 
  ((inverse R) # redA) <# ((trans redB) # (inverse R)).

(** ** Equivalence between strongly normalising definitions *)

(** In this section, we prove the equivalence between Lengrand's
    definition of strong normalisation, denoted by [SN], and the
    inductive definition (%\ref{def:sn}%) here denoted by [SN_ind]. In
    his PhD thesis, S. Lengrand develops a constructive theory of
    normalisation in the sense that it does not rely on classical
    logic. In this theory, the notion of strong normalisation for
    reduction relations is defined by a second-order formula which is
    based on a stability predicate called
    [patriarchal] (cf. %\cite{LengrandPhD,lengSNInd05}%). *)

Definition patriarchal {A} (red:Red A) (P:A -> Prop): Prop
  := forall x, (forall y, red x y -> P y) -> P x.

(** In this way, one says that a predicate over [A] is patriarchal
    w.r.t. a reduction relation over [A] if, every [red]-reduct [b:A]
    of [a] such that [P b] holds, then [P a] also holds for every
    [a:A]. Now, an element [a:A] is strongly normalising w.r.t. to the
    reduction relation [red], when [red] is patriarchal for every
    predicate [P]: *)

Definition SN {A:Type} (red:Red A) (a:A): Prop
  := forall P, patriarchal red P -> P a.
(** Most of the Coq code presented so far can be found at %{\small
         \url{http://www.lix.polytechnique.fr/~lengrand/Work/HDR/Coq/First-order/NormalisationTheory.v}}%. Nevertheless,
         the proof code is not the same because this develpment does
         not use the library [ssreflect].

    The above definition corresponds to the standard inductive
    definition of strong normalisation for reduction relations given
    in (%\ref{def:sn}%): *)

Inductive SN_ind {A:Type} (red: Red A) (a:A): Prop :=
  | sn_acc: (forall b, red a b -> SN_ind red b) -> SN_ind red a.
(** So, given an element [a:A] and a reduction relation [red] over
    [A], [a] is strongly normalising w.r.t. [red] if every one-step
    [red]-reduct [b] of [a] is strongly normalising w.r.t. [red]. This
    means that in order to conclude that [SN_ind red a], one has to
    prove first that [(forall b, red a b -> SN_ind red b)]. Note that
    formally, this inductive definition gives only one direction of
    the biconditional (%\ref{def:sn}%), but the other direction is
    straightforward: *)

Lemma SNstable {A} {red: Red A}: forall a, SN_ind red a -> forall b, red a b -> SN_ind red b.
Proof.
  intros a HSN b Hred.
  inversion HSN; clear HSN.
  apply H; assumption. 
Qed.
(** This proof does the analysis of the definition [SN_ind] in order
    to match the hypothesis [SN_ind red a], named [HSN], through the
    tactic [inversion].

    The induction principle automatically generated for [SN_ind],
    called [SN_ind_ind], is as follows:

    %\begin{alltt}

    forall (A : Type) (red : Red A) (P : A -> Prop), (forall a : A,
    (forall b : A, red a b -> SN_ind red b) -> (forall b : A, red a b
    -> P b) -> P a) -> forall a : A, SN_ind red a -> P a

    \end{alltt}%

    So, in order to conclude that a certain property holds for all
    [a:A] such that [SN_ind red a], we need to prove that [forall b : A,
    red a b -> SN_ind red b] and [(forall b : A, red a b -> P b) -> P a]. In
    the proof of theorem [SN_indEquivSN], we use this induction
    principle. *)
(* begin hide *)
Lemma SNTrans {A} {red: Red A}: forall a, SN_ind red a -> SN_ind (trans red) a.
Proof.
  induction 1 as [? IHr IHTr]; apply sn_acc; intros ? HTrans;
    induction HTrans as [ ? ? ? | ? ? ? Hr Htr IHtr].
  - auto.
  - apply IHtr; intros; auto.
    + apply IHr in Hr; destruct Hr; auto.
    + apply IHTr in Hr; destruct Hr as [Hr]; apply Hr; constructor; auto.
Qed.
(* end hide *)

(** The definitions [SN] and [SN_ind] are equivalent as stated by the
    next theorem. Since this proof is an important contribution of
    this work, we comment the proof steps in order to explain it in
    more detail. Note that the type [A] and a reduction relation [R]
    over [A] are given as implicit arguments, i.e. they are inferred
    from the context. *)

Theorem SN_indEquivSN {A:Type} {R : Red A} : forall t, SN_ind R t <-> SN R t.
Proof.
  intro t; split. (** %{\color{blue} We start by considering}% [t]
  %{\color{blue}to be an element of the set}% [A]%{\color{blue}, or
  more precisely, let}% [t] %{\color{blue} be an element of type}%
  [A]. %{\color{blue}We split the proof into two steps.}% *)
  
  - intro HSN_ind.  (** %{\color{blue} First, we need to prove that}%
    [SN_ind R t] %{\color{blue}implies}% [SN R t]. %{\color{blue}So,
    we are assuming that}% [SN_ind R t]%{\color{blue}, and we label
    this assumption as}% [HSN_ind]. *)
    
    induction HSN_ind. (** %{\color{blue}We proceed by induction on
    the hypothesis}% [HSN_ind]. %{\color{blue} This corresponds to the
    application of the induction principle}%
    [SN_ind_ind]%{\color{blue} as explained in the previous page, in
    which, the property}% [P] %{\color{blue} is instantiated with}%
    [SN R]. %{\color{blue}Therefore, we need to prove}% [SN R a],
    %{\color{blue} for a given}% [a:A]%{\color{blue}, assuming that it
    holds for all one-step}% [R]%{\color{blue}-descendents of}%
    [a]%{\color{blue}, i.e. assuming that}% [forall b : A, R a b -> SN R
    b]. %{\color{blue} Call this assumption}% [H0]. %{\color{blue}
    More precisely, the hypothesis}% [H0] %{\color{blue} states that
    every one-step}% [R]%{\color{blue}-reduct of}% [a]
    %{\color{blue}satisfies every}% [R]%{\color{blue}-patriarchal
    predicate.}% *)

    unfold SN in *. (** %{\color{blue}Unfolding the definition of}%
    [SN]%{\color{blue}, one has to prove that}% [forall P : A -> Prop,
    patriarchal R P -> P a]. *)

    intros P Hpat. (** %{\color{blue} So, given a predicate a}%
    [R]%{\color{blue}-patriarchal predicate}% [P]%{\color{blue}, we
    need to prove that}% [a] %{\color{blue}holds for}% [P]. *)
    
    apply Hpat. (** %{\color{blue} But}% [P] %{\color{blue}is}%
    [R]%{\color{blue}-patriarchal, and hence}% [P b]
    %{\color{blue}holds for all one-step}% [R]%{\color{blue}-reduct
    of}% [a]. *)

    intros b Hred; apply H0; assumption. (** %{\color{blue}Therefore,
    we conclude by hypothesis}% [H0]. *)
    
  - intro HSN. (** %{\color{blue} On the other direction, suppose
    that}% [SN r t]%{\color{blue}, and call this hypothesis}%
    [HSN]. *)
    
    unfold SN in HSN. (** %{\color{blue}By definition}% [SN r t]
    %{\color{blue}means that}% [forall P : A -> Prop, patriarchal R P -> P
    t]. *)
    
    unfold patriarchal in HSN. (** %{\color{blue}where}% [patriarchal]
    %{\color{blue}means that}% [(forall x : A, (forall y : A, R x y -> P y) -> P
    x)]. *)
    
    apply HSN. (** %{\color{blue}Now we can instantiate the
    predicate}% [P] %{\color{blue}in the hypothesis}% [HSN]
    %{\color{blue}with}% [SN_ind R] %{\color{blue}and then we need to
    prove that}% [forall x : A, (forall y : A, R x y -> SN_ind R y) -> SN_ind R
    x]. *)

    intros x HSN_ind. (** %{\color{blue}To do so, let}% [x:A]
    %{\color{blue}and call}% [HSN_ind] %{\color{blue}the hypothesis}%
    [forall y : A, R x y -> SN_ind R y]%{\color{blue}, and prove that}%
    [SN_ind R x]. *)

    apply sn_acc. (** %{\color{blue}Applying the definition of}%
    [SN_ind]%{\color{blue}, i.e. the constructor}%
    [sn_acc,]%{\color{blue} we need to prove that}% [forall y : A, R x y ->
    SN_ind R y] *)

    assumption. (** %{\color{blue}which is exactly the hypothesis}%
    [HSN_ind]%{\color{blue}, and we conclude.}% *)
Qed.

(** ** The Main Theorem *)

(** In this section, we present the main steps of the formal proof of
    the Modular Strong Normalisation Theorem.  *)
(* begin hide *)
Lemma WeakStrongSimul {A B} (redA1 redA2: Red A) (redB: Red B) (R: Rel A B):
  WeakSimul redA1 redB R
  -> StrongSimul redA2 redB R
  -> StrongSimul (redA1 # redA2) redB R.
Proof.
  intros H1 H2.
  unfold StrongSimul in *.
  unfold WeakSimul in *.
  unfold Sub in *.
  intros a b H3.
  inversion H3; subst. clear H3.
  inversion H0; subst. clear H0.
  assert (H': (inverse R # redA1) a b1).
  { apply compose with b0; assumption. }
  apply H1 in H'.
  inversion H'; subst. clear H'.
  induction H0.
  - apply H2.
    apply compose with b1; assumption.
  - assert (Hstrong: (trans redB # inverse R) b2 b).
    { apply H2. apply compose with b1; assumption. }
    inversion Hstrong; subst. clear Hstrong.
    apply compose with b3. 
    + apply tailtransit with b2; assumption.
    + assumption.
Qed.  

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

Theorem SNbySimul {A B} {redA: Red A} {redB: Red B} {R: Rel A B}:
  StrongSimul redA redB R ->
  forall a, Image (inverse R) (SN_ind redB) a -> SN_ind redA a.
(* begin hide *)
Proof.
  intros Hstrong a Hinv.
  inversion Hinv; subst. clear Hinv.
  inversion H0; subst. clear H0. 
  assert (HSNTrans: SN_ind (trans redB) a0).
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
(* end hide *)

Lemma RCSimul {A B} {redA red'A: Red A} {redB: Red B} {R: Rel A B}:
  (StrongSimul red'A redB R) -> (WeakSimul redA redB R) ->
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

Inductive Id {A} : Red A :=
  identity: forall a:A, Id a a.

Lemma HId {A} (red: Red A): forall a, SN_ind red a <-> Image (inverse Id) (SN_ind red) a.
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

Inductive union {A} (red1: Red A)(red2: Red A) : Red A :=
 | union_left: forall a b,  red1 a b -> union red1 red2 a b
 | union_right: forall a b,  red2 a b -> union red1 red2 a b.

Notation "R1 \un R2" := (union R1 R2) (at level 40).

Lemma UnionStrongSimul {A} {redA red'A: Red A}:
  StrongSimul redA (redA \un red'A) Id.
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
  StrongSimul ((refltrans redA) # red'A) (redA \un red'A) Id.
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
      assert (Hone: (redA \un red'A) a b).
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

Lemma inclUnion {A} {redA red'A: Red A}: forall a, (SN_ind redA a) -> (forall b, (((refltrans redA) # red'A) a b) -> SN_ind (redA \un red'A) b) -> (SN_ind (redA \un red'A) a).
Proof.
  intros a HSN.
  induction HSN. clear H.
  intros Hyp.
  apply sn_acc.
  intros b0 Hunion.
  inversion Hunion; subst.
  - apply H0.
    + assumption.
    + intros b' Hrefl.
      apply Hyp.
      inversion Hrefl; subst.
      apply compose with b.
      * apply refltailtransit with b0.
        ** apply transSub in H.
           apply atleast1 in H.
           assumption.
        ** assumption.
      * assumption.
  - apply Hyp.
    apply compose with a.
    + apply reflex.
    + assumption.
Qed.

Lemma stabComp {A} {redA: Red A}: forall a,
    SN_ind redA a -> forall b, refltrans redA a b -> SN_ind redA b.
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

Lemma SNinclUnion {A} {redA red'A: Red A}: (forall b, SN_ind redA b -> forall c, red'A b c -> SN_ind redA c) ->
                                           (forall a, (SN_ind ((refltrans redA) # red'A) a) ->
                                                 (SN_ind redA a) -> (SN_ind (redA \un red'A) a)).
(* begin hide *)
Proof.
  intros Hstable a HSNcomp.
  induction HSNcomp.
  intros HSN.
  apply inclUnion.
  - assumption.
  - intros b Hcomp.    
    apply H0.
    + assumption.
    + inversion Hcomp; subst. clear Hcomp.
      assert(H': SN_ind redA b0).
      {
        apply stabComp with a; assumption.
      }
      apply Hstable with b0; assumption.
Qed.
(* end hide *)

Lemma SNunion {A} {redA red'A: Red A}:
  (forall b, SN_ind redA b -> forall c, red'A b c -> SN_ind redA c) ->
  forall a, (SN_ind (redA \un red'A) a) <->
       (SN_ind ((refltrans redA) # red'A) a) /\ ((SN_ind redA) a).
(* begin hide *)
Proof. 
  intros Hstable a; split.
  - intro HSN. split.
    + assert (HSsimul: StrongSimul (refltrans redA # red'A) (redA \un red'A) Id).
      {
        apply UnionReflStrongSimul.
      }
      apply HId in HSN.
      generalize dependent HSN.
      apply SNbySimul; assumption.
    + assert (HSsimul: StrongSimul redA (redA \un red'A) Id).
      {
        apply UnionStrongSimul.
      }
      apply HId in HSN.
      generalize dependent HSN.
      apply SNbySimul; assumption.
  - intro Hand.
    destruct Hand as [Hcomp HredA].
    assert (HSNunion1: (SN_ind ((refltrans redA) # red'A) a) ->
                       (SN_ind redA a) -> (SN_ind (redA \un red'A) a)).
    {
      apply SNinclUnion; assumption.
    }
    apply HSNunion1; assumption.
Qed.
(* end hide *)

Theorem ModStrNorm {A B: Type} {redA red'A: Red A}
        {redB: Red B} {R: Rel A B}:
  (StrongSimul red'A redB R) ->
  (WeakSimul redA redB R) ->
  (forall b: A, SN_ind redA b) -> forall a, Image (inverse R) (SN_ind redB) a ->
                                 SN_ind (redA \un red'A) a.
Proof.
  intros Hstrong Hweak HSN a HImage. (** %{\color{blue} Let}% [A]
  %{\color{blue}and}% [B] %{\color{blue}be types}%, [redA]
  %{\color{blue}and}% [red'A] %{\color{blue}be two reduction relations
  over}% [A]%{\color{blue},}% [redB] %{\color{blue}a reduction
  relation over}% [B]%{\color{blue}, and}% [R] %{\color{blue}a
  relation from}% [A] %{\color{blue}to}% [B]%{\color{blue}. Assume
  that}% [red'A] %{\color{blue}is strongly simulated by}% [redB]
  %{\color{blue}through}% [R]%{\color{blue}, that}% [redA]
  %{\color{blue}is weakly simulated by}% [redB]
  %{\color{blue}through}% [R]%{\color{blue}, that every}% [b:A]
  %{\color{blue}is such that}% [SN_ind redA b]%{\color{blue}, and
  let}% [a:A] %{\color{blue}be an arbitrary element in the inverse
  image of}% [SN_ind redB]%{\color{blue}. We need to prove that}%
  [SN_ind (redA \un red'A) a]%{\color{blue}. By lemma}%
  [SNunion]%{\color{blue}, this is equivalent to prove that}% [SN_ind
  (refltrans redA # red'A) a /\ SN_ind redA a]. *)

  assert(Hsplit: SN_ind (redA \un red'A) a <->
                    SN_ind (refltrans redA # red'A) a /\ SN_ind redA a).
  {
    apply SNunion.
    intros b HSN' c Hred.
    apply HSN.
  }
  destruct Hsplit as [H Hunion]; clear H. (** %{\color{blue}Note that
                    just one direction of this equivalence is needed.}% *)

  apply Hunion; split. (** %{\color{blue}The proof of this conjunction
  is split in two parts. We first need to prove that}% [SN_ind
  (refltrans redA # red'A) a]%{\color{blue}, which can be proved by
  lemma}% [SNbySimul]%{\color{blue}, as long as}% [(refltrans redA #
  red'A)] %{\color{blue}is strongly simulated by}% [redB]
  %{\color{blue}through}% [R]. *)
  
  - assert(HSNSimul: StrongSimul (refltrans redA # red'A) redB R ->
                   forall a : A, Image (inverse R) (SN_ind redB) a ->
                                 SN_ind (refltrans redA # red'A) a).
  {
   apply SNbySimul.
  }
  apply HSNSimul.
    + apply RCSimul; assumption. (** %{\color{blue}Now we need to
                                     prove that}% [(refltrans redA #
                                     red'A)] %{\color{blue}is strongly
                                     simulated by}% [redB]
                                     %{\color{blue}through}%
                                     [R]%{\color{blue}, which is
                                     achieved by lemma}% [RCSimul]. *)
      
    + assumption.
  - apply HSN. (** %{\color{blue}The second part of the conjunction
                   corresponds to the hypothesis}%
                   [HSN]%{\color{blue}, and we conclude.}% *)
Qed.
(* end hide *)

(** * Conclusion *)

(** In this work we presented a constructive formalisation of the
    Modular Strong Normalisation Theorem in the Coq Proof
    Assistant. The proof is constructive in the sense that it does not
    use the principle of proof by contradiction or any other classical
    rule. In addition, only the standard Coq libraries, that are
    loaded at startup, are used. The constructive approach is not
    the standard way to prove termination of a reduction relation. In
    fact, the most common way to prove strong normalisation is by
    defining termination as the absence of infinite reductions, and
    using proof by contradiction as the reasoning tool. For instance,
    a classical proof of the Modular Strong Normalisation Theorem is
    available at %\cite{kes09}%. Constructive proofs are usually more
    difficult and elaborate than classical ones, but the former are
    preferred in the context of Computer Science.

    The Modular Strong Normalisation Theorem is an abstract result
    that states the conditions for the union of two reduction
    relations to be terminating. It is a non-trivial result in
    abstract reduction systems that uses the well known technique of
    termination by simulation, i.e. the termination of a reduction
    system is obtained by simulating its steps via another reduction
    relation that is known to be terminating.

    The proofs developed in this formalisation follow the ideas
    presented in %\cite{LengrandPhD}%, where a theory of constructive
    normalisation is developed. This theory is based on a definition
    of strong normalisation that ... Instead of using Lengrand's
    definition, we decided to use the standard inductive definition of
    strong normalisation. A formal proof of the equivalence between
    these definitions is also provided. In this way, we believe that
    our presentation is easy to follow and ...

    An interesting application of the Modular Strong Normalisation
    Theorem is given in %\cite{kes09}% to establish the termination of
    a calculus with explicit substitutions. Termination of calculus
    with explicit substitutions is a challenging problem that...

     - This is part of a bigger project.  Compatible versions of Coq
     - General explanation of how to compile and generate
     - documentation.

*)
