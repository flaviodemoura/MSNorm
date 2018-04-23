(** * Introduction

This work is about a mechanical and constructive proof of the Modular Strong Normalisation Theorem in the Coq Proof Assistant %~\cite{CoqTeam}%. The proof is entirely constructive in the sense that it does not use classical reasoning, i.e. derivations based on the law of excluded middle or proof by contradiction, for instance. This is interesting from the computational point of view because the algorithmic content of proofs can be automatically extracted as certified code %~\cite{Let2008}%. There is no extraction of code in this work, which is part of a bigger project that aims to generate certified code. The choice of Coq as the formalisation tool is natural because the underlying logic behind the calculus of inductive constructions, the theory over which Coq is developed, is also constructive %\cite{Paulin93,wernerPhD}%. 

The Modular Strong Normalisation Theorem states the conditions for the union of two reduction relations over a set $A$ to be terminating (or strongly normalising) knowing that they can be simulated by another terminating reduction relation (cf. %~\cite{kes09}%). It is well known that the union of terminating relations are not necessarily terminating, i.e. termination is not a modular property %\cite{toyama87}%. More precisely, a property $P$ that holds for a combined system, assuming that each subsystem have the same property $P$, is called modular, i.e. if $P$ is a modular property that holds for both systems $A$ and $B$, then it also holds for the combined system built from $A$ and $B$. In the context of rewriting theory, termination is known to be a non-modular property. Nevertheless, under certain restrictions, modularity can be recovered (cf. %~\cite{Gramlich12}%).

The main result of this paper is the formalisation of a constructive formal proof of the Modular Strong Normalisation Theorem. A constructive proof of this theorem is presented in %\cite{LengrandPhD}% and part of it, that does not include the Modular Strong Normalisation Theorem, is formalised in Coq %\footnote{\scriptsize \url{http://www.lix.polytechnique.fr/~lengrand/Work/HDR/Coq/First-order/NormalisationTheory.v}}%. In his work, Lengrand defines the strong normalisation property in terms of a specialized inductive principle that should hold for all predicate, i.e. through a second order formula. In our formalisation, we follow the standard inductive definition of strongly normalising relations. In addition, we prove the equivalence of Lengrand's notion of strong normalisation with the standard inductive definition used here. Our proof of the Modular Strong Normalisation Theorem follows the ideas in %\cite{LengrandPhD}%, but we use only the standard inductive definition of strong normalisation. In this way, we believe that we achieved a simpler and easier to follow formalisation. This paper is built up from a Coq script where some code was hidden for the sake of clarity of this document. All the files concerning this work are freely available in the repository  %{\tt https://github.com/flaviodemoura/MSNorm}%. The contributions of this work can be summarised as follows:

- A constructive proof of the Modular Strong Normalisation Theorem that is based only on the standard inductive definition of strong normalisation in the Coq Proof Assistant.
- An equivalence proof between different notions of Strong Normalisation
- ??
 *)

(* in  where a classical (i.e. non-constructive) proof can be found in %\cite{kes09}% (Theorem A.2). It uses the standard technique for proving termination using a reduction to absurdity: one assumes that termination does not hold, reaches a contradiction and conclude that termination must hold. *)

(** * The Modular Strong Normalisation Theorem *)

(**
In this section, we present the Modular Strong Normalisation Theorem whose formalisation will be detailed in the next section. This is an abstract theorem about termination of reduction relations through the well known simulation technique %\cite{BN98}%. In order to fix notation, let [A] and [B] be sets. A relation from [A] to [B] is a subset of $A\times B$. If $R$ is a relation from [A] to [B] then we write $aRb$ instead of $(a,b) \in R$, and in this case, we say that $a$ %{\it reduces}% to $b$. If one uses arrow notation to represent relations, and $\to$ is a relation from [A] to [B] then $\leftarrow$ is the inverse relation from [B] to [A]. If $\to_1$ is a relation from $A$ to $B$, and $\to_2$ is a relation from $B$ to $C$ then the composition of $\to_1$ with $\to_2$, written $\to_1\cdot \to_2$, is a relation from $A$ to $C$. A relation from a set to itself is a %{\it reduction relation}%, i.e. a reduction relation is a subset of $A\times A$. If $\to_A$ is a reduction relation over $A$, then a %{\it reduction sequence}% is a finite or infinite sequence of the form $a \to_A a_1 \to_A a_2 \to_A \ldots$ A finite reduction $a \to_A a_1 \to_A a_2 \to_A \ldots$ \to_A a_n\ (n\geq 0)$ is a $n$-step reduction from $a$. We write $\to_A^+$ (resp. $\to_A^*$) for the transitive (resp. reflexive transitive) closure of $\to_A$. *) 
(* In Lengrand's work, the set of $\to$-strongly normalising elements is defined as the intersection of all subsets of [A] that are patriarchal, where a subset [B] of [A] is %{\it patriarchal}% if $\forall a \in A, \to(a) \subseteq B$ then $a \in B$.
We follow the proof of %\cite{LengrandPhD,lengSNInd05}% that developed a constructive normalisation theory for proving termination of reduction relations, i.e. binary relations from a set to itself, in a constructive way.
Instead of using the above definition of $SN^{\to}$, we decided to work directly with its standard inductive definition which is given by
A reduction relation over $A$ is said to be %{\it strongly normalising}%, if the following property holds any $a\in A$: there is no infinite reduction starting from $a$. *)
(**
An element $a\in A$ is %{\it strongly normalising}% w.r.t $\to_A$ if every reduction sequence starting from $a$ is finite, and in this case we write $a \in SN^{\to_A}$. This idea can be expressed inductively as follows: 
%\begin{equation}\label{def:sn}
a \in {SN}^{\to_A} \mbox{ iff } \forall b, (a \to_A b \mbox{ implies } b \in {SN}^{\to_A})
\end{equation}% *)
(*
%\noindent% whose Coq code is given by
[[
Inductive SN_ind {A:Type} (red: Red A) (a:A): Prop :=
  | sn_acc: (forall b, red a b -> SN_ind red b) -> SN_ind red a.
]]
A few comments about Coq are at a place. In the above definition, [Inductive] is the reserved word for inductive definitions. It is followed by the name of the definition, which in our case is [SN_ind], and it has three arguments: [{A:Type}], [(red:Red A)] and [(a:A)]. The first argument appears between curly brackets, which means that it is  %{\it implicit}%. Implicit arguments are types of polymorphic functions that can be inferred from the context. The second argument corresponds to a reduction relation [red] over [A], and the third argument is an element of [A]. This definition has one constructor named [sn_acc] whose content corresponds exactly to the definition given in (%\ref{def:sn}%). In this way, in order to prove that a certain element [a:A] is strongly normalising w.r.t. a reduction relation $\to_r$, one has to build a proof of the formula $\forall b, a \to_r b \to SN\_ind \to_r b$.*)
(**
In order to present the Modular Strong Normalisation Theorem, we need to define the notions of strong and weak simulation. In the following definitions $A$ and $B$ are arbitrary sets:

%\begin{definition}\label{def:sws}
Let $\to$ be a relation from $A$ to $B$, $\to_A$ be a reduction relation over $A$  and $\to_B$ be a reduction relation over $B$. The reduction relation $\to_B$ {\it strongly} (resp. {\it weakly}) simulates $\to_A$ through $\to$ if $(\leftarrow \cdot \to_A) \subseteq (\to_B^+ \cdot \leftarrow)$ (resp. $(\leftarrow \cdot \to_A) \subseteq (\to_B^* \cdot \leftarrow)$). \flavio{Aqui pode ser interessante inserir uma figura para ilustrar estas definições.}
\begin{tikzpicture}[scale=.75]
\draw[ultra thick,myblue] (0,0) circle [x radius=1.5cm, y radius=4cm]
                    (6,0) circle [x radius=1.5cm, y radius=4cm];
                    
\node[font=\color{myblue}\Large\bfseries] at (0,5) {A};
\node[font=\color{myblue}\Large\bfseries] at (6,5) {B};  

\node (a1)  at (0,2)  {a};
\node (a2) at (0,0)   {a'};

\node[circle] (b1) at (6,2)  {b}; 
\node[circle] (b2) at (6,-2)  {b'};

\draw[->,red] (a1.east) .. controls +(up:0cm) and +(left:1cm) .. node[above,sloped] {R} (b1.west);
\draw[->,red] (a2.east) .. controls +(up:0cm) and +(left:1cm) .. node[above,sloped] {R} (b2.west);
\draw[->,red] (a1.south) .. controls +(up:0cm) and +(left:0cm) .. node[above,sloped] {A} (a2.north);
\draw[->,red] (b1.south) .. controls +(up:0cm) and +(left:0cm) .. node[above,sloped] {$B^+$} (b2.north);
\end{tikzpicture}
\end{definition}%

Now we are ready to state the Modular Strong Normalisation Theorem:
%\begin{theorem}
Let $\to$ be a relation from $A$ to $B$, $\to_1$ and $\to_2$ be two reduction relations over $A$, and $\to_B$ be a reduction relation over $B$. Suppose that:
\begin{enumerate}
\item\label{hip:one} $\to_B$ strongly simulates $\to_1$ through $\to$;
\item\label{hip:two} $\to_B$ weakly simulates $\to_2$ through $\to$;
\item\label{hip:three} $A \subseteq {SN\_ind}^{\to_1}$.
\end{enumerate}
Then $\leftarrow ({SN\_ind}^{\to_B}) \subseteq {SN\_ind}^{\to_1 \cup \to_2}$. In other words, $$\forall a:A, (a\in \leftarrow({SN\_ind}^{\to_B}) \mbox{ implies } a \in {SN\_ind}^{\to_1\cup \to_2}.$$
\end{theorem}%
%\begin{proof}
 This proof follows the lines of \cite{LengrandPhD}, but using the standard definition $SN\_ind$. First of all, hypothesis \ref{hip:one} and \ref{hip:two} allow us to conclude that the composition $(\to_1^* \cdot \to_2)$ is strongly simulated by $\to_B$: in fact, from hypothesis \ref{hip:two} we have that $\to_1^*$ is weakly simulated by $\to_B$. In addition, the composition of two reduction relations that are, respectively, strongly and weakly simulated by the same reduction relation is strongly simulated by this reduction relation. Therefore, $(\to_1^* \cdot \to_2)$ is strongly simulated by $\to_B$ through $\to$, that together with the fact that $a\in \leftarrow({SN\_ind}^{\to_B})$ allow us to conclude that $a \in {SN\_ind}^{\to_1^* \cdot \to_2}$. Now, from hypothesis \ref{hip:three}, we have $a \in {SN\_ind}^{\to_1}$, and we conclude from the fact that ${SN\_ind}^{\to_1^* \cdot \to_2} \cap {SN\_ind}^{\to_1} = {SN\_ind}^{\to_1\cup \to_2}$. \flavio{expandir!} \hfill$\Box$ 
\end{proof}%
*)

(** * The Formalisation 

In this section we present the details of the formalisation of the Modular Strong Normalisation Theorem in the Coq Proof Assistant. The first important point is that our proof is constructive, i.e. it does not use classical reasoning. In addition, no additional library other then the ones that are automatically loaded after starting Coq is used. The theory behind Coq, known as the calculus of inductive constructions, is a constructive higher-order logic which makes natural the choice of Coq as the formalisation tool for this work.

In terms of notation, sets are coded as arbitrary types in such a way that the membership relation $a \in A$ ($a$ is an element of the set $A$) is represented as $a:A$ ($a$ has type $A$). *)
(*This correspondence is extensively used in Computer Science when one writes $a:\mathbb{N}$ ($a$ has type $\mathbb{N}$) to express the fact that $a$ is a natural number, i.e. that $a\in \mathbb{N}$ (cf. %\cite{Geu09}%).
Given two sets $A$ and $B$, a binary relation from $A$ to $B$ is a subset of the Cartesian product $A\times B$. In this way, if $R\subseteq A\times B$ then we usually write $R a b$ or $a R b$ to mean that $a$ is related to $b$ through $R$, i.e. $(a,b) \in R$. Alternatively, the membership relation can be represented by a type assignment so that an element $a$ belongs to the set $A$ ($a \in A$) corresponds to the fact the $a$ has type $A$ ($a:A$). So for instance, we can say that $n$ is a natural number by either writing $a\in \mathbb{N}$, i.e. that $a$ belongs to the set of natural numbers, if we are in the context of set theory, or $a:\mathbb{N}$, i.e that $a$ has the type of natural numbers, if we are in the context of type theory. In the rest of this section, we present a number of basic definitions in order to make clear the notation used in the other sections of this work. The definitions given in this section can be found in %\url{http://www.lix.polytechnique.fr/~lengrand/Work/HDR/Coq/First-order/NormalisationTheory.v}%. *)
(** We start with some basic definitions in order to make Coq notation clear, and that will allow us to give some comments about Coq. Note that this paper is written directly from a Coq script file, therefore, the Coq code presented is the real code of the formalisation. A relation from $A$ to $B$ is defined as a binary predicate as follows:
 *)

Definition Rel (A B : Type) := A -> B -> Prop.
(** %\noindent% In this definition, [Rel] receives two types as argument, and return the signature of a relation from $A$ to $B$, i.e. the type [A -> B -> Prop] of a relation from [A] to [B]. As seen before, if $A=B$ then we have a %{\it reduction relation}%: *)

Definition Red (A : Type) := Rel A A.
(** Given two relations [R1] and [R2] from [A] to [B], if every pair of elements in [R1] is also in [R2] then we say that [R1] is a subrelation of [R2]: *)

Definition Sub {A B} (R1 R2: Rel A B) : Prop := forall a b, R1 a b -> R2 a b.
(** In the above definition, [A] and [B] first appear between curly brackets, which means that these arguments  are  %{\it implicit}%. Implicit arguments are types of polymorphic functions that can be inferred from the context. Therefore, [Sub] requires two relations as arguments, and Coq automatically infers its type. A more convenient notation can be easily defined for the objects we are constructing. In the case of the predicate [Sub], we define an infix notation as follows: *)

Notation "R1 <# R2" := (Sub R1 R2) (at level 50).
(** This means that now one can write [R1 <# R2] instead of [Sub R1 R2]. In addition, in order to avoid parsing ambiguity, a precedence level ranging from 0 to 100 can be provided. *)

(* (* begin hide *) *)
(* (* Inclusion is reflexive *) *)
(* Lemma SubRefl {A B} (R: Rel A B) : R <# R. *)
(* Proof. *)
(*   unfold Sub. *)
(*   intros a b H. *)
(*   exact H. *)
(* Qed. *)

(* (* Inclusion is transitive *) *)
(* Lemma SubTrans {A B} (R2 R1 R3: Rel A B) : R1 <# R2 -> R2 <# R3 -> R1 <# R3. *)
(* Proof. *)
(*   unfold Sub. *)
(*   intros Hr1 Hr2. *)
(*   intros a b H. *)
(*   apply Hr2, Hr1. *)
(*   exact H. *)
(* Qed. *)

(* (* Double inclusion, i.e. equivalence *) *)
(* Definition Equiv {A B} (R1 R2: Rel A B) := R1 <# R2 /\ R2 <# R1. *)
(* Notation "R1 -- R2" := (Equiv R1 R2) (at level 50). *)

(**  Given two relations, say [red1] from [A] to [B] and [red2] from [B] to [C], one can build a new relation from [A] to [C] by composing its steps: *)

Inductive comp {A B C} (red1: Rel A B)(red2: Rel B C) : Rel A C :=
  compose: forall b a c,  red1 a b -> red2 b c -> comp red1 red2 a c.
Notation "R1 # R2" := (comp R1 R2) (at level 40).
(* begin hide *)
Arguments compose {A B C red1 red2} _ _ _ _ _ .
(* end hide *)
(** %\noindent% The inductive definition [comp] has just one constructor named [compose] that explicitly builds the composition of [red1] and [red2]. Therefore, in order to prove that $a$ and $c$ are related by the (composite) relation [(comp red1 red2)] one has to explicitly give an element [b] such that [(red1 a b)] and [(red2 b c)]. *)

(** The inverse of a relation from a [A] to [B] is inductively defined as the corresponding relation from [B] to [A]: *)

Inductive inverse {A B} (R: Rel A B) : Rel B A :=
  inverseof: forall a b, R a b -> inverse R b a.

(*  (* begin hide *) *)
(* (* Composition is associative *) *)
(* Lemma compTrans {A B C D} (R1: Rel A B)(R2: Rel B C)(R3: Rel C D) *)
(*   : (R1 # R2) # R3 -- R1 # (R2 # R3). *)
(* Proof. *)
(*   unfold Equiv. split. *)
(*   - unfold Sub. *)
(*     intros a b H. *)
(*     inversion H as [a' b' d Hc Hr3 Heq Heq']; subst. *)
(*     inversion Hc as [a'' b' d Hr1 Hr2 Heq Heq']; subst. *)
(*     apply (compose a''). *)
(*     + exact Hr1. *)
(*     + apply (compose a'). *)
(*       * exact Hr2. *)
(*       * exact Hr3. *)
(*   - unfold Sub. *)
(*     intros a b H. *)
(*     inversion H; subst. *)
(*     inversion H1; subst. *)
(*     apply (compose b1). *)
(*     + apply (compose b0). *)
(*       * assumption. *)
(*       * assumption. *)
(*     + assumption. *)
(* Qed. *)

(* (* Composition is monotonous *) *)
(* Lemma SubComp {A B C} (R1 R2: Rel A B)(R3 R4: Rel B C)  *)
(* : R1 <# R2 -> R3 <# R4 -> (comp R1 R3) <# (comp R2 R4). *)
(* Proof. *)
(*   unfold Sub. *)
(*   intros H H0. *)
(*   intros a b H'. *)
(*   inversion H'; subst. *)
(*   apply (compose b0). *)
(*   + apply H in H1. *)
(*     assumption. *)
(*   + apply H0 in H2. *)
(*     assumption. *)
(* Qed. *)

(** The transitive closure of a reduction relation [red] over [A] is constructed, as usual, by adding to [red] all possible reductions with at least one step starting from each $a\in A$: *)

Inductive trans {A} (red: Red A) : Red A :=
| singl: forall a b,  red a b -> trans red a b
| transit: forall b a c,  red a b -> trans red b c -> trans red a c.
(* begin hide *)
Arguments transit {A} {red} _ _ _ _ _ .
(* end hide *)
(** Therefore, it is straightforward from the definition to prove that a reduction relation is included in its transitive closure: *)

Lemma transSub {A:Type} (red: Red A) : red <# (trans red).
(* begin hide *)
Proof.
  unfold Sub.
  intros a b H.
  apply singl; assumption.
Qed.
(* end hide *)
(** The reflexive transitive closure of a reduction relation is obtained from its transitive closure by adding reflexivity, i.e. by adding the fact that each element of the relation reduces to itself in 0 steps: *)

Inductive refltrans {A} (red: Red A) : Red A :=
| reflex: forall a,  refltrans red a a
| atleast1: forall a b,  trans red a b -> refltrans red a b.

(* Given a reduction relation [red] over [A], and an element [a:A], the transitive closure of [red] contains all the elements of the form [(a,b)], where [b] is related with [a] by a finite (possibly empty) number of composition applications. In this sense, [(a,b)] can be seen as a path from [a] to [b] through [red]. Paths can be composed in such a way that a new path from [a] to [c] can be built from a path from [a] to [b] and a path from [b] to [c]: *)

Lemma tailtransit {A red}: forall (b a c:A),  trans red a b -> trans red b c -> trans red a c.
(* begin hide *)
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
(* (* Transitive closure is monotonous *) *)
(* Lemma SubTrans1 {A} (red1 red2: Red A) : red1 <# red2 -> (trans red1) <# (trans red2). *)
(* Proof. *)
(*   unfold Sub. *)
(*   intros H a b H0. *)
(*   induction H0. *)
(*   - apply H in H0. *)
(*     apply singl; assumption. *)
(*   - apply H in H0. *)
(*     apply (transit b). *)
(*     + exact H0. *)
(*     + apply IHtrans. *)
(* Qed. *)
(* (* end hide *) *)

(** The image of a predicate via a relation is inductively defined as follows: *)

Inductive Image {A B} (R:Rel A B)(P: A -> Prop): B -> Prop
  := image: forall a b, P a -> R a b -> Image R P b.
(* begin hide *)
Arguments image {A B R P} _ _ _ _.
(* end hide *)
(** The notions of weak and strong simulation of reduction relations, as given in Definition %\ref{def:sws}%, are a straightforward translation to the Coq language:*)

Definition WeakSimul {A B} (redA: Red A) (redB: Red B) (R: Rel A B) := 
  ((inverse R) # redA) <# ((refltrans redB) # (inverse R)).

Definition StrongSimul {A B} (redA: Red A) (redB: Red B) (R: Rel A B) := 
  ((inverse R) # redA) <# ((trans redB) # (inverse R)).

(* (* begin hide *) *)
(* (* The fact that redA is strongly simulated by redB is *)
(* monotonic in redB and anti-monotonic in redA *) *)
(* Lemma SimulMonotonic {A B} (redA1 redA2: Red A) (redB1 redB2: Red B) (R: Rel A B): *)
(*   redA2 <# redA1 -> redB1 <# redB2 -> StrongSimul redA1 redB1 R -> StrongSimul redA2 redB2 R. *)
(* Proof. *)
(*   unfold StrongSimul. *)
(*   intros H H0. *)
(*   intros H2. *)
(*   apply (SubTrans ((inverse R) # redA1)). *)
(*   - apply SubComp. *)
(*     + apply SubRefl. *)
(*     + apply H. *)
(*   - apply (SubTrans ((trans redB1) # (inverse R))). *)
(*     + apply H2. *)
(*     + apply SubComp. *)
(*       * apply SubTrans1 in H0; apply H0. *)
(*       * apply SubRefl. *)
(* Qed. *)

(* (* If redA1 and redA2 are strongly simulated by the same relation, *)
(* so is their composition *) *)
(* Lemma SimulBoth {A B} (redA1 redA2: Red A) (redB: Red B) (R: Rel A B): *)
(*   StrongSimul redA1 redB R *)
(*   -> StrongSimul redA2 redB R *)
(*   -> StrongSimul (redA1 # redA2) redB R. *)
(* Proof. *)
(*   unfold StrongSimul. *)
(*   intros H1 H2. *)
(*   unfold Sub. *)
(*   intros a b H3. *)
(*   inversion H3;subst. *)
(*   inversion H0;subst. *)
(*   unfold Sub in H1. *)
(*   assert(H': (inverse R # redA1) a b1). *)
(*   { apply (compose b0). *)
(*     - assumption. *)
(*     - assumption. *)
(*   } *)
(*   apply H1 in H'. *)
(*   inversion H'; subst. *)
(*   assert(H'': (inverse R # redA2) b2 b). *)
(*   { apply (compose b1). *)
(*     - assumption. *)
(*     - assumption. *)
(*   } *)
(*   apply H2 in H''. *)
(*   inversion H''; subst. *)
(*   apply (compose b3). *)
(*   - apply (tailtransit b2). *)
(*     + assumption. *)
(*     + assumption. *)
(*   - assumption. *)
(* Qed. *)

(* (* If redA is strongly simulated, so is its transitive closure *) *)
(* Lemma SimulTrans {A B} (redA: Red A) (redB: Red B) (R: Rel A B) *)
(* : StrongSimul redA redB R -> StrongSimul (trans redA) redB R. *)
(* Proof. *)
(*   unfold StrongSimul. *)
(*   unfold Sub in *. *)
(*   intros Hip a b H. *)
(*   inversion H; subst. *)
(*   clear H. *)
(*   generalize dependent a. *)
(*   induction H1. *)
(*   - intros a' H'. *)
(*     apply Hip. *)
(*     apply compose with a; assumption. *)
(*   - intros a' H'. *)
(*     assert (H'': (inverse R # redA) a' b). *)
(*     { apply compose with a; assumption. } *)
(*     apply Hip in H''. clear H'. *)
(*     inversion H''; subst. *)
(*     apply IHtrans in H2. *)
(*     inversion H2; subst. *)
(*     apply compose with b1. *)
(*     apply tailtransit with b0; assumption. *)
(*     assumption. *)
(* Qed. *)

(* (* The transitive closure is equivalent to the composition of the *)
(* relation with its reflexive-transitive closure *) *)
(* Lemma trans2refltrans {A} {red: Red A}: trans red -- red # (refltrans red). *)
(* Proof. *)
(*   unfold Equiv. *)
(*   unfold Sub. *)
(*   split. *)
(*   - intros a b H. *)
(*     inversion H; subst. *)
(*     + apply (compose b). *)
(*       * assumption. *)
(*       * apply reflex. *)
(*     + apply (compose b0). *)
(*       * assumption. *)
(*       * apply atleast1; assumption. *)
(*   - intros a b H. *)
(*     inversion H; subst. *)
(*     inversion H1; subst. *)
(*     + apply singl in H0; assumption. *)
(*     + apply (transit b0). *)
(*       * assumption. *)
(*       * assumption. *)
(* Qed. *)

(* (* end hide *) *)

(* (* Constructive Normalisation Theory *)

(* In his PhD thesis, S. Lengrand defines the strong normalisation property in terms of patriarchal sets, which expresses a notion of stability w.r.t. a given reduction relation: *)  *)
(* (* *)
(* Definition patriarchal {A} (red:Red A) (P:A -> Prop): Prop *)
(*   := forall x, (forall y, red x y -> P y) -> P x. *)
(* *) *)
(* (** This means that a predicate [P] over a set [A] is patriarchal w.r.t. a given reduction relation [red] over [A], if for every element [a] of [A] which reduces to a term [b], that satisfies [P], through the given reduction relation [red], one concludess that [a] also holds for [P]. A term [a] is then strongly normalising w.r.t. a given reduction relation [red] if [a] holds forall all patriarchal predicate w.r.t. the reduction relation [red].  This notion of strong normalisation is then a second-order property: *) *)
(* (* *)
(* Definition SN {A:Type} (red:Red A) (a:A): Prop *)
(*   := forall P, patriarchal red P -> P a. *)
(* *) *)
(* (* begin hide *) *)

(* (* If all 1-step reducts of a are SN, so is a *) *)
(* (* Lemma toSN {A}{red:Red A} {x}: (forall y, red x y -> SN red y) -> SN red x. *)
(* Proof. *)
(*   unfold SN. *)
(*   intros H P H1. *)
(*   unfold patriarchal in *. *)
(*   apply H1. *)
(*   intros y H2. *)
(*   apply H. *)
(*   - assumption. *)
(*   - assumption. *)
(* Qed. *) *)
(* (* end hide *) *)

(* (** Being SN is a patriarchal predicate TBD *) *)
(* (* *)
(* Lemma SNpatriarchal {A} {red: Red A}: patriarchal red (SN red). *)
(* (* begin hide *) *)
(* Proof. *)
(*   unfold patriarchal. *)
(*   intros M H. *)
(*   unfold SN in *. *)
(*   intros P H1. *)
(*   unfold patriarchal in H1. *)
(*   apply H1. *)
(*   intros y H0. *)
(*   apply H. *)
(*   + assumption. *)
(*   + unfold patriarchal. *)
(*     assumption. *)
(* Qed.*) *)
(* (* end hide *) *)

(* (* Induction principle: *)
(* Let P be a predicate such that, for all SN elements a, if the 1-step *)
(* reducts of a satisfy P then a satisfies P. *)
(* Then all SN elements satisfy P TBD *) *)
(* (* *)
(* Theorem SNind {A} {red: Red A} {P: A -> Prop} *)
(* : (forall a, (forall b, red a b -> P b) -> SN red a -> P a) *)
(*   -> (forall a, SN red a -> P a). *)
(* (* begin hide *) *)
(* Proof. *)
(*   intros. *)
(*   assert (H': patriarchal red (fun a => SN red a -> P a)). *)
(*   { unfold patriarchal. *)
(*     intros. *)
(*     apply H. *)
(*     - intros. *)
(*       apply H1. *)
(*       + assumption.       *)
(*       + apply (SNstable x). *)
(*         * assumption. *)
(*         * assumption. *)
(*     - assumption. *)
(*   } *)
(*   apply (H0 (fun a : A => SN red a -> P a)). *)
(*   - assumption. *)
(*   - assumption. *)
(* Qed. *)
(* (* end hide *) *)
(* *) *)
(* (* begin hide *) *)
(* (* Being patriarchal for red1 is monotonic in red1 *) *)
(* (* Lemma Patriarchalmonotonic {A} {red1 red2: Red A}:  *)
(*   red1 <# red2 -> forall P, patriarchal red1 P -> patriarchal red2 P. *)
(* Proof. *)
(*   unfold Sub; unfold patriarchal. *)
(*   intros H0 P H1 a H2. *)
(*   apply H1. *)
(*   intros y H3. *)
(*   apply H2. *)
(*   apply H0. *)
(*   apply H3. *)
(* Qed.*) *)

(* (* Being SN for red1 is anti-monotonic in red1 *) *)
(* (* Lemma SNmonotonic {A} {red1 red2: Red A}: red1 <# red2 -> forall a, SN red2 a -> SN red1 a. *)
(* Proof. *)
(*   unfold SN. *)
(*   intros H0 a H1 P H2. *)
(*   apply H1. *)
(*   apply (Patriarchalmonotonic H0 P H2). *)
(* Qed. *)
(* *) *)
(* (* Being SN for a relation is the same thing as being SN for its transitive closure *) *)
(* (* Lemma SNSNtrans {A} {red: Red A}: forall a, SN red a <-> SN (trans red) a. *)
(* Proof. *)
(*   assert(forall M, SN red M -> forall N, refltrans red M N -> SN (trans red) N). *)
(*   { apply (@SNind _ _ (fun M => forall N, refltrans red M N -> SN (trans red) N)). *)
(*     intros M IH MSN. *)
(*     assert(forall N, trans red M N -> SN (trans red) N). *)
(*     { intros N H. *)
(*       apply trans2refltrans in H. *)
(*       inversion H; subst. *)
(*       apply (IH b); assumption. *)
(*     } *)
(*     assert(H'': patriarchal (trans red) (SN (trans red))). *)
(*     { apply (@SNpatriarchal _ (trans red)). } *)
(*     unfold patriarchal in H''. *)
(*     intros N H1. *)
(*     apply H'' in H; clear H''. *)
(*     inversion H1; subst. *)
(*     - assumption. *)
(*     - apply (SNstable M). *)
(*       + assumption. *)
(*       + assumption. *)
(*   } *)
(*   split. *)
(*   - intros. *)
(*     apply (H a). *)
(*     + assumption. *)
(*     + apply reflex. *)
(*   - apply SNmonotonic. *)
(*     apply transSub. *)
(* Qed. *)
(* *) *)
(* (* Strong Induction principle: *)
(* Let P be a predicate such that, for all SN elements a, if the n-step *)
(* reducts of a satisfy P then a satisfies P. *)
(* Then all SN elements satisfy P. *)

(* This theorem is stronger than the previous version, since the *)
(* induction hypothesis can be applied not only to the 1-step reducts, *)
(* but to all n-step reducts. In the natural numbers, we can assume the *)
(* IH holds not only for n-1, but for all m<n. *)
(* *) *)
(* (* *)
(* Theorem SNsind {A} {red: Red A} {P: A -> Prop} *)
(* : (forall a, (forall b, trans red a b -> P b) -> SN red a -> P a) *)
(*   -> (forall a, SN red a -> P a). *)
(* Proof. *)
(*   intros H a H0. *)
(*   apply (proj1(SNSNtrans a)) in H0. *)
(*   generalize dependent a. *)
(*   apply SNind. *)
(*   intros a H0 H1. *)
(*   apply H. *)
(*   - assumption. *)
(*   - apply SNSNtrans. *)
(*     assumption.  *)
(* Qed.*) *)
(* (* end hide *) *)

(* Aqui inicia o nosso arquivo *)
  
(* Lemma refl_plus_trans_is_trans {A red} : *)
(*   forall (a b c : A), (refltrans red a b) -> (trans red b c) -> *)
(*                       trans red a c. *)
(* Proof. *)
(*   Admitted. *)

(** ** Strong Normalisation 

In %\cite{LengrandPhD}%, S. Lengrand develops a constructive theory of normalisation in the sense that it does not rely on classical logic. In this theory, the notion of strong normalisation for reduction relations is defined by a second-order formula which is based on a stability predicate called %{\it patriarchal}%: *)

Definition patriarchal {A} (red:Red A) (P:A -> Prop): Prop
  := forall x, (forall y, red x y -> P y) -> P x.

Definition SN {A:Type} (red:Red A) (a:A): Prop
  := forall P, patriarchal red P -> P a.

Lemma SNpatriarchal {A} {red: Red A}: patriarchal red (SN red).
(* begin hide *)
Proof.
  unfold patriarchal.
  intros M H.
  unfold SN in *.
  intros P H1.
  unfold patriarchal in H1.
  apply H1.
  intros y H0.
  apply H.
  + assumption.
  + unfold patriarchal.
    assumption.
Qed.
(* end hide *)

Lemma SN_stable {A} {red: Red A}: forall M, SN red M -> forall N, red M N -> SN red N.
(* begin hide *)
Proof.
    assert (H: patriarchal red (fun a => forall b, red a b -> SN red b)).
  { unfold patriarchal.
    unfold SN.
    intros.
    unfold patriarchal in *.
    apply H1.
    intros.
    apply H with (y := b).
    - assumption.
    - assumption.
    - apply H1.
  }
  assert (H1: patriarchal red (SN red)).
  { apply SNpatriarchal. }
  intros.
  apply (H0 _ H).
  assumption.
Qed.
(* end hide *)
  
(* Induction principle: *)
(* Let P be a predicate such that, for all SN elements a, if the 1-step *)
(* reducts of a satisfy P then a satisfies P. *)
(* Then all SN elements satisfy P TBD *)

Theorem SNind {A} {red: Red A} {P: A -> Prop}
: (forall a, (forall b, red a b -> P b) -> SN red a -> P a)
  -> (forall a, SN red a -> P a).
(* begin hide *)
Proof.
  intros.
  assert (H': patriarchal red (fun a => SN red a -> P a)).
  { unfold patriarchal.
    intros.
    apply H.
    - intros.
      apply H1.
      + assumption.
      + apply (SN_stable x).
        * assumption.
        * assumption.
    - assumption.
  }
  apply (H0 (fun a : A => SN red a -> P a)).
  - assumption.
  - assumption.
Qed.
(* end hide *)

Lemma toSN {A}{red:Red A} {x}: (forall y, red x y -> SN red y) -> SN red x.
(* begin hide *)
Proof.
  unfold SN.
  intros H P H1.
  unfold patriarchal in *.
  apply H1.
  intros y H2.
  apply H.
  - assumption.
  - assumption.
Qed.
(* end hide *)

(** ** Equivalence between different notions of SN *)

(** The standard inductive definition of strong normalisation for reduction relations is given by: *)

Inductive SN_ind {A:Type} (red: Red A) (a:A): Prop :=
  | sn_acc: (forall b, red a b -> SN_ind red b) -> SN_ind red a.
(** In this section, we prove that the definitions [SN_ind] and [SN] are equivalent, and in what follows we work only with the standard definition [SN_ind]. *)

Lemma SNstable {A} {red: Red A}: forall a, SN_ind red a -> forall b, red a b -> SN_ind red b.
(* begin hide *)
Proof.
  intros a HSN b Hred.
  inversion HSN; clear HSN.
  apply H; assumption. 
Qed.
(* end hide *)

Lemma SNTransStable {A} {red: Red A}: forall a, SN_ind red a -> forall b, (trans red) a b -> SN_ind red b.
(* begin hide *)
Proof.
  intros a HSN b Htrans.
  induction Htrans.
  - apply SNstable with a; assumption.
  - apply IHHtrans. apply SNstable with a; assumption.
Qed.    
(* end hide *)

Lemma SNTrans {A} {red: Red A}: forall a, SN_ind red a -> SN_ind (trans red) a.
(* begin hide *)
Proof.
  induction 1 as [? IHr IHTr]; apply sn_acc; intros ? HTans;
    induction HTans as [ ? ? ? | ? ? ? Hr Htr IHtr].
  - auto.
  - apply IHtr; intros; auto.
    + apply IHr in Hr; destruct Hr; auto.
    + apply IHTr in Hr; destruct Hr as [Hr]; apply Hr; constructor; auto.
Qed.
(* end hide *)

(* Definition NF {A:Type} (R : Red A) (t : A) := forall t', ~ R t t'. *)
               
(* Inductive SNalt {A:Type} (R : Red A) (t : A) : Prop := *)
(* | SN_nf : NF R t -> SNalt R t  *)
(* | SN_acc : (forall t', R t t' -> SNalt R t') -> SNalt R t. *)

Theorem SNindP {A:Type} {R: Red A} {P: A -> Prop}
: (forall t, (forall t', R t t' -> P t') -> SN_ind R t -> P t)
  -> (forall t, SN_ind R t -> P t).
Proof. Admitted. 
(*   intros IH t Ht. induction Ht. *)
(*   - apply IH. *)
(*    + intros. apply H in H0. inversion H0. *)
(*    + constructor; assumption. *)
(*   - apply IH. *)
(*    + assumption. *)
(*    + apply SN_acc. assumption. *)
(* Qed. *)
(* end hide *)

(* Lemma SNaltPat {A:Type} {R: Red A} : patriarchal R (SNalt R). *)
(* (* begin hide *) *)
(* Proof. *)
(*   unfold patriarchal. intros x H. apply SN_acc. assumption. *)
(* Qed. *)
(* (* end hide *) *)

(** The equivalence between these two definitions is proved by the following theorem: *)
(* Theorem SNaltEquivSN {A:Type} {R: Red A}: forall t, SNalt R t <-> SN R t. *)
(* (* begin hide *) *)
(* Proof. *)
(*  split; intro H. *)
(*  - inversion H. *)
(*    + apply toSN. intros t' HRtt'. *)
(*      apply H0 in HRtt'. inversion HRtt'. *)
(*    + eapply SNindP. *)
(*      * intros. apply SNpatriarchal. apply H1. *)
(*      * assumption. *)
(*  - eapply SNind. *)
(*    + intros. apply SNaltPat. apply H0. *)
(*    + assumption. *)
(* Qed. *)
(* (* end hide *)  *)
(* (** In fact, the constructor [SN_nf] which states that every normal form is [SNalt] is not essential and can be removed leading to the definition called [SN_ind]: *) *)
(* (** The equivalence between [SN_ind] and [SNalt] is given by the following theorem: *) *)
(* Lemma SN_indEquivSNalt {A:Type} {R : Red A} : forall t, SN_ind R t <-> SNalt R t. *)
(* (* begin hide *) *)
(* Proof. *)
(*  split; intro H; induction H.  *)
(*  - apply SN_acc; assumption. *)
(*  - constructor. intros t' H1. *)
(*    unfold NF in H. apply H in H1. *)
(*    inversion H1. *)
(*  - constructor. assumption. *)
(* Qed.     *)
(* (* end hide *) *)

Lemma SN_indEquivSN {A:Type} {R : Red A} : forall t, SN_ind R t <-> SN R t.
Proof.
  intro t; split.
  - intro HSN_ind. (** Suppose that [SN_ind R t] and call this hypothesis [HSN_ind]. *)
    inversion HSN_ind. (** This means that [forall b : A, R t b -> SN_ind R b]. Call this hypothesis H. *)
    eapply SNindP.
    + intros t' HredSN HSN.
      apply SNpatriarchal.
      apply HredSN.
    + assumption.
  - intro HSN. (** Suppose [(SN r t)], and call this hypothesis [HSN]. *)
    
    unfold SN in HSN. (** By definition [(SN r t)] means that [forall P : A -> Prop, patriarchal R P -> P t]. *)
    
    unfold patriarchal in HSN. (** where [patriarchal] means that [(forall x : A, (forall y : A, R x y -> P y) -> P x)]. *)
    
    apply HSN. (** Now we can instantiate the predicate [P] in[HSN] with [SN_ind R] and then we need to prove that [forall x : A, (forall y : A, R x y -> SN_ind R y) -> SN_ind R x]. *)

    intros x HSN_ind. (** To do so, let [x:A] and call [HSN_ind] the hypothesis [forall y : A, R x y -> SN_ind R y], and prove that [SN_ind R x]. *)

    apply sn_acc. (** Applying the definition of [SN_ind], i.e. the constructor [sn_acc], we need to prove that [forall y : A, R x y -> SN_ind R y] *)

    assumption. (** which is exactly the hypothesis [HSN_ind], and we conclude. *)
Qed.

(** ** The Main Theorem *)

(** Now suppose that we have two reduction relations over [A], say [red1] and [red2], a relation [R] from [A] to [B] and a reduction relation [red] over [B]. If [red1] is weakly simulated by [red] through [R], and [red2] is strongly simulated by [red] through [R] then the composition [red1 # red2] is strongly simulated by [red] through [R]: *)

Lemma WeakStrongSimul {A B} (redA1 redA2: Red A) (redB: Red B) (R: Rel A B):
  WeakSimul redA1 redB R
  -> StrongSimul redA2 redB R
  -> StrongSimul (redA1 # redA2) redB R.
(* begin hide *)
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
(* end hide *)

Lemma SimulWeakTrans {A B} (redA: Red A) (redB: Red B) (R: Rel A B)
: WeakSimul redA redB R -> WeakSimul (trans redA) redB R.
(* begin hide *)
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
(* end hide *)

Lemma SimulWeakReflTrans {A B} (redA: Red A) (redB: Red B) (R: Rel A B)
: WeakSimul redA redB R -> WeakSimul (refltrans redA) redB R.
(* begin hide *)
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

(* LENGRAND: Strong normalisation by simulation:
Assume redA is strongly simulated by redB through R.
If a is the image of some element that is SN for redB,
then a is SN for redA. TBD *)

Theorem SNbySimul {A B} {redA: Red A} {redB: Red B} {R: Rel A B}:
StrongSimul redA redB R -> forall a, Image (inverse R) (SN_ind redB) a -> SN_ind redA a.
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

(** [RCSimul] TBD *)

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
(* end hide *)

Inductive Id {A} : Red A :=
  identity: forall a:A, Id a a.

Lemma HId {A} (red: Red A): forall a, SN_ind red a <-> Image (inverse Id) (SN_ind red) a.
(* begin hide *)
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

(** Union of reduction relations *)

Inductive union {A} (red1: Red A)(red2: Red A) : Red A :=
 | union_left: forall a b,  red1 a b -> union red1 red2 a b
 | union_right: forall a b,  red2 a b -> union red1 red2 a b.

Notation "R1 \un R2" := (union R1 R2) (at level 40).

Lemma UnionStrongSimul {A} {redA red'A: Red A}:
  StrongSimul redA (redA \un red'A) Id.
(* begin hide *)
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
(* end hide *)

Lemma UnionReflStrongSimul {A} {redA red'A: Red A}:
  StrongSimul ((refltrans redA) # red'A) (redA \un red'A) Id.
(* begin hide *)
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
(* end hide *)

Lemma inclUnion {A} {redA red'A: Red A}: forall a, (SN_ind redA a) -> (forall b, (((refltrans redA) # red'A) a b) -> SN_ind (redA \un red'A) b) -> (SN_ind (redA \un red'A) a).
(* begin hide *)
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
(* end hide *)

Lemma stabComp {A} {redA: Red A}: forall a,
    SN_ind redA a -> forall b, refltrans redA a b -> SN_ind redA b.
(* begin hide *)
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

Lemma SNinclUnion {A} {redA red'A: Red A}: (forall b, SN_ind redA b -> forall c, red'A b c -> SN_ind redA c) -> (forall a, (SN_ind ((refltrans redA) # red'A) a) -> (SN_ind redA a) -> (SN_ind (redA \un red'A) a)).
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

(** The main theorem of this formalisation is named [ModStrNorm], after modular strong normalisation theorem TBD *)

Theorem ModStrNorm {A B} {redA red'A: Red A} {redB: Red B} {R: Rel A B}:
  (StrongSimul red'A redB R) -> (WeakSimul redA redB R) ->
  (forall b: A, SN_ind redA b) -> forall a, Image (inverse R) (SN_ind redB) a ->
                                 SN_ind (redA \un red'A) a.
(* begin hide *)
Proof.
  intros Hstrong Hweak HSN a HImage.
  assert(Hsplit: SN_ind (redA \un red'A) a <->
                    SN_ind (refltrans redA # red'A) a /\ SN_ind redA a).
  {
    apply SNunion.
    intros b HSN' c Hred.
    apply HSN.
  }
  destruct Hsplit as [H Hunion]; clear H.
  apply Hunion; split.
  - assert(HSNSimul: StrongSimul (refltrans redA # red'A) redB R ->
                   forall a : A, Image (inverse R) (SN_ind redB) a ->
                                 SN_ind (refltrans redA # red'A) a).
  {
   apply SNbySimul.
  }
  apply HSNSimul.
  + apply RCSimul; assumption.
  + assumption.
  - apply HSN.
Qed.
(* end hide *)

(** * Conclusion

     - This is part of a bigger project.

*)

