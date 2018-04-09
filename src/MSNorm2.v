(** * Introduction

This work is about a mechanical proof of termination of a reduction relation built up from two terminating reduction relations. A property that holds for a combined system, assuming that each subsystem has the same property, is called modular. In other words, if $P$ is a modular property that holds for both systems $A$ and $B$, then the combined system $C$, built from $A$ and $B$, also satisfies the property $P$. In the context of rewriting theory, termination is known to be a non-modular property. Nevertheless, under certain restrictions, modularity can be recovered. In this work, we present a formal/mechanic proof of a theorem stating the conditions for the termination of the union of two terminating reduction relations. 

The formalisation is constructive in the sense that it does use classical reasoning, i.e. derivations based on the law of excluded middle or proof by contradiction, for instance. This is interesting from the computational point of view because the algorithmic content of proofs can be automatically extracted as certified code %~\cite{Let2008}%. There is no extraction code in this work, which is part of a bigger project that aims to generate certified code.

The main result of this paper is a constructive formal proof of the Modular Strong Normalisation Theorem for reduction relations. A classical (i.e. non-constructive) proof of this theorem is available in %\cite{kes09}% (Theorem A.2). It uses the standard technique for proving termination using a reduction to absurdity: one assumes that termination does not hold, reaches a contradiction and conclude that termination must hold. A constructive proof of the Modular Strong Normalisation Theorem is presented in %\cite{LengrandPhD}%. This proof is not straightforward from the standard definitions of termination, instead it is done from stability. We follow Lengrand's proof

- Is it possible to avoid Lengrand's SN definition, and provide a direct proof of the theorem?

- Constructiveness (explore advantages)

- The choice of the Coq proof assistant is very natural due to the constructive logic behind it.
  
  The contributions of this work are the following:
  1. A constructive proof of the modular strong normalisation theorem in Coq
  2. An equivalence proof between different notions of Strong Normalisation (SN)
  3. We proved lemmas (? and ?) using the inductive definition of SN that we proved equivalent to the one based on patriarchal predicates.

- This paper is built from a Coq script...

*)

(** Coq background section? (Not sure) *)

(** * Reduction theory 

A relation from a set $A$ to a set $B$ is defined as a binary predicate [Rel] that receives an element of $A$ and an element of $B$ as argument:
 *)

Definition Rel (A B : Type) := A -> B -> Prop.
(** This approach is standard in type theory, where sets correspond to types in the sense that the membership relation $a \in A$ corresponds to the notion that $a$ has type $A$, written $a:A$. In this way, the fact that the elements $a:A$ and $b:B$ are related by the relation [Rel] is denoted by [Rel a b]. When $A$ and $B$ are the same set, we have the so called {\it reduction relation} over the set $A$: 
*)

Definition Red (A : Type) := Rel A A.
(* We used Lengrand's definitions and initial properties but we didn't use the [ssreflect] library. 
The constructive proof of the strong normalisation theorem is given by Lengrand, but it was not formalised by Lengrand. *)
(** We present a number of basic definitions in order to make clear the notation used in the other sections of this work. A relation [R1] is a subrelation of the relation [R2], written [R1 <# R2], if every pair of elements related by [R1] is also related by [R2]: *)

Definition Sub {A B} (R1 R2: Rel A B) : Prop :=
  forall a b, R1 a b -> R2 a b.

(** In the above definition, [A] and [B] first appear between curly brackets. Arguments between curly brackets are called implicit arguments, which are types of polymorphic functions that can be inferred from the context. A infix notation for the subrelation can be defined with an index level that defines the precedence of each operator. *)

Notation "R1 <# R2" := (Sub R1 R2) (at level 50).

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

(* (* Given two relations [red1] from [A] to [B], and [red2] from [B] to [C], one can define a new relation from [A] to [C] by composing its steps as follows: *) *)

Inductive comp {A B C} (red1: Rel A B)(red2: Rel B C) : Rel A C :=
  compose: forall b a c,  red1 a b -> red2 b c -> comp red1 red2 a c.
Notation "R1 # R2" := (comp R1 R2) (at level 40).
Arguments compose {A B C red1 red2} _ _ _ _ _ .
(* The inductive definition [comp] has just one constructor named [compose] that explicitly builds the composition of [red1] and [red2] from given reductions in [red1] and [red2]  that have a common element in [B]. *)

(** The inverse of a relation from a set [A] to a set [B] is inductively defined as the corresponding relation from [B] to [A]: *)

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

(* Transitive closure of a reduction relation *)
Inductive trans {A} (red: Red A) : Red A :=
| singl: forall a b,  red a b -> trans red a b
| transit: forall b a c,  red a b -> trans red b c -> trans red a c.

Arguments transit {A} {red} _ _ _ _ _ .

(* A reduction relation is included in its transitive closure *)
Lemma transSub {A:Type} (red: Red A) : red <# (trans red).
Proof.
  unfold Sub.
  intros a b H.
  apply singl; assumption.
Qed.

(* Given a path from a to b and a path from b to c, *)
(* construction of the path from a to c *)
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

(** The Image of a predicate via a relation ... TBD *)

Inductive Image {A B} (R:Rel A B)(P: A -> Prop): B -> Prop
  := image: forall a b, P a -> R a b -> Image R P b.

Arguments image {A B R P} _ _ _ _.

(** Strong simulation:
redA is strongly simulated by redB through R
(one step of redA yields at least one step of redB) TBD
*)

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

(* Reflexive and transitive closure of a relation *)
Inductive refltrans {A} (red: Red A) : Red A :=
| reflex: forall a,  refltrans red a a
| atleast1: forall a b,  trans red a b -> refltrans red a b.

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

(** Union of reduction relations - realocar *)

Inductive union {A} (red1: Red A)(red2: Red A) : Red A :=
 | union_left: forall a b,  red1 a b -> union red1 red2 a b
 | union_right: forall a b,  red2 a b -> union red1 red2 a b.

Notation "R1 \un R2" := (union R1 R2) (at level 40).
  
(* Lemma refl_plus_trans_is_trans {A red} : *)
(*   forall (a b c : A), (refltrans red a b) -> (trans red b c) -> *)
(*                       trans red a c. *)
(* Proof. *)
(*   Admitted. *)

(** ** Strong Normalisation

Several properties concerning strong normalisation need to be proved by induction on the SN predicate ...

*)

(** Weak simulation TBD *)

Definition WeakSimul {A B} (redA: Red A) (redB: Red B) (R: Rel A B) := 
  ((inverse R) # redA) <# ((refltrans redB) # (inverse R)).

(** If redA1 is weakely simulated by a relation 
   and redA2 is strongly simulated by the same relation
   then their composition is strongly simulated by the same relation. *)

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
(** Normal forms and Strong Normalisation TBD *)

Definition NF {A:Type} (R : Red A) (t : A) := forall t', ~ R t t'.
               
Inductive SNalt {A:Type} (R : Red A) (t : A) : Prop :=
| SN_nf : NF R t -> SNalt R t 
| SN_acc : (forall t', R t t' -> SNalt R t') -> SNalt R t.

(* begin hide *)
Theorem SNindP {A:Type} {R: Red A} {P: A -> Prop}
: (forall t, (forall t', R t t' -> P t') -> SNalt R t -> P t)
  -> (forall t, SNalt R t -> P t).
Proof.
  intros IH t Ht. induction Ht.
  - apply IH. 
   + intros. apply H in H0. inversion H0.
   + constructor; assumption.
  - apply IH.  
   + assumption.
   + apply SN_acc. assumption.
Qed.
(*
Lemma SNaltPat {A:Type} {R: Red A} : patriarchal R (SNalt R).
Proof.
  unfold patriarchal. intros x H. apply SN_acc. assumption.
Qed.
(* end hide *)
*)
(* The equivalence between these two definitions is proved by the following theorem: *)
(*
Theorem SNaltEquivSN {A:Type} {R: Red A}: forall t, SNalt R t <-> SN R t.
(* begin hide *)
Proof.
 split; intro H. 
 - inversion H.
   + apply toSN. intros t' HRtt'.
     apply H0 in HRtt'. inversion HRtt'.
   + eapply SNindP.
     * intros. apply SNpatriarchal. apply H1.
     * assumption.
 - eapply SNind.
   + intros. apply SNaltPat. apply H0.
   + assumption.
Qed.
(* end hide *)
*)
(** In fact, the constructor [SN_nf] which states that every normal form is [SNalt] is not essential and can be removed leading to the definition called [SN_ind]: *)

Inductive SN_ind {A:Type} (red: Red A) (a:A): Prop :=
  | sn_acc: (forall b, red a b -> SN_ind red b) -> SN_ind red a.

(** The equivalence between [SN_ind] and [SNalt] is given by the following theorem: *)

Lemma SN_indEquivSNalt {A:Type} {R : Red A} : forall t, SN_ind R t <-> SNalt R t.
(* begin hide *)
Proof.
 split; intro H; induction H. 
 - apply SN_acc; assumption.
 - constructor. intros t' H1.
   unfold NF in H. apply H in H1.
   inversion H1.
 - constructor. assumption.
Qed.    
(* end hide *)

(* If M is SN, so are its 1-step reducts TBD *)

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
Proof.
Admitted.

(** LENGRAND: Strong normalisation by simulation:
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
(* end hide *)

Lemma inclUnion {A} {redA red'A: Red A}: forall a, (SN_ind redA a) -> (forall b, (((refltrans redA) # red'A) a b) -> SN_ind (redA \un red'A) b) -> (SN_ind (redA \un red'A) a).
(* begin hide *)
Proof.
  intros a HSN.
  induction HSN.
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
        ** apply transSub in H1.
           apply atleast1 in H1.
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

