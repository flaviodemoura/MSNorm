(* begin hide *)

(* Require Import NormalisationTheory. *)


(** * Reduction theory 

 The type of relations is defined as follows: 

*)

Definition Rel (A B:Type) := A -> B -> Prop.

(** Reduction relations are relations over a given set $A$: *)
Definition Red (A:Type) := Rel A A.

(* begin hide *)

(* Inclusion of a relation in another relation *)
Definition Sub {A B} (R1 R2: Rel A B) : Prop := forall a b, R1 a b -> R2 a b.
Notation "R1 <# R2" := (Sub R1 R2) (at level 50).

(* Inclusion is reflexive *)
Lemma SubRefl {A B} (R: Rel A B) : R <# R.
Proof.
  unfold Sub.
  intros a b H.
  exact H.
Qed.

(* Inclusion is transitive *)
Lemma SubTrans {A B} (R2 R1 R3: Rel A B) : R1 <# R2 -> R2 <# R3 -> R1 <# R3.
Proof.
  unfold Sub.
  intros Hr1 Hr2.
  intros a b H.
  apply Hr2, Hr1.
  exact H.
Qed.

(* Double inclusion, i.e. equivalence *)
Definition Equiv {A B} (R1 R2: Rel A B) := R1 <# R2 /\ R2 <# R1.
Notation "R1 -- R2" := (Equiv R1 R2) (at level 50).

(* Composition of relations *)
Inductive comp {A B C} (red1: Rel A B)(red2: Rel B C) : Rel A C :=
  compose: forall b a c,  red1 a b -> red2 b c -> comp red1 red2 a c
.
Notation "R1 # R2" := (comp R1 R2) (at level 40).
Arguments compose {A B C red1 red2} _ _ _ _ _ .

(* Inverse of a relation *)
Inductive inverse {A B} (R: Rel A B) : Rel B A :=
  inverseof: forall a b, R a b -> inverse R b a
.

(* Composition is associative *)
Lemma compTrans {A B C D} (R1: Rel A B)(R2: Rel B C)(R3: Rel C D)
  : (R1 # R2) # R3 -- R1 # (R2 # R3).
Proof.
  unfold Equiv. split.
  - unfold Sub.
    intros a b H.
    inversion H as [a' b' d Hc Hr3 Heq Heq']; subst.
    inversion Hc as [a'' b' d Hr1 Hr2 Heq Heq']; subst.
    apply (compose a'').
    + exact Hr1.
    + apply (compose a').
      * exact Hr2.
      * exact Hr3.
  - unfold Sub.
    intros a b H.
    inversion H; subst.
    inversion H1; subst.
    apply (compose b1).
    + apply (compose b0).
      * assumption.
      * assumption.
    + assumption.
Qed.

(* Composition is monotonous *)
Lemma SubComp {A B C} (R1 R2: Rel A B)(R3 R4: Rel B C) 
: R1 <# R2 -> R3 <# R4 -> (comp R1 R3) <# (comp R2 R4).
Proof.
  unfold Sub.
  intros H H0.
  intros a b H'.
  inversion H'; subst.
  apply (compose b0).
  + apply H in H1.
    assumption.
  + apply H0 in H2.
    assumption.
Qed.

(* Transitive closure of a reduction relation *)
Inductive trans {A} (red: Red A) : Red A :=
| singl: forall a b,  red a b -> trans red a b
| transit: forall b a c,  red a b -> trans red b c -> trans red a c
.

Arguments transit {A} {red} _ _ _ _ _ .

(* A reduction relation is included in its transitive closure *)
Lemma transSub {A:Type} (red: Red A) : red <# (trans red).
Proof.
  unfold Sub.
  intros a b H.
  apply singl; assumption.
Qed.

(* Given a path from a to b and a path from b to c,
construction of the path from a to c *) 
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

(* Transitive closure is monotonous *)
Lemma SubTrans1 {A} (red1 red2: Red A) : red1 <# red2 -> (trans red1) <# (trans red2).
Proof.
  unfold Sub.
  intros H a b H0.
  induction H0.
  - apply H in H0.
    apply singl; assumption.
  - apply H in H0.
    apply (transit b).
    + exact H0.
    + apply IHtrans.
Qed.

(* Image of a predicate via a relation *)
Inductive Image {A B} (R:Rel A B)(P: A -> Prop): B -> Prop
  := image: forall a b, P a -> R a b -> Image R P b.

Arguments image {A B R P} _ _ _ _.

(***************)
(* Simulations *)

(* Strong simulation:
redA is strongly simulated by redB through R
(one step of redA yields at least one step of redB)
 *)
Definition StrongSimul {A B} (redA: Red A) (redB: Red B) (R: Rel A B) := 
  ((inverse R) # redA) <# ((trans redB) # (inverse R)).

(* The fact that redA is strongly simulated by redB is
monotonic in redB and anti-monotonic in redA *)
Lemma SimulMonotonic {A B} (redA1 redA2: Red A) (redB1 redB2: Red B) (R: Rel A B):
  redA2 <# redA1 -> redB1 <# redB2 -> StrongSimul redA1 redB1 R -> StrongSimul redA2 redB2 R.
Proof.
  unfold StrongSimul.
  intros H H0.
  intros H2.
  apply (SubTrans ((inverse R) # redA1)).
  - apply SubComp.
    + apply SubRefl.
    + apply H.
  - apply (SubTrans ((trans redB1) # (inverse R))).
    + apply H2.
    + apply SubComp.
      * apply SubTrans1 in H0; apply H0.
      * apply SubRefl.
Qed.

(* If redA1 and redA2 are strongly simulated by the same relation,
so is their composition *)
Lemma SimulBoth {A B} (redA1 redA2: Red A) (redB: Red B) (R: Rel A B):
  StrongSimul redA1 redB R
  -> StrongSimul redA2 redB R
  -> StrongSimul (redA1 # redA2) redB R.
Proof.
  unfold StrongSimul.
  intros H1 H2.
  unfold Sub.
  intros a b H3.
  inversion H3;subst.
  inversion H0;subst.
  unfold Sub in H1.
  assert(H': (inverse R # redA1) a b1).
  { apply (compose b0).
    - assumption.
    - assumption.
  }
  apply H1 in H'.
  inversion H'; subst.
  assert(H'': (inverse R # redA2) b2 b).
  { apply (compose b1).
    - assumption.
    - assumption.
  }
  apply H2 in H''.
  inversion H''; subst.
  apply (compose b3).
  - apply (tailtransit b2).
    + assumption.
    + assumption.
  - assumption.
Qed.

(* If redA is strongly simulated, so is its transitive closure *)
Lemma SimulTrans {A B} (redA: Red A) (redB: Red B) (R: Rel A B)
  : StrongSimul redA redB R -> StrongSimul (trans redA) redB R.
Proof.
  unfold StrongSimul.
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
    apply tailtransit with b0; assumption.
    assumption.
Qed.

(* Reflexive and transitive closure of a relation *)
Inductive refltrans {A} (red: Red A) : Red A :=
| reflex: forall a,  refltrans red a a
| atleast1: forall a b,  trans red a b -> refltrans red a b
.

(* The transitive closure is equivalent to the composition of the
relation with its reflexive-transitive closure *)
Lemma trans2refltrans {A} {red: Red A}: trans red -- red # (refltrans red).
Proof.
  unfold Equiv.
  unfold Sub.
  split.
  - intros a b H.
    inversion H; subst.
    + apply (compose b).
      * assumption.
      * apply reflex.
    + apply (compose b0).
      * assumption.
      * apply atleast1; assumption.
  - intros a b H.
    inversion H; subst.
    inversion H1; subst.
    + apply singl in H0; assumption.
    + apply (transit b0).
      * assumption.
      * assumption.
Qed.


(*******************************)
(* Strong Normalisation theory *)

(* What it means for a predicate to be patriarchal *)
Definition patriarchal {A} (red:Red A) (P:A -> Prop): Prop
  := forall x, (forall y, red x y -> P y) -> P x.

(* a is strongly normalising for red *)
Definition SN {A:Type} (red:Red A) (a:A): Prop
  := forall P, patriarchal red P -> P a.

(* If all 1-step reducts of a are SN, so is a *)
Lemma toSN {A}{red:Red A} {x}: (forall y, red x y -> SN red y) -> SN red x.
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

(* Being SN is a patriarchal predicate *)
Lemma SNpatriarchal {A} {red: Red A}: patriarchal red (SN red). 
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

(* If M is SN, so are its 1-step reducts *)
Lemma SNstable {A} {red: Red A}: forall M, SN red M -> forall N, red M N -> SN red N.
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

(* Induction principle:
Let P be a predicate such that, for all SN elements a, if the 1-step
reducts of a satisfy P then a satisfies P.
Then all SN elements satisfy P *)

Theorem SNind {A} {red: Red A} {P: A -> Prop}
  : (forall a, (forall b, red a b -> P b) -> SN red a -> P a)
    -> (forall a, SN red a -> P a).
Proof.
  intros.
  assert (H': patriarchal red (fun a => SN red a -> P a)).
  { unfold patriarchal.
    intros.
    apply H.
    - intros.
      apply H1.
      + assumption.      
      + apply (SNstable x).
        * assumption.
        * assumption.
    - assumption.
  }
  apply (H0 (fun a : A => SN red a -> P a)).
  - assumption.
  - assumption.
Qed.

(* Being patriarchal for red1 is monotonic in red1 *)
Lemma Patriarchalmonotonic {A} {red1 red2: Red A}: 
  red1 <# red2 -> forall P, patriarchal red1 P -> patriarchal red2 P.
Proof.
  unfold Sub; unfold patriarchal.
  intros H0 P H1 a H2.
  apply H1.
  intros y H3.
  apply H2.
  apply H0.
  apply H3.
Qed.

(* Being SN for red1 is anti-monotonic in red1 *)
Lemma SNmonotonic {A} {red1 red2: Red A}: red1 <# red2 -> forall a, SN red2 a -> SN red1 a.
Proof.
  unfold SN.
  intros H0 a H1 P H2.
  apply H1.
  apply (Patriarchalmonotonic H0 P H2).
Qed.

(* Being SN for a relation is the same thing as being SN for its transitive closure *)
Lemma SNSNtrans {A} {red: Red A}: forall a, SN red a <-> SN (trans red) a.
Proof.
  assert(forall M, SN red M -> forall N, refltrans red M N -> SN (trans red) N).
  { apply (@SNind _ _ (fun M => forall N, refltrans red M N -> SN (trans red) N)).
    intros M IH MSN.
    assert(forall N, trans red M N -> SN (trans red) N).
    { intros N H.
      apply trans2refltrans in H.
      inversion H; subst.
      apply (IH b); assumption.
    }
    assert(H'': patriarchal (trans red) (SN (trans red))).
    { apply (@SNpatriarchal _ (trans red)). }
    unfold patriarchal in H''.
    intros N H1.
    apply H'' in H; clear H''.
    inversion H1; subst.
    - assumption.
    - apply (SNstable M).
      + assumption.
      + assumption.
  }
  split.
  - intros.
    apply (H a).
    + assumption.
    + apply reflex.
  - apply SNmonotonic.
    apply transSub.
Qed.

(* Strong Induction principle:
Let P be a predicate such that, for all SN elements a, if the n-step
reducts of a satisfy P then a satisfies P.
Then all SN elements satisfy P.

This theorem is stronger than the previous version, since the
induction hypothesis can be applied not only to the 1-step reducts,
but to all n-step reducts. In the natural numbers, we can assume the
IH holds not only for n-1, but for all m<n.
 *)

Theorem SNsind {A} {red: Red A} {P: A -> Prop}
  : (forall a, (forall b, trans red a b -> P b) -> SN red a -> P a)
    -> (forall a, SN red a -> P a).
Proof.
  intros H a H0.
  apply (proj1(SNSNtrans a)) in H0.
  generalize dependent a.
  apply SNind.
  intros a H0 H1.
  apply H.
  - assumption.
  - apply SNSNtrans.
    assumption. 
Qed.

(* Strong normalisation by simulation:
Assume redA is strongly simulated by redB through R.
If a is the image of some element that is SN for redB,
then a is SN for redA.
 *)
Theorem SNbySimul {A B} {redA: Red A} {redB: Red B} {R: Rel A B}:
  StrongSimul redA redB R -> forall a, Image (inverse R) (SN redB) a -> SN redA a.
Proof.
  intros H M H0.
  inversion H0.
  clear H0 H3 b.
  generalize dependent M. generalize dependent a.
  apply (@SNsind _ _ (fun a => forall M : A, inverse R a M -> SN redA M)).
  intros N H0 SNN M H1.
  apply SNpatriarchal.
  intros M' H2.
  unfold StrongSimul in H; unfold Sub in H.
  assert(H': (inverse R # redA) N M').
  - apply (compose M).
    + assumption.
    + assumption.
  - apply H in H'.
    inversion H'; subst.
    apply (H0 b).
    + assumption.
    + assumption.
Qed.

(* end hide *)


(* Union of reduction relations *)
Inductive union {A} (red1: Red A)(red2: Red A) : Red A :=
| union_left: forall a b,  red1 a b -> union red1 red2 a b
| union_right: forall a b,  red2 a b -> union red1 red2 a b
.

Notation "R1 \un R2" := (union R1 R2) (at level 40).

(* Lemma refl_plus_trans_is_trans {A red} : *)
(*   forall (a b c : A), (refltrans red a b) -> (trans red b c) -> *)
(*                       trans red a c. *)
(* Proof. *)
(*   Admitted. *)

Definition WeakSimul {A B} (redA: Red A) (redB: Red B) (R: Rel A B) := 
  ((inverse R) # redA) <# ((refltrans redB) # (inverse R)).

(* If redA1 is weakely simulated by a relation 
   and redA2 is strongly simulated by the same relation
   then their composition is strongly simulated by the same relation. *)
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

Inductive SN_ind {A:Type} (red: Red A) (a:A): Prop :=
| sn_acc: (forall b, red a b -> SN_ind red b) -> SN_ind red a.

Definition NF {A:Type} (R : Red A) (t : A) := forall t', ~ R t t'.

Inductive SNalt {A:Type} (R : Red A) (t : A) : Prop :=
| SN_nf : NF R t -> SNalt R t 
| SN_acc : (forall t', R t t' -> SNalt R t') -> SNalt R t.

Lemma SNaltPat {A:Type} {R: Red A} : patriarchal R (SNalt R).
Proof.
  unfold patriarchal. intros x H. apply SN_acc. assumption.
Qed.

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

Lemma SN_indEquivSNalt {A:Type} {R : Red A} : forall t, SN_ind R t <-> SNalt R t.
Proof.
  split; intro H; induction H. 
  - apply SN_acc; assumption.
  - constructor. intros t' H1.
    unfold NF in H. apply H in H1.
    inversion H1.
  - constructor. assumption.
Qed.    

(* begin hide *)

Theorem SNaltEquivSN {A:Type} {R: Red A}: forall t, SNalt R t <-> SN R t.
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

Lemma SN_ind_is_SN {A} {red:Red A}: forall a, SN_ind red a -> SN red a.
Proof.
Admitted.

Lemma SN_is_SN_ind {A} {red:Red A}: forall a, SN red a -> SN_ind red a.
Proof.
Admitted.

Lemma SN_eq_SN_ind {A} {red:Red A}: forall a, SN red a <-> SN_ind red a.
Proof.
Admitted.

Lemma RCSimul {A B} {redA red'A: Red A} {redB: Red B} {R: Rel A B}:
  (StrongSimul red'A redB R) -> (WeakSimul redA redB R) ->
  (StrongSimul ((refltrans redA) # red'A) redB R).
Proof.
  intros Hst Hwk.
  assert (Hrfl:  WeakSimul (refltrans redA) redB R).
  {
    apply SimulWeakReflTrans; assumption.
  }
  clear Hwk.
  apply WeakStrongSimul; assumption.
Qed.

Inductive Id {A} : Rel A A :=
  identity: forall a:A, Id a a.

Lemma inverseId {A}: forall a b :A, inverse Id a b -> a = b.
Proof.
  intros.
  inversion H; subst.
  inversion H0; subst.
  reflexivity.
Qed.

Lemma HId {A} (red: Red A): forall a, SN red a <-> Image (inverse Id) (SN red) a. 
Proof.
  split.
  - intros H.
    apply image with a.
    + assumption.
    + apply inverseof. apply identity.
  - intros H.
    inversion H; subst.
    apply inverseId in H1.
    rewrite H1 in H0; assumption.
Qed.

Lemma UnionStrongSimul {A} {redA red'A: Red A}:
  StrongSimul redA (redA \un red'A) Id.
Proof.
  unfold StrongSimul.
  unfold Sub.
  intros a b HredA.
  inversion HredA; subst.
  apply inverseId in H. subst.
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
      apply inverseId in H0. subst.
      constructor; assumption.
    + apply inverseof. apply identity.
  - intros.
    generalize dependent b0.
    apply inverseId in H0. subst.
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
           apply inverseId in H2. subst.
           assumption.
      * apply inverseof. apply identity.
Qed.

Lemma inclUnion {A} {redA red'A: Red A}: forall a,
    (SN redA a) ->
    (forall b, (((refltrans redA) # red'A) a b) -> SN (redA \un red'A) b) ->
    (SN (redA \un red'A) a).
Proof.
  intros a HSN Hyp.
  apply SN_ind_is_SN.
  apply SN_is_SN_ind in HSN.
  generalize dependent Hyp.
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
  - apply SN_is_SN_ind.
    apply Hyp.
    apply compose with a.
    + apply reflex.
    + assumption.
Qed.

Lemma redTrans {A} {redA: Red A}: forall a b c,
    redA a b -> redA b c -> redA a c.
Proof.
  intros.
  Admitted.
  
Lemma stabComp {A} {redA: Red A}: forall a b,
    SN redA a -> refltrans redA a b -> SN redA b.
Proof.
  intros a b HSN Hrefl.
  induction Hrefl.
  - assumption.
  - apply SNstable with (a).
    + assumption.
    + induction H.
      * assumption.
      * assert(H': SN redA b).
        {
          apply SNstable with (M := a); assumption.
        }
        apply IHtrans in H'.
        apply redTrans with b; assumption. 
Qed.
    
Lemma SNinclUnion {A} {redA red'A: Red A}: forall a,
    (forall b c, SN redA b -> red'A b c -> SN redA c) ->
    (SN ((refltrans redA) # red'A) a) ->
    (SN redA a) ->
    (SN (redA \un red'A) a).
Proof.
  intros a HStable HSNcomp.
  apply SN_is_SN_ind in HSNcomp.
  induction HSNcomp.
  intros HSN.
  apply inclUnion.
  - assumption.
  - intros b Hcomp.    
    apply H0.
    + assumption.
    + inversion Hcomp; subst.
      assert(H': SN redA b0).
      {
        apply stabComp with a; assumption.
      }
      apply HStable with b0; assumption.
Qed.

Lemma SNunion {A} {redA red'A: Red A}: 
  (forall a b, SN redA a -> red'A a b -> SN redA b) ->
  forall c, (SN (redA \un red'A) c) <-> (SN ((refltrans redA) # red'A) c) /\ ((SN redA) c).
Proof.
  intros Hst c. split.
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
  - intro Hand. destruct Hand as [Hcomp HredA].
    assert (HSNunion1: (SN ((refltrans redA) # red'A) c) -> (SN redA c) -> (SN (redA \un red'A) c)).
    {
      apply SNinclUnion.
      intro b. apply Hst. 
    }
    apply HSNunion1; assumption.
Qed.

(** THINK MORE ABOUT THIS
   The third condition of the lemma states that the set A coincides with the set of strongly normalizing terms w.r.t. redA, i.e. A = SN^{redA}. Nevertheless, it is trivial that SN^{redA} is a subset of A by its definition. The other direction is expressed by the formula (forall b: A, SN redA b) stating that all elements of A are SN w.r.t. redA.
 *)

Theorem LexSimul {A B} {redA: Red A} {red'A: Red A} {redB: Red B} {R: Rel A B}:
  (StrongSimul red'A redB R) -> (WeakSimul redA redB R) ->
  (forall b: A, SN redA b) ->
  forall a, Image (inverse R) (SN redB) a -> SN (redA \un red'A) a.
Proof.
  intros H1 H2 H3 a H4.
  unfold StrongSimul in H1; unfold WeakSimul in H2.
  unfold Sub in *.
  assert(H': StrongSimul (refltrans redA # red'A) (redB) R).
  { unfold StrongSimul; unfold Sub.
    intros.
    inversion H; subst.
    inversion H5; subst.
    admit.
  }
Admitted.

(* end hide *)



