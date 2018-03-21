(* begin hide *)

Require Import NormalisationTheory.

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

Lemma inclUnion {A} {redA red'A: Red A}: forall a, (SN redA a) -> (forall b, (((refltrans redA) # red'A) a b) -> SN (redA \un red'A) b) -> (SN (redA \un red'A) a).
Proof.
  intros a b HSN Hyp.
  apply SN_ind_is_SN.
  Admitted.
  (* apply SN_is_SN_ind in HSN. *)
  (* assert (Hyp' : (refltrans redA # red'A) a b -> SN_ind (redA \un red'A) b). *)
  (* {  *)
  (*   intro Hrefl. *)
  (*   apply SN_is_SN_ind. *)
  (*   apply Hyp; assumption. *)
  (* } *)
  (* clear Hyp. *)
  (* generalize dependent Hyp'. *)
  (* generalize dependent b. *)
  (* induction HSN. *)
  (* intros b' Hyp. *)
(*   assert (H': (redA \un red'A) a b). *)
(*   { *)
(*     admit. *)
(*   } *)
(*   apply sn_acc with b. *)
(*   - assumption. *)
(*   - apply IHHSN with b'. *)
(*     intro Hrefl. *)
(*     apply Hyp. *)
(*     assert (Hcomp: redA a b ->  (refltrans redA # red'A) b b' -> (refltrans redA # red'A) a b'). *)
(*     { *)
(*       admit. *)
(*     } *)
(*     apply Hcomp; assumption. *)
(* Admitted. *)

Lemma SNinclUnion {A} {redA red'A: Red A}: forall a, (forall b c, SN redA b -> red'A b c -> SN redA c) -> (SN ((refltrans redA) # red'A) a) -> (SN redA a) -> (SN (redA \un red'A) a).
      Proof.
        Admitted.
    (* intros a HSNcomp HSN. *)
    (* apply SN_eq_SN_ind. *)
    (* assert (HSN_indcomp: SN_ind (refltrans redA # red'A) a). *)
    (* { generalize HSNcomp. *)
    (*   apply SN_eq_SN_ind. } *)
    (* clear HSNcomp. *)
    (* assert (HSN_ind : SN_ind redA a). *)
    (* { generalize HSN. *)
    (*   apply SN_eq_SN_ind. } *)
    (* clear HSN. *)
    (* generalize dependent HSN_ind. *)
    (* induction HSN_indcomp.  *)
    (* intro HSN_ind. *)
    (* assert (Hincl:  (SN redA a) -> ((((refltrans redA) # red'A) a b) -> SN (redA \un red'A) b) -> (SN (redA \un red'A) a)). *)
    (* { *)
    (*   apply inclUnion. *)
    (* } *)
    (* assert (Heq: SN (redA \un red'A) a <-> SN_ind (redA \un red'A) a). *)
    (* { *)
    (* apply SN_eq_SN_ind. *)
    (* } *)
    (* destruct Heq as [Heq1 Heq2]. *)
    (* apply Heq1. *)
    (* apply Hincl. *)
    (* - apply SN_eq_SN_ind in HSN_ind; assumption. *)
    (* - intro Hcomp. *)
    (*   apply SN_eq_SN_ind. *)
    (*   apply IHHSN_indcomp. *)
    (*   (* usar a estabilidade *) *)
    (*   Lemma stabComp {A} {redA red'A: Red A}: forall b, SN_ind (refltrans redA # red'A) b -> (forall a b, SN redA a -> red'A a b -> SN redA b) -> SN_ind redA b. *)
    (*   Proof. *)
    (*   Admitted. *)
    (*   (* fim do lema de estabilidade *) *)
    (*   assert (HstabComp: SN_ind (refltrans redA # red'A) b -> (forall a b, SN redA a -> red'A a b -> SN redA b) -> SN_ind redA b). *)
    (*   { *)
    (*   apply stabComp.   *)
    (*   } *)
    (*   apply HstabComp. *)
    (*   + assumption. *)
    (*   + Admitted. *)

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



