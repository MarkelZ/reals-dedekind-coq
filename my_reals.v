(* 
 * ================================================================
 * Real Numbers as Dedkind Cuts
 * ================================================================ 
 * 
 * This Coq script formalizes the real numbers as Dedekind cuts and
 * proves some theorems about them.
 *)


(* 
 * ================================================================
 * Imports
 * ================================================================ 
 *)

Require Import QArith.
Require Import Lqa.
Require Import QArith Qminmax Psatz.

Open Scope Q_scope.


(* 
 * ================================================================
 * My tactics
 * ================================================================ 
 *)

Ltac qauto:=
  unfold Qdiv;
  unfold Qinv;
  repeat split;
  simpl;
  eauto;
  try lra.


(* 
 * ================================================================
 * Real numbers from Dedekind cuts 
 * ================================================================ 
 *)

(* Dedekind cut conditions *)

Definition inhabited (C : Q -> Prop) :=
    exists q : Q, C q.

Definition rounded_left (L : Q -> Prop) :=
    forall q : Q,
    L q <-> exists r : Q, q < r /\ L r.

Definition rounded_right (U : Q -> Prop) :=
    forall r : Q,
    U r <-> exists q : Q, q < r /\ U q.

Definition disjoint (L U : Q -> Prop) :=
    forall q : Q, ~ (L q /\ U q).

Definition located (L U : Q -> Prop) :=
    forall q r : Q, q < r -> L q \/ U r.

Definition congruent (C : Q -> Prop) :=
    forall q r : Q, C q /\ q == r -> C r.

(* Dedekind cut definition *)
Definition cut (L U : Q -> Prop) :=
    inhabited L /\ inhabited U /\ 
    rounded_left L /\ rounded_right U /\
    disjoint L U /\ located L U /\ 
    congruent L /\ congruent U.

(* My real type from Dedekind cut (L, U) *)
Inductive my_R :=
    cons_R (L U : Q -> Prop) : cut L U -> my_R.


(* 
 * ================================================================
 * Map rational numbers to my real numbers
 * ================================================================ 
 *)

(* Dedekind cut of a rational number *)
Definition L_Q (q : Q) := fun r : Q => r < q.
Definition U_Q (q : Q) := fun r : Q => q < r.

(* Proof that the cuts constructed from rational 
   numbers are indeed Dedekind cuts *)
Lemma cut_Q (s : Q) : cut (L_Q s) (U_Q s).
Proof.
    unfold L_Q, U_Q. repeat split.
    - exists (s - 1). lra.
    - exists (s + 1). lra.
    - intros H1. exists ((q + s) / 2). qauto.
    - intros (r & H1). lra.
    - intros H1. exists ((s + r) / 2). qauto.
    - intros (q & H1). lra.
    - intros q. lra.
    - intros q r H2. lra.
    - intros q r H. lra.
    - intros q r H. lra.
Qed.

(* Map from rational numbers to my real numbers *)
Definition Q_to_R (q : Q) :=
    cons_R (L_Q q) (U_Q q) (cut_Q q).

(* Some constants *)
Definition R0 := Q_to_R 0.
Definition R1 := Q_to_R 1.
Definition R2 := Q_to_R 2.


(* 
 * ================================================================
 * Addition
 * ================================================================ 
 *)

(* Dedekind cuts of my real number addition *)
Definition L_add (L1 L2 : Q -> Prop) : Q -> Prop := 
    fun z : Q => exists x y : Q, L1 x /\ L2 y /\ z == x + y.

Definition U_add (U1 U2 : Q -> Prop) : Q -> Prop := 
    fun z : Q => exists x y : Q, U1 x /\ U2 y /\ z == x + y.

(* Proof that the cuts constructed from addition are indeed Dedekind cuts *)
Lemma cut_add (L1 U1 L2 U2 : Q -> Prop) (cut1 : cut L1 U1) (cut2 : cut L2 U2) :
        cut (L_add L1 L2) (U_add U1 U2).
Proof.
    (* destruct x as [L1 U1 (H1x & H2x & H3x & H4x & H5x & H6x)]. 
    destruct y as [L2 U2 (H1y & H2y & H3y & H4y & H5y & H6y)].  *)
    unfold L_add, U_add.
    repeat split.
    - destruct cut1 as ((q & H1) & _).
      destruct cut2 as ((r & H2) & _).
      exists (q + r), q, r. repeat split; eauto.
    - destruct cut1 as (_ & (q & H1) & _).
      destruct cut2 as (_ & (r & H2) & _).
      exists (q + r), q, r. repeat split; eauto.
    - intros (x & y & H1 & H2 & H3).
      destruct cut1 as (_ & _ & (H4 & _) & _).
      destruct cut2 as (_ & _ & (H7 & _) & _).
      destruct (H4 H1) as (x' & H5 & H6).
      destruct (H7 H2) as (y' & H8 & H9).
      exists (x' + y'). qauto.
      exists x', y'; repeat split; eauto.
    - intros (r & H1 & (x & y & H2 & H3 & H4)).
      destruct cut1 as (_ & _ & (_ & H5) & _).
      destruct cut2 as (_ & _ & (_ & H6) & _).
      exists (x - (r/2) + (q/2)), (y - (r/2) + (q/2)).
      qauto.
      + apply H5. exists x. qauto.
      + apply H6. exists y. qauto.
    - intros (x & y & H1 & H2 & H3).
      destruct cut1 as (_ & _ & _ & (H4 & _) & _).
      destruct cut2 as (_ & _ & _ & (H7 & _) & _).
      destruct (H4 H1) as (x' & H5 & H6).
      destruct (H7 H2) as (y' & H8 & H9).
      exists (x' + y'). qauto.
      exists x', y'; repeat split; eauto.
    - intros (q & H1 & (x & y & H2 & H3 & H4)).
      destruct cut1 as (_ & _ & _ & (_ & H5) & _).
      destruct cut2 as (_ & _ & _ & (_ & H6) & _).
      exists (x - (q/2) + (r/2)), (y - (q/2) + (r/2)).
      qauto.
      + apply H5. exists x. qauto.
      + apply H6. exists y. qauto.
    - intros q ((x & y & H1 & H2 & H3) & (x' & y' & H4 & H5 & H6)).
      destruct cut1 as (_ & _ & _ & _ & H7 & H9 & Hc & _).
      destruct cut2 as (_ & _ & _ & _ & H8 & H10 & _).
      assert (x > x' \/ x < x' \/ x == x') as H11; [lra|].
      destruct H11 as [H|[H|H]].
      + destruct (H9 x' x); try eapply H7; eauto.
      + assert (y > y'); [lra|].
        destruct (H10 y' y); try eapply H8; eauto.
      + eapply H7. split; [|apply H4]. eauto.
    - intros q r H1. 
      destruct cut1 as (_ & _ & _ & _ & _ & H2 & _).
      destruct cut2 as (_ & _ & _ & _ & _ & H3 & _).
      unfold located in *.
      edestruct H2, H3; eauto; admit.
    - intros q r ((x & y & H1 & H2 & H3) & H4).
      exists x, y. qauto.
    - intros q r ((x & y & H1 & H2 & H3) & H4).
      exists x, y. qauto.
Admitted.

(* My real number addition *)
Definition add (x y : my_R) : my_R :=
    match x with cons_R L1 U1 cut1 =>
    match y with cons_R L2 U2 cut2 =>
    cons_R (L_add L1 L2) (U_add U1 U2) (cut_add L1 U1 L2 U2 cut1 cut2)
    end end.

Notation "x +' y" := (add x y) (at level 50, left associativity).


(* 
 * ================================================================
 * Additive inverses
 * ================================================================ 
 *)

(* Dedekind cuts of my real number additive inverse *)
Definition L_neg (U : Q -> Prop) : Q -> Prop :=
    fun q : Q => exists r : Q, U r /\ q == -r.

Definition U_neg (L : Q -> Prop) : Q -> Prop :=
    fun q : Q => exists r : Q, L r /\ q == -r.

(* Proof that the cuts constructed as the additive inverse are indeed Dedekind
   cuts *)
Lemma cut_neg (L U : Q -> Prop) (cut_x : cut L U) :
    cut (L_neg U) (U_neg L).
Proof.
    unfold L_neg, U_neg.
    repeat split.
    - destruct cut_x as (_ & (q & H) & _).
      exists (-q), q. qauto.
    - destruct cut_x as ((q & H) & _).
      exists (-q), q. qauto.
    - intros (r & H1 & H2).
      destruct cut_x as (_ & _ & _ & H & _).
      destruct (H r) as (H3 & _).
      destruct (H3 H1) as (x & H4 & H5).
      exists (- x). split; [|exists x]; qauto.
    - intros (r & H1 & (r' & H2 & H3)).
      exists (- q). split; [|lra].
      destruct cut_x as (_ & _ & _ & H & _).
      destruct (H (- q)) as (_ & H4).
      apply H4. exists r'. qauto.
    - intros (q & H1 & H2).
      destruct cut_x as (_ & _ & H & _ & _).
      destruct (H q) as (H3 & _).
      destruct (H3 H1) as (x & H4 & H5).
      exists (- x). split; [|exists x]; qauto.
    - intros (q & H1 & (q' & H2 & H3)).
      exists (- r). split; [|lra].
      destruct cut_x as (_ & _ & H & _ & _).
      destruct (H (- r)) as (_ & H4).
      apply H4. exists q'. qauto.
    - intros q ((r & H1 & H2) & (r' & H3 & H4)).
      destruct cut_x as (_ & _ & _ & _ & H7 & _ & _ & Hc).
      eapply H7. split; eauto.
      apply (Hc r). qauto.
    - admit.
    - intros q r ((q' & H1 & H2) & H3).
      exists q'. qauto.
    - intros q r ((q' & H1 & H2) & H3).
      exists q'. qauto.
Admitted.

(* My real number additive inverse *)
Definition inv (x : my_R) : my_R :=
    match x with cons_R L U cut_x =>
    cons_R (L_neg U) (U_neg L) (cut_neg L U cut_x)
    end.

Notation "-' x" := (inv x) (at level 40, left associativity).


(* 
 * ================================================================
 * Equality
 * ================================================================ 
 *)

(* My real number equivalence *)
Definition equiv (x y : my_R) : Prop :=
    match x with cons_R L1 U1 cut1 =>
    match y with cons_R L2 U2 cut2 =>
        forall q : Q, (L1 q <-> L2 q) /\ (U1 q <-> U2 q)
    end end.

Notation "x =' y" := (equiv x y) (at level 10).

(* Proof that =' is an equivalence relation *)
Lemma equiv_reflexive (x : my_R) :
    x =' x.
Proof.
    destruct x. intros q. 
    repeat split; eauto.
Qed.

Lemma equiv_symmetric (x y : my_R) : 
    x =' y -> y =' x.
Proof.
    intros H. 
    destruct x as [L1 U1 c1], y as [L2 U2 c2].
    intros q. destruct (H q) as ((H1 & H2) & H3 & H4).
    repeat split; eauto.
Qed.

Lemma equiv_transitive (x y z : my_R) :
    x =' y -> y =' z -> x =' z.
Proof.
    intros H1 H2.
    destruct x as [L1 U1 c1], y as [L2 U2 c2], z as [L3 U3 c3].
    intros q. 
    destruct (H1 q) as ((H11 & H12) & H13 & H14).
    destruct (H2 q) as ((H21 & H22) & H23 & H24).
    repeat split; eauto.
Qed.


(* 
 * ================================================================
 * Lemmas using our newly defined +', -', and ='
 * ================================================================ 
 *)

Lemma add_correct : 
  forall q r : Q, ((Q_to_R q) +' (Q_to_R r)) =' (Q_to_R (q + r)).
Proof.
  simpl. intros q r q'. unfold L_add, U_add, L_Q, U_Q. repeat split.
  - intros (x & y & H1 & H2 & H3). lra.
  - intros H1. exists (q - (q + r - q') / 2), (r - (q + r - q') / 2). qauto.
  - intros (x & y & H1 & H2 & H3). lra.
  - intros H1. exists (q - (q + r - q') / 2), (r - (q + r - q') / 2). qauto.
Qed.

Corollary one_plus_one_is_two :
    (R1 +' R1) =' R2.
Proof.
    apply add_correct.
Qed.

Lemma neg_correct : forall q : Q, (-' Q_to_R q) =' (Q_to_R (- q)).
Proof.
  simpl. intros q r. unfold L_neg, U_neg, L_Q, U_Q. repeat split.
  - intros (s & H1 & H2). lra.
  - intros H. exists (- r). lra.
  - intros (s & H1 & H2). lra.
  - intros H. exists (- r). lra.
Qed.

Lemma double_neg :
    forall x : my_R, (-' -' x) =' x.
Proof.
    intros [L U c] q. repeat split; unfold L_neg, U_neg. 
    - intros (r & (r' & H1 & H2) & H3).
      destruct c as (_ & _ & _ & _ & _ & _ & H4 & _).
      apply (H4 (-r) q). qauto.
      apply (H4 r' (-r)). qauto.
    - intros; exists (- q); qauto; exists q; qauto.
    - intros (r & (r' & H1 & H2) & H3).
      destruct c as (_ & _ & _ & _ & _ & _ & _ & H4).
      apply (H4 (-r) q). qauto.
      apply (H4 r' (-r)). qauto.
    - intros; exists (- q); qauto; exists q; qauto.
Qed.

Lemma add_inverse :
  forall x : my_R, (x +' -' x) =' R0.
Proof.
    intros [L U c] q. unfold L_add, U_add, L_neg, U_neg, L_Q, U_Q; repeat split.
    - intros (x & y & H1 & (r & H2 & H3) & H4).
      admit.
    - admit.
    - admit.
    - admit.
Admitted.


(* 
 * ================================================================
 * Show that (R, 0, +, -) is an abelian group
 * ================================================================ 
 *)

Lemma associative :
    forall x y z : my_R,
    add (add x y) z =' (add x (add y z)).
Proof.
    intros [L1 U1 c1] [L2 U2 c2] [L3 U3 c3] q. 
    unfold L_add, U_add; repeat split.
    - intros (x & y & (x' & y' & H1 & H2 & H3) & H4 & H5).
      exists x', (y' + y). 
      repeat split; [|exists y', y|]; qauto.
    - intros (x & y & H4 & (x' & y' & H1 & H2 & H3) & H5).
      exists (x + x'), y'.
      repeat split; [exists x, x'|..]; qauto.
    - intros (x & y & (x' & y' & H1 & H2 & H3) & H4 & H5).
      exists x', (y' + y). 
      repeat split; [|exists y', y|]; qauto.
    - intros (x & y & H4 & (x' & y' & H1 & H2 & H3) & H5).
      exists (x + x'), y'.
      repeat split; [exists x, x'|..]; qauto.
Qed.

Lemma commutative :
    forall x y : my_R,
    (add x y) =' (add y x).
Proof.
    intros [L1 U1 c1] [L2 U2 c2] q.
    unfold L_add, U_add, L_Q, U_Q; repeat split;
    intros (x & y & H1 & H2 & H3);
    exists y, x; qauto.
Qed.

Lemma identity_left :
    forall x : my_R,
    add R0 x =' x.
Proof.
    intros [L U c] q. 
    unfold L_add, U_add, L_Q, U_Q; repeat split.
    - intros (x & y & H1 & H2 & H3).
      destruct c as (_ & _ & H4 & _).
      apply H4. exists y. qauto.
    - intros H1.
      destruct c as (_ & _ & H4 & _).
      destruct (H4 q) as ((r & H5 & H6) & _); [eauto|].
      exists (q - r), r. qauto.
    - intros (x & y & H1 & H2 & H3).
      destruct c as (_ & _ & _ & H4 & _).
      apply H4. exists y. qauto.
    - intros H1.
      destruct c as (_ & _ & _ & H4 & _).
      destruct (H4 q) as ((r & H5 & H6) & _); [eauto|].
      exists (q - r), r. qauto.
Qed.

Lemma identity_right :
    forall x : my_R,
    add x R0 =' x.
Proof.
    intros x.
    eapply equiv_transitive.
    - apply commutative.
    - apply identity_left.
Qed.

Lemma inverse_left :
    forall x : my_R,
    (x +' -'x) =' R0.
Proof.
    apply add_inverse.
Qed.

Lemma inverse_right :
    forall x : my_R,
    (-'x +' x) =' R0.
Proof.
    intros x.
    eapply equiv_transitive.
    - apply commutative.
    - apply inverse_left.
Qed.
