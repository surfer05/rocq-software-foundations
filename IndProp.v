Set Warnings "-notation-overridden".
From LF Require Export Logic.
From LF Require Export Basics.
From LF Require Export Lists.
From LF Require Export Poly.


(* inductively defined propositions *)
(* you define a proposition by giving rules for proving it, and Coq treats those rules as constructors that build proof terms. *)

(* EXAMPLE : THE COLLATZ CONJECTURE *)
(* csf -> Collatz step functions *)
Fixpoint div2 (n : nat) : nat :=
  match n with 
  | 0 => 0
  | 1 => 0
  | S ( S n) => S ( div2 n)
  end.

Definition csf (n : nat) : nat :=
  if even n then div2 n
  else (3 * n) + 1.

Fail Fixpoint reaches1_in (n : nat) : nat :=
  if n=? 1 then 0
  else 1 + reaches1_in (csf n).

Fail Fixpoint Collatz_holds_for (n : nat) : Prop :=
  match n with
  | 0 => False
  | 1 => True
  | _ => if even n then Collatz_holds_for (div2 n)
                   else Collatz_holds_for ((3 * n) + 1)
  end.

Inductive Collatz_holds_for : nat -> Prop := 
  | Chf_one : Collatz_holds_for 1
  | Chf_even (n : nat) : even n = true -> 
                         Collatz_holds_for (div2 n) ->
                         Collatz_holds_for n 
  | Chf_odd (n : nat) : even n = false -> 
                        Collatz_holds_for ((3*n + 1)) ->
                        Collatz_holds_for n.

Example Collatz_holds_for_12 : Collatz_holds_for 12.
Proof.
  apply Chf_even. reflexivity. simpl.
  apply Chf_even. reflexivity. simpl.
  apply Chf_odd. reflexivity. simpl.
  apply Chf_even. reflexivity. simpl.
  apply Chf_odd. reflexivity. simpl.
  apply Chf_even. reflexivity. simpl.
  apply Chf_even. reflexivity. simpl.
  apply Chf_even. reflexivity. simpl.
  apply Chf_even. reflexivity. simpl.
  apply Chf_one.
Qed.

Conjecture collatz : forall n, n <> 0 -> Collatz_holds_for n.


(* EXAMPLE : BINARY RELATION FOR COMPARING NUMBERS *)

Inductive le : nat -> nat -> Prop :=
  | le_n (n : nat) : le n n
  | le_S (n m : nat) : le n m -> le n ( S m).

Notation "n <= m" := (le n m) (at level 70).
Example le_3_5 : 3 <= 5.
Proof.
  apply le_S. apply le_S. apply le_n. 
Qed.

(* EXAMPLE : TRANSITIVE CLOSURE *)

Inductive clos_trans { X : Type} (R : X -> X -> Prop) : X -> X -> Prop :=
  | t_step ( x y : X) :
      R x y ->
      clos_trans R x y
  | t_trans ( x y z : X) :
      clos_trans R x y ->
      clos_trans R y z ->
      clos_trans R x z.

Inductive Person : Type := Sage | Cleo | Ridley | Moss.

Inductive parent_of : Person -> Person -> Prop :=
  | po_SC : parent_of Sage Cleo
  | po_SR : parent_of Sage Ridley
  | po_CM : parent_of Cleo Moss.

Definition ancestor_of : Person -> Person -> Prop :=
  clos_trans parent_of.

Example ancestor_of_ex : ancestor_of Sage Moss.
Proof.
  unfold ancestor_of. apply t_trans with Cleo.
  - apply t_step. apply po_SC.
  - apply t_step. apply po_CM.
Qed.

(* EXAMPLE : REFLEXIVE AND TRANSITIVE CLOSURE *)

Inductive clos_refl_trans { X : Type} (R : X -> X -> Prop) : X -> X -> Prop :=
  | rt_step (x y : X) : 
      R x y -> 
      clos_refl_trans R x y
  | rt_refl ( x : X) :
      clos_refl_trans R x x 
  | rt_trans ( x y z : X ) :
      clos_refl_trans R x y ->
      clos_refl_trans R y z ->
      clos_refl_trans R x z.

Definition cs ( n m : nat) : Prop := csf n = m.
Check cs.
Definition cms n m := clos_refl_trans cs n m.
Check cms.


(* Exercise : clos_refl_trans_sym *)

Inductive clos_refl_trans_sym { X : Type} (R : X -> X -> Prop) : X -> X -> Prop :=
  | rts_step (x y : X) : 
      R x y -> 
      clos_refl_trans_sym R x y
  | rts_refl ( x : X) :
      clos_refl_trans_sym R x x 
  | rts_sym ( x y : X) :
      clos_refl_trans_sym R x y ->
      clos_refl_trans_sym R y x
  | rts_trans ( x y z : X ) :
      clos_refl_trans_sym R x y ->
      clos_refl_trans_sym R y z ->
      clos_refl_trans_sym R x z.
  
(* had to import these notations, no idea why [a;b;c] was showing error *)
Notation "x :: l" := (cons x l)
      (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..). 

(* EXAMPLE : PERMUTATIONS *)

Inductive Perm3 {X : Type} : list X -> list X -> Prop :=
  | perm3_swap12 (a b c : X) :
      Perm3 [a;b;c] [b;a;c]
  | perm3_swap23 (a b c : X) :
      Perm3 [a;b;c] [a;c;b]
  | perm3_trans (l1 l2 l3 : list X) :
      Perm3 l1 l2 -> Perm3 l2 l3 -> Perm3 l1 l3.


(* EXAMPLE : EVENNESS ( YET AGAIN ) *)

Inductive ev : nat -> Prop :=
  | ev_0 : ev 0
  | ev_SS (n : nat ) ( H : ev n) : ev ( S ( S n)).

Check ev.
Check ev_0.
Check (ev 5).
Check ev_SS.

Fail Inductive wrong_ev (n : nat) : Prop :=
  | wrong_ev_0 : wrong_ev 0
  | wrong_ev_SS (H: wrong_ev n) : wrong_ev (S (S n)).

Module EvPlayground.

  Inductive ev : nat -> Prop :=
    | ev_0 : ev 0
    | ev_SS : forall (n : nat), ev n -> ev (S (S n)).

End EvPlayground.

Theorem ev_4 : ev 4.
Proof.
  apply ev_SS. apply ev_SS. apply ev_0. 
Qed.

Theorem ev_4' : ev 4.
Proof.
  apply (ev_SS 2 ( ev_SS 0 ev_0)).
Qed.

Theorem ev_plus4 : forall n, ev n -> ev ( 4 + n).
Proof.
  intros n.
  simpl. 
  intros H.
  apply ev_SS.
  apply ev_SS.
  apply H.
Qed.

Theorem ev_double : forall n,
  ev ( double n).
Proof.
  intros.
  induction n as [ | n' IHn'].
  - simpl. apply ev_0.
  - simpl. apply ev_SS. apply IHn'.
Qed.

(* Constructing Evidence for Permutations *)

Lemma Perm3_rev : Perm3 [1;2;3] [3;2;1].
Proof.
  apply perm3_trans with (l2 := [2;3;1]).
  - apply perm3_trans with (l2 := [2;1;3]).
    + apply perm3_swap12.
    + apply perm3_swap23.
  - apply perm3_swap12.
Qed.

Lemma Perm3_rev' : Perm3 [1;2;3] [3;2;1].
Proof.
  apply (perm3_trans _ [2;3;1] _
          (perm3_trans _ [2;1;3] _
            (perm3_swap12 _ _ _)
            (perm3_swap23 _ _ _))
          (perm3_swap12 _ _ _)).
Qed.

Lemma Perm3_ex1 : Perm3 [1;2;3] [2;3;1].
Proof.
  apply perm3_trans with (l2 := [2;1;3]).
  - apply perm3_swap12.
  - apply perm3_swap23.
Qed.

Lemma Perm3_refl : forall (X : Type ) (a b c : X ), 
  Perm3 [a;b;c] [a;b;c].
Proof.
  intros. 
  apply perm3_trans with (l2 := [b;a;c]).
  - apply perm3_swap12.
  - apply perm3_swap12.
Qed.

(* ################################################################# *)
(* USING EVIDENCE IN PROOFS *)

Theorem ev_inversion : forall (n : nat),
    ev n ->
    (n = 0) \/ (exists n', n = S (S n') /\ ev n').
Proof.
  intros n E.  destruct E as [ | n' E'] eqn:EE.
  - (* E = ev_0 : ev 0 *)
    left. reflexivity.
  - (* E = ev_SS n' E' : ev (S (S n')) *)
    right. exists n'. split. reflexivity. apply E'.
Qed.

(* Theorem le_inversion : forall (n m : nat),
  le n m ->
  (n = m) \/ (exists m', m = S m' /\ le n m').
Proof.
  intros n m E.
  destruct E as [| m' E'] eqn:EE.
  - left. reflexivity.
  - right. exists m'. split.
     reflexivity. apply E'.
Qed. *)

Theorem evSS_ev : forall n, ev (S (S n)) -> ev n.
Proof.
  intros n E. apply ev_inversion in E. destruct E as [H0|H1].
  - discriminate H0.
  - destruct H1 as [n' [Hnn' E']]. injection Hnn' as Hnn'.
    rewrite Hnn'. apply E'.
Qed.

Theorem evSS_ev' : forall n,
  ev (S (S n)) -> ev n.
Proof.
  intros n E.  inversion E as [| n' E' Hnn'].
  (* We are in the [E = ev_SS n' E'] case now. *)
  apply E'.
Qed.

Theorem one_not_even : ~ ev 1.
Proof.
  intros H. apply ev_inversion in H.  destruct H as [ | [m [Hm _]]].
  - discriminate H.
  - discriminate Hm.
Qed.

Theorem one_not_even' : ~ ev 1.
Proof. intros H. inversion H. Qed.

Theorem SSSSev__even : forall n,
  ev (S (S (S (S n)))) -> ev n.
Proof.
  intros n H. inversion H as [| n0 H0 Heq0]. inversion H0 as [| n1 H1 Heq1].
  apply H1.
Qed.

Theorem ev5_nonsense :
  ev 5 -> 2 + 2 = 9.
Proof.
  intros H.
  inversion H as [| n0 H0 Heq0].
  inversion H0 as [| n1 H1 Heq1].
  inversion H1.
Qed.

Theorem inversion_ex1 : forall (n m o : nat),
  [n; m] = [o; o] -> [n] = [m].
Proof.
  intros n m o H. inversion H. reflexivity. Qed.

Theorem inversion_ex2 : forall (n : nat),
  S n = O -> 2 + 2 = 5.
Proof.
  intros n contra. inversion contra. Qed.

Lemma ev_Even_firsttry : forall n,
  ev n -> Even n.
Proof.
  unfold Even.
  intros n E. inversion E as [EQ' | n' E' EQ'].
  - (* E = ev_0 *) exists 0. reflexivity.
  - assert (H: (exists k', n' = double k')
               -> (exists n0, S (S n') = double n0)).
        { intros [k' EQ'']. exists (S k'). simpl.
          rewrite <- EQ''. reflexivity. }
    apply H.
    generalize dependent E'.
Abort.

(* ================================================================= *)
(* INDUCTION ON EVIDENCE *)

Lemma ev_Even : forall n,
  ev n -> Even n.
Proof.
  unfold Even. intros n E.
  induction E as [|n' E' IH].
  - (* E = ev_0 *)
    exists 0. reflexivity.
  - (* E = ev_SS n' E',  with IH : Even n' *)
    destruct IH as [k Hk]. rewrite Hk.
    exists (S k). simpl. reflexivity.
Qed.

Theorem ev_Even_iff : forall n,
  ev n <-> Even n.
Proof.
  intros n. split.
  - (* -> *) apply ev_Even.
  - (* <- *) unfold Even. intros [k Hk]. rewrite Hk. apply ev_double.
Qed.

Theorem ev_sum : forall n m, ev n -> ev m -> ev (n + m).
Proof.
  intros n m En Em.
  induction En.
  - apply Em.
  - simpl. apply ev_SS. apply IHEn.
Qed.
(** [] *)

Theorem ev_ev__ev : forall n m,
  ev (n+m) -> ev n -> ev m.

Proof.
  intros n m.
  intros E1 E2.
  induction E2.
  - apply E1.
  - simpl in E1. inversion E1 as [| sum E3 H]. apply (IHE2 E3).
Qed.

Theorem ev_plus_plus : forall n m p,
  ev (n+m) -> ev (n+p) -> ev (m+p).
Proof.
  intros n m p Enm Enp.
  apply ev_ev__ev with (n + n).
  - assert (ev ((n + m) + (n + p))) as H.
    { apply ev_sum. apply Enm. apply Enp. }
    rewrite add_comm with n m in H.
    rewrite <- add_assoc with m n (n + p) in H.
    rewrite add_assoc with n n p in H.
    rewrite add_comm with (n + n) p in H.
    rewrite add_assoc with m p (n + n) in H.
    rewrite add_comm with (m + p) (n + n) in H.
    apply H.
  - rewrite <- double_plus. apply ev_double.
Qed.


(* ------------ MULTIPLE INDUCTION HYPOTHESES ------------- *)

Inductive ev' : nat -> Prop :=
  | ev'_0 : ev' 0
  | ev'_2 : ev' 2
  | ev'_sum n m (Hn : ev' n) (Hm : ev' m) : ev' (n + m).

Theorem ev'_ev : forall n, ev' n <-> ev n.
Proof.
  intros n.
  split.
  - intros H. induction H.
    + apply ev_0.
    + apply ev_SS. apply ev_0.
    + apply ev_sum. apply IHev'1. apply IHev'2.
  - intros H. induction H.
    + apply ev'_0.
    + rewrite <- plus_1_l with (S n). rewrite <- plus_n_Sm. rewrite <- plus_1_l.
      rewrite add_assoc. apply ev'_sum.
      * apply ev'_2.
      * apply IHev.
Qed.

Module Perm3Reminder.

Inductive Perm3 {X : Type} : list X -> list X -> Prop :=
  | perm3_swap12 (a b c : X) :
      Perm3 [a;b;c] [b;a;c]
  | perm3_swap23 (a b c : X) :
      Perm3 [a;b;c] [a;c;b]
  | perm3_trans (l1 l2 l3 : list X) :
      Perm3 l1 l2 -> Perm3 l2 l3 -> Perm3 l1 l3.

End Perm3Reminder.

Lemma Perm3_symm : forall (X : Type) (l1 l2 : list X),
  Perm3 l1 l2 -> Perm3 l2 l1.
Proof.
  intros X l1 l2 E.
  induction E as [a b c | a b c | l1 l2 l3 E12 IH12 E23 IH23].
  - apply perm3_swap12.
  - apply perm3_swap23.
  - apply (perm3_trans _ l2 _).
    * apply IH23.
    * apply IH12.
Qed.

Lemma Perm3_In : forall (X : Type) (x : X) (l1 l2 : list X),
    Perm3 l1 l2 -> In x l1 -> In x l2.
Proof.
  intros X x l1 l2 HPerm HIn.
  induction HPerm.
  - simpl.
    destruct HIn as [E|HIn'].
    + right. left. apply E.
    + inversion HIn' as [E|HIn''].
      * left. apply E.
      * inversion HIn'' as [E|contra].
        ** right. right. left. apply E.
        ** destruct contra.
  - simpl.
    destruct HIn as [E|HIn'].
    + left. apply E.
    + inversion HIn' as [E|HIn''].
      * right. right. left. apply E.
      * inversion HIn'' as [E|contra].
        ** right. left. apply E.
        ** destruct contra.
  - simpl.
    apply IHHPerm2. apply IHHPerm1. apply HIn.
Qed.

Lemma Perm3_NotIn : forall (X : Type) (x : X) (l1 l2 : list X),
    Perm3 l1 l2 -> ~In x l1 -> ~In x l2.
Proof.
  intros X x l1 l2 HPerm HNotIn contra.
  apply HNotIn.
  apply Perm3_In with (l1:=l2).
  - apply Perm3_symm. apply HPerm.
  - apply contra.
Qed.

Example Perm3_example2 : ~ Perm3 [1;2;3] [1;2;4].
Proof.
  intros contra.
  assert (H: In 3 [1;2;4]).
  { apply Perm3_In with (l1:=[1;2;3]). apply contra. simpl. right. right. left. reflexivity. }
  destruct H as [|H1]. discriminate.
  destruct H1 as [|H2]. discriminate.
  destruct H2 as [|H3]. discriminate.
  destruct H3.
Qed.


(* ################################################################# *)
(* -------------- EXERCISING WITH INDUCTIVE RELATIONS -------------------- *)

    Module Playground.

      Inductive le : nat -> nat -> Prop :=
        | le_n (n : nat)                : le n n
        | le_S (n m : nat) (H : le n m) : le n (S m).
      
      Notation "n <= m" := (le n m).

      Theorem test_le1 :
        3 <= 3.
      Proof.
        (* WORKED IN CLASS *)
        apply le_n.  Qed.
      
      Theorem test_le2 :
        3 <= 6.
      Proof.
        (* WORKED IN CLASS *)
        apply le_S. apply le_S. apply le_S. apply le_n.  Qed.
      
      Theorem test_le3 :
        (2 <= 1) -> 2 + 2 = 5.
      Proof.
        (* WORKED IN CLASS *)
        intros H. inversion H. inversion H2.  Qed.
      
      (** The "strictly less than" relation [n < m] can now be defined
          in terms of [le]. *)
      
      Definition lt (n m : nat) := le (S n) m.
      
      Notation "n < m" := (lt n m).
      
      (** The [>=] operation is defined in terms of [<=]. *)
      
      Definition ge (m n : nat) : Prop := le n m.
      Notation "m >= n" := (ge m n).
      
      End Playground.

      (** **** Exercise: 3 stars, standard, especially useful (le_facts) *)
      Lemma le_trans : forall m n o, m <= n -> n <= o -> m <= o.
      Proof.
        intros m n o Emn Eno.
        induction Eno as [|o Eno IH].
        - apply Emn.
        - apply (le_S m o IH).
      Qed.
      
      Theorem O_le_n : forall n,
        0 <= n.
      Proof.
        intros n.
        induction n.
        - apply le_n.
        - apply (le_S 0 n IHn).
      Qed.
      
      Theorem n_le_m__Sn_le_Sm : forall n m,
        n <= m -> S n <= S m.
      Proof.
        intros n m H.
        induction H as [|m H IH].
        - apply le_n.
        - apply (le_S (S n) (S m) IH).
      Qed.
      
      Theorem Sn_le_Sm__n_le_m : forall n m,
        S n <= S m -> n <= m.
      Proof.
        intros n m H.
        induction m.
        - inversion H as [H0 | zero H1 H2]. apply le_n. inversion H1.
        - inversion H as [H0 | Sm H1 H2]. apply le_n. apply (le_S n m (IHm H1)).
      Qed.
      
      Theorem le_plus_l : forall a b,
        a <= a + b.
      Proof.
        intros a b.
        induction b.
        - rewrite add_0_r. apply le_n.
        - rewrite <- plus_n_Sm. apply (le_S a (a + b) IHb).
      Qed.
      (** [] *)
      
      (** **** Exercise: 2 stars, standard, especially useful (plus_le_facts1) *)
      
      Theorem plus_le : forall n1 n2 m,
        n1 + n2 <= m ->
        n1 <= m /\ n2 <= m.
      Proof.
        intros n1 n2 m H.
        induction H.
        - split.
          + apply le_plus_l.
          + rewrite add_comm. apply le_plus_l.
        - destruct IHle as [H1 H2].
          split.
          + apply (le_S n1 m H1).
          + apply (le_S n2 m H2).
      Qed.
      
      Theorem plus_le_cases : forall n m p q,
        n + m <= p + q -> n <= p \/ m <= q.
        (** Hint: May be easiest to prove by induction on [n]. *)
      Proof.
        induction n.
        - left. apply O_le_n.
        - intros. destruct p.
          + right. apply plus_le in H.
            destruct H as [H1 H2].
            rewrite plus_O_n in H1.
            apply H2.
          + simpl in H.
            rewrite plus_n_Sm with n m in H.
            rewrite plus_n_Sm with p q in H.
            apply IHn in H. destruct H.
            * left. apply n_le_m__Sn_le_Sm. apply H.
            * right. apply Sn_le_Sm__n_le_m. apply H.
      Qed.
      (** [] *)
      
      (** **** Exercise: 2 stars, standard, especially useful (plus_le_facts2) *)
      
      Theorem plus_le_compat_l : forall n m p,
        n <= m ->
        p + n <= p + m.
      Proof.
        intros n m p.
        induction p.
        - intros. rewrite plus_O_n. rewrite plus_O_n. apply H.
        - intros. simpl. apply n_le_m__Sn_le_Sm. apply (IHp H).
      Qed.
      
      Theorem plus_le_compat_r : forall n m p,
        n <= m ->
        n + p <= m + p.
      Proof.
        intros n m p H.
        rewrite add_comm with n p.
        rewrite add_comm with m p.
        apply plus_le_compat_l.
        apply H.
      Qed.
      
      Theorem le_plus_trans : forall n m p,
        n <= m ->
        n <= m + p.
      Proof.
        intros n m p.
        generalize dependent n.
        generalize dependent m.
        induction p.
        - intros. rewrite add_comm. rewrite plus_O_n. apply H.
        - intros. destruct H.
          + apply le_plus_l.
          + simpl.
            apply IHp in H.
            apply le_S in H. rewrite plus_n_Sm in H.
            apply (le_S n (m + S p) H).
      Qed.
      (** [] *)
      
      (** **** Exercise: 3 stars, standard, optional (lt_facts) *)
      Theorem lt_ge_cases : forall n m,
        n < m \/ n >= m.
      Proof.
        intros n m.
        destruct m.
        - right. apply O_le_n.
        - induction n.
          + left. apply n_le_m__Sn_le_Sm. apply O_le_n.
          + destruct IHn.
            * destruct H.
              right. apply le_n.
              left. apply n_le_m__Sn_le_Sm. apply H.
            * right. apply le_S. apply H.
      Qed.
      
      Theorem n_lt_m__n_le_m : forall n m,
        n < m ->
        n <= m.
      Proof.
        intros n m H.
        apply le_S in H.
        apply Sn_le_Sm__n_le_m in H.
        apply H.
      Qed.
      
      Theorem plus_lt : forall n1 n2 m,
        n1 + n2 < m ->
        n1 < m /\ n2 < m.
      Proof.
        intros n1 n2 m H.
        inversion H as [H12 | n H12 Hm].
        - split.
          + apply n_le_m__Sn_le_Sm. apply le_plus_l.
          + apply n_le_m__Sn_le_Sm. rewrite add_comm. apply le_plus_l.
        - rewrite <- Hm in H. apply Sn_le_Sm__n_le_m in H.
          apply plus_le in H. destruct H as [H1 H2].
          split.
          + apply n_le_m__Sn_le_Sm. apply H1.
          + apply n_le_m__Sn_le_Sm. apply H2.
      Qed.
      (** [] *)
      
      (** **** Exercise: 4 stars, standard, optional (leb_le) *)
      Theorem leb_complete : forall n m,
        n <=? m = true -> n <= m.
      Proof.
        intros n m.
        generalize dependent m.
        induction n.
        - intros. apply O_le_n.
        - intros. destruct m.
          + discriminate.
          + simpl in H. apply IHn in H. apply n_le_m__Sn_le_Sm. apply H.
      Qed.
      
      Theorem leb_correct : forall n m,
        n <= m ->
        n <=? m = true.
      Proof.
        intros n m.
        generalize dependent n.
        induction m.
        - intros. inversion H. reflexivity.
        - destruct n.
          + reflexivity.
          + intros. apply Sn_le_Sm__n_le_m in H. apply (IHm n H).
      Qed.
      
      (** Hint: The next two can easily be proved without using [induction]. *)
      
      Theorem leb_iff : forall n m,
        n <=? m = true <-> n <= m.
      Proof.
        intros n m.
        split.
        - apply leb_complete.
        - apply leb_correct.
      Qed.
      
      Theorem leb_true_trans : forall n m o,
        n <=? m = true -> m <=? o = true -> n <=? o = true.
      Proof.
        intros n m o Hnm Hmo.
        apply leb_complete in Hnm.
        apply leb_complete in Hmo.
        apply leb_correct.
        apply le_trans with m.
        apply Hnm. apply Hmo.
      Qed.
      (** [] *)
      
      Module R.
      
      (** **** Exercise: 3 stars, standard, especially useful (R_provability)
      
          We can define three-place relations, four-place relations,
          etc., in just the same way as binary relations.  For example,
          consider the following three-place relation on numbers: *)
      
      Inductive R : nat -> nat -> nat -> Prop :=
        | c1                                     : R 0     0     0
        | c2 m n o (H : R m     n     o        ) : R (S m) n     (S o)
        | c3 m n o (H : R m     n     o        ) : R m     (S n) (S o)
        | c4 m n o (H : R (S m) (S n) (S (S o))) : R m     n     o
        | c5 m n o (H : R m     n     o        ) : R n     m     o
      .
      
      (** - Which of the following propositions are provable?
            - [R 1 1 2]
            - [R 2 2 6]
      
          - If we dropped constructor [c5] from the definition of [R],
            would the set of provable propositions change?  Briefly (1
            sentence) explain your answer.
      
          - If we dropped constructor [c4] from the definition of [R],
            would the set of provable propositions change?  Briefly (1
            sentence) explain your answer. *)
      
      (* FILL IN HERE *)
      
      (* Do not modify the following line: *)
      Definition manual_grade_for_R_provability : option (nat*string) := None.
      (** [] *)
      
      (** **** Exercise: 3 stars, standard, optional (R_fact)
      
          The relation [R] above actually encodes a familiar function.
          Figure out which function; then state and prove this equivalence
          in Coq. *)
      
      Definition fR : nat -> nat -> nat
        := plus.
      
      Theorem R_equiv_fR : forall m n o, R m n o <-> fR m n = o.
      Proof.
        split.
        - intros. induction H.
          + reflexivity.
          + simpl. f_equal. apply IHR.
          + rewrite <- plus_n_Sm. f_equal. apply IHR.
          + simpl in IHR.
            apply S_injective in IHR. rewrite <- plus_n_Sm in IHR.
            apply S_injective in IHR.
            apply IHR.
          + rewrite add_comm in IHR. apply IHR.
        - intros.
          rewrite <- H.
          destruct H.
          induction m.
            + induction n. apply c1. apply c3. apply IHn.
            + simpl. apply c2. apply IHm.
      Qed.
      (** [] *)
      
      End R.
      
      (** **** Exercise: 4 stars, advanced (subsequence)
      
          A list is a _subsequence_ of another list if all of the elements
          in the first list occur in the same order in the second list,
          possibly with some extra elements in between. For example,
      
            [1;2;3]
      
          is a subsequence of each of the lists
      
            [1;2;3]
            [1;1;1;2;2;3]
            [1;2;7;3]
            [5;6;1;9;9;2;7;3;8]
      
          but it is _not_ a subsequence of any of the lists
      
            [1;2]
            [1;3]
            [5;6;2;1;7;3;8].
      
          - Define an inductive proposition [subseq] on [list nat] that
            captures what it means to be a subsequence. (Hint: You'll need
            three cases.)
      
          - Prove [subseq_refl] that subsequence is reflexive, that is,
            any list is a subsequence of itself.
      
          - Prove [subseq_app] that for any lists [l1], [l2], and [l3],
            if [l1] is a subsequence of [l2], then [l1] is also a subsequence
            of [l2 ++ l3].
      
          - (Harder) Prove [subseq_trans] that subsequence is
            transitive -- that is, if [l1] is a subsequence of [l2] and [l2]
            is a subsequence of [l3], then [l1] is a subsequence of [l3]. *)
      
      Inductive subseq : list nat -> list nat -> Prop :=
        | subseq0 l : subseq [] l
        | subseq1 x l1 l2 (H : subseq l1 l2) : subseq (x :: l1) (x :: l2)
        | subseq2 x l1 l2 (H : subseq l1 l2) : subseq l1 (x :: l2)
      .
      
      Theorem subseq_refl : forall (l : list nat), subseq l l.
      Proof.
        induction l as [| x l IH].
        - apply subseq0.
        - apply (subseq1 x l l IH).
      Qed.
      
      Theorem subseq_app : forall (l1 l2 l3 : list nat),
        subseq l1 l2 ->
        subseq l1 (l2 ++ l3).
      Proof.
        intros.
        induction H as [| x l1 l2 H IH | x l1 l2 H IH].
        - apply subseq0.
        - simpl. apply (subseq1 x l1 (l2 ++ l3) IH).
        - simpl. apply (subseq2 x l1 (l2 ++ l3) IH).
      Qed.
      
      Theorem subseq_trans : forall (l1 l2 l3 : list nat),
        subseq l1 l2 ->
        subseq l2 l3 ->
        subseq l1 l3.
      Proof.
        (* Hint: be careful about what you are doing induction on and which
           other things need to be generalized... *)
        intros l1 l2 l3 H12 H23.
        generalize dependent l1.
        induction H23 as [| x l2 l3 H23 IH | x l2 l3 H23 IH].
        - intros.
          assert (l1 = []) as Hl1. inversion H12. reflexivity.
          rewrite Hl1. apply subseq0.
        - intros. inversion H12 as [| x' l1' l2' H12' | x' l1' l2' H12'].
          + apply subseq0.
          + apply (subseq1 x l1' l3 (IH l1' H12')).
          + apply (subseq2 x l1 l3 (IH l1 H12')).
        - intros. apply (subseq2 x l1 l3 (IH l1 H12)).
      Qed.
      (** [] *)
      
      (** **** Exercise: 2 stars, standard, optional (R_provability2)
      
          Suppose we give Coq the following definition:
      
          Inductive R : nat -> list nat -> Prop :=
            | c1                    : R 0     []
            | c2 n l (H: R n     l) : R (S n) (n :: l)
            | c3 n l (H: R (S n) l) : R n     l.
      
          Which of the following propositions are provable?
      
          - [R 2 [1;0]]
          - [R 1 [1;2;1;0]]
          - [R 6 [3;2;1;0]]  *)
      
      (* FILL IN HERE
      
          [] *)

(* CASE STUDY : REGULAR EXPRESSIONS *)

Inductive reg_exp (T : Type) : Type :=
  | EmptySet
  | EmptyStr
  | Char (t : T)
  | App (r1 r2 : reg_exp T)
  | Union (r1 r2 : reg_exp T)
  | Star (r : reg_exp T).

Arguments EmptySet {T}.
Arguments EmptyStr {T}.
Arguments Char {T} _.
Arguments App {T} _ _.
Arguments Union {T} _ _.
Arguments Star {T} _.

Reserved Notation "s =~ re" (at level 80).

Inductive exp_match {T} : list T -> reg_exp T -> Prop :=
  | MEmpty : [] =~ EmptyStr
  | MChar x : [x] =~ (Char x)
  | MApp s1 re1 s2 re2
             (H1 : s1 =~ re1)
             (H2 : s2 =~ re2)
           : (s1 ++ s2) =~ (App re1 re2)
  | MUnionL s1 re1 re2
                (H1 : s1 =~ re1)
              : s1 =~ (Union re1 re2)
  | MUnionR s2 re1 re2
                (H2 : s2 =~ re2)
              : s2 =~ (Union re1 re2)
  | MStar0 re : [] =~ (Star re)
  | MStarApp s1 s2 re
                 (H1 : s1 =~ re)
                 (H2 : s2 =~ (Star re))
               : (s1 ++ s2) =~ (Star re)

  where "s =~ re" := (exp_match s re).

Example reg_exp_ex1 : [1] =~ Char 1.
Proof.
  apply MChar.
Qed.

Check MApp [1;2].

Example reg_exp_ex2 : [1;2] =~ App (Char 1) (Char 2).
Proof.
  apply (MApp [1]).
  - apply MChar.
  - apply MChar.
Qed.

Example reg_exp_ex3 : ~([1;2] =~ Char 1).
Proof.
  intros H. inversion H.
Qed.

Fixpoint reg_exp_of_list {T} (l : list T) :=
  match l with 
    | [] => EmptyStr
    | x :: l' => App (Char x) (reg_exp_of_list l')
  end.

Example reg_exp_ex4 : [1;2;3] =~ reg_exp_of_list [1;2;3].
Proof.
  simpl. apply (MApp [1]).
  { apply MChar. }
  apply (MApp [2]). 
  { apply MChar. }
  apply (MApp [3]).
  { apply MChar. }
  apply MEmpty.
Qed.


Lemma MStar1 :
  forall T s (re : reg_exp T) ,
    s =~ re ->
    s =~ Star re.
Proof.
  intros T s re H.
  rewrite <- (app_nil_r _ s).
  apply MStarApp.
  - apply H.
  - apply MStar0.
Qed.

Lemma EmptySet_is_empty : forall T ( s : list T),
  ~(s =~ EmptySet).
Proof.
  intros T s.
  unfold not. intros. inversion H.
Qed.

Lemma MUnion' : forall T (s : list T) (re1 re2 : reg_exp T),
  s =~ re1 \/ s =~ re2 ->
  s =~ Union re1 re2.
Proof.
  intros.
  destruct H.
  - apply MUnionL. apply H.
  - apply MUnionR. apply H.
Qed.
  
Lemma MStar' : forall T (ss : list (list T)) (re : reg_exp T),
  (forall s, In s ss -> s =~ re) ->
  fold app ss [] =~ Star re.
Proof.
  intros.
  induction ss as [ | s1 ss IHss'].
  - simpl. apply MStar0.
  - simpl. apply MStarApp.
    + apply H. left. reflexivity.
    + apply IHss'. intros. apply H. right. apply H0.
Qed.

Definition EmptyStr' {T:Type} := @Star T (EmptySet).

Theorem EmptyStr_not_needed : forall T (s : list T),
  s =~ EmptyStr <-> s =~ EmptyStr'.
Proof.
  intros. split.
  - intros.
    destruct s.
    + apply MStar0.
    + inversion H.
  - intros.
    destruct s.
    + apply MEmpty.
    + inversion H. inversion H2.
Qed.

Fixpoint re_chars {T} (re : reg_exp T) : list T :=
  match re with 
  | EmptySet => []
  | EmptyStr => []
  | Char x => [x]
  | App re1 re2 => re_chars re1 ++ re_chars re2
  | Union re1 re2 => re_chars re1 ++ re_chars re2
  | Star re => re_chars re
  end.

Theorem in_re_match : forall T (s : list T) (re : reg_exp T) (x : T),
  s =~ re -> 
  In x s -> 
  In x (re_chars re).
Proof.
  intros T s re x HMatch Hin.
  induction HMatch
    as [ | x'
         | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
         | s1 re1 re2 Hmatch IH | s2 re1 re2 Hmatch IH 
         | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2]. 
  - simpl in Hin. destruct Hin.
  - simpl. simpl in Hin. apply Hin.
  - simpl.
    rewrite In_app_iff in Hin.
    destruct Hin as [ Hin | Hin].
    + rewrite In_app_iff. left. apply (IH1 Hin).
    + rewrite In_app_iff. right. apply (IH2 Hin).
  - simpl. rewrite In_app_iff. left. apply (IH Hin).
  - simpl. rewrite In_app_iff. right. apply (IH Hin).
  - simpl. destruct Hin.
  - simpl. rewrite In_app_iff in Hin. 
    destruct Hin as [Hin | Hin].
    + apply (IH1 Hin).
    + apply (IH2 Hin).  
Qed.


Fixpoint re_not_empty {T : Type} (re : reg_exp T) : bool :=
  match re with 
  | EmptySet => false
  | EmptyStr => true 
  | Char _ => true
  | App re1 re2 => (re_not_empty re1) && (re_not_empty re2)
  | Union re1 re2 => (re_not_empty re1) || (re_not_empty re2)
  | Star _ => true
  end.

  Theorem andb_true_iff : forall b1 b2:bool,
  b1 && b2 = true <-> b1 = true /\ b2 = true.
Proof.
  intros b1 b2.
  split.
  + intros H. destruct b1.
    - destruct b2.
      split. reflexivity. reflexivity. discriminate H.
    - destruct b2. discriminate H. discriminate H.
  + intros [H1 H2]. rewrite H1. rewrite H2. reflexivity.
Qed.

Theorem orb_true_iff : forall b1 b2,
  b1 || b2 = true <-> b1 = true \/ b2 = true.
Proof.
  intros b1 b2.
  split.
  + intros H.
    destruct b1. left. reflexivity. destruct b2. right. reflexivity. discriminate H.
  + intros [H1 | H2]. rewrite H1. reflexivity. rewrite H2. destruct b1. reflexivity. reflexivity.
Qed.

Lemma re_not_empty_correct : forall T (re : reg_exp T),
  (exists s, s =~ re) <-> re_not_empty re = true.
Proof.
  split.
  - intros H. destruct H as [ s Hmatch].
    induction Hmatch.
    + reflexivity.
    + reflexivity.
    + simpl. rewrite IHHmatch1.  rewrite IHHmatch2. reflexivity.
    + simpl. rewrite IHHmatch. reflexivity.
    + simpl. apply orb_true_iff. right. apply IHHmatch.
    + reflexivity.
    + reflexivity.
  - intros H.
    induction re.
    + inversion H.
    + exists []. apply MEmpty.
    + exists [t]. apply MChar.
    + simpl in H. apply andb_true_iff in H. destruct H as [H1 H2].
      apply IHre1 in H1. destruct H1 as [s1 H1].
      apply IHre2 in H2. destruct H2 as [s2 H2].
      exists (s1 ++ s2). apply MApp. apply H1. apply H2.
    + simpl in H. apply orb_true_iff in H. destruct H as [H1 | H2].
      * apply IHre1 in H1. destruct H1 as [s1 H1].
        exists s1. apply MUnionL. apply H1.
      * apply IHre2 in H2. destruct H2 as [s2 H2].
        exists s2. apply MUnionR. apply H2.
    + exists []. apply MStar0.
Qed.

Lemma star_app : forall T (s1 s2 : list T) ( re : reg_exp T),
  s1 =~ Star re -> 
  s2 =~ Star re ->
  s1 ++ s2 =~ Star re.
Proof.
  intros T s1 s2 re H1.
  induction H1 
    as [ | x' | s1 re1 s2' re2 Hmatch IH1 Hmatch2 IH2 
         | s1 re1 re2 Hmatch IH | re1 s2' re2 Hmatch IH
         | re'' | s1 s2' re'' Hmatch1 IH1 Hmatch2 IH2   ].
  - simpl. intros H. apply H.
  - intros H. simpl.
Abort.


Lemma star_app: forall T (s1 s2 : list T) (re re' : reg_exp T),
  re' = Star re ->
  s1 =~ re' ->
  s2 =~ Star re ->
  s1 ++ s2 =~ Star re.
Abort.

Lemma star_app : forall T (s1 s2 : list T) (re : reg_exp T),
  s1 =~ Star re -> 
  s2 =~ Star re -> 
  s1 ++ s2 =~ Star re.
Proof.
  intros T s1 s2 re H1.
  remember (Star re) as re' eqn:Eq.
  induction H1 
    as [ | x' 
         | s1 re1 s2' re2 Hmatch1 IH1 Hmatch2 IH2
         | s1 re1 re2 Hmatch IH | re1 s2' re2 Hmatch IH
         | re'' 
         | s1 s2' re'' Hmatch1 IH1 Hmatch2 IH2 ].
  - discriminate.
  - discriminate.
  - discriminate.
  - discriminate.
  - discriminate.
  - intros H. simpl. apply H.
  - intros. rewrite <- app_assoc.
    apply MStarApp.
    + apply Hmatch1.
    + apply IH2.
      * apply Eq.
      * apply H.
Qed.  

Lemma MStar'' : forall T (s : list T) (re : reg_exp T),
  s =~ Star re -> 
  exists ss : list (list T),
      s = fold app ss []
      /\ forall s', In s' ss -> s' =~ re.
Proof.
  intros T s re Hmatch.
  remember (Star re ) as re'.
  induction Hmatch
    as [|x'|s1 re1 s2' re2 Hmatch1 IH1 Hmatch2 IH2
        |s1 re1 re2 Hmatch IH|re1 s2' re2 Hmatch IH
        |re''|s1 s2' re'' Hmatch1 IH1 Hmatch2 IH2].
  - discriminate.
  - discriminate.
  - discriminate.
  - discriminate.
  - discriminate.
  - exists []. simpl. split.
    + reflexivity.
    + intros. destruct H.
  - destruct (IH2 Heqre') as [ss' [H1 H2]].
    injection Heqre' as Heqre'. destruct Heqre'.
    exists (s1 :: ss'). split.
    + simpl. rewrite H1. reflexivity.
    + intros s' HIn. destruct HIn.
      * rewrite <- H. apply Hmatch1.
      * apply H2 in H. apply H.
Qed. 


Module Pumping.

  Fixpoint pumping_constant {T} (re : reg_exp T) : nat :=
    match re with 
    | EmptySet => 1
    | EmptyStr => 1
    | Char _ => 2 
    | App re1 re2 => 
          pumping_constant re1 + pumping_constant re2
    | Union re1 re2 => 
          pumping_constant re1 + pumping_constant re2
    | Star r => pumping_constant r 
  end.

  Lemma pumping_constant_ge_1 :
    forall T ( re : reg_exp T),
          1 <= pumping_constant re.
  Proof.
    intros T re. induction re.
    - apply le_n.
    - apply le_n.
    - apply le_S. apply le_n.
    - simpl. apply le_trans with (n := pumping_constant re1).
      apply IHre1.
      apply le_plus_l.
    - simpl. apply le_trans with (n := pumping_constant re1).
      apply IHre1. apply le_plus_l.
    - simpl. apply IHre.
  Qed.

  Fixpoint napp {T} (n : nat) (l : list T) : list T :=
    match n with 
     | 0 => []
     | S n' => l ++ napp n' l
    end.

  Lemma napp_plus : forall T (n m : nat) (l : list T),
    napp (n + m) l = napp n l ++ napp m l.
  Proof.
    intros T n m l.
    induction n as [ | n' IHn'].
    - simpl. reflexivity.
    - simpl. rewrite IHn', app_assoc. reflexivity.
  Qed.
  
  Lemma napp_star : 
    forall T m s1 s2 (re : reg_exp T), 
           s1 =~ re -> s2 =~ Star re -> 
           napp m s1 ++ s2 =~ Star re.
  Proof.
    intros T m s1 s2 re Hs1 Hs2.
    induction m.
    - simpl. apply Hs2.
    - simpl. rewrite <- app_assoc.
      apply MStarApp.
      + apply Hs1.
      + apply IHm.
  Qed. 

  (* TODO-4 *)

  Lemma weak_pumping : forall T (re : reg_exp T) s,
    s =~ re ->
    pumping_constant re <= length s ->
    exists s1 s2 s3,
        s = s1 ++ s2 ++ s3 /\
        s2 <> [] /\
        forall m, s1 ++ napp m s2 ++ s3 =~ re.
  Proof.
    intros T re s Hmatch.
    induction Hmatch
      as [ | x | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
         | s1 re1 re2 Hmatch IH | s2 re1 re2 Hmatch IH
         | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2 ].
    - (* MEmpty *)
      simpl. intros contra. inversion contra.
    (* FILL IN HERE *) Admitted.


  Lemma pumping : forall T (re : reg_exp T) s,
    s =~ re ->
    pumping_constant re <= length s -> 
    exists s1 s2 s3,
          s = s1 ++ s2 ++ s3 /\
          s2 <> [] /\ 
          length s1 + length s2 <= pumping_constant re /\
          forall m, s1 ++ napp m s2 ++ s3 =~ re.

  Proof.
    intros T re s Hmatch.
    induction Hmatch
      as [ | x | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
         | s1 re1 re2 Hmatch IH | s2 re1 re2 Hmatch IH
         | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2 ].
    - (* MEmpty *)
      simpl. intros contra. inversion contra.
    (* FILL IN HERE *) Admitted.
End Pumping.

(* CASE STUDY : IMPROVING REFLECTION *)

Theorem eqb_refl : forall n : nat,
  ( n =? n ) = true.
Proof.
  intros n.
  induction n as [ | n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem eqb_eq : forall n1 n2 : nat,
  n1 =? n2 = true <-> n1 = n2.
Proof.
  intros n1 n2. split.
  - apply eqb_true.
  - intros H. rewrite H. rewrite eqb_refl. reflexivity.
Qed.

Theorem filter_not_empty_In : forall n l,
  filter (fun x => n=? x) l <> [] -> In n l.
  Proof.
    intros n l. induction l as [|m l' IHl'].
    - simpl. intros H. apply H. reflexivity.
    - simpl. destruct (n =? m) eqn:H.
      + intros _. rewrite eqb_eq in H. rewrite H.
        left. reflexivity.
      + intros H'. right. apply IHl'. apply H'.
  Qed.
  
Inductive reflect (P : Prop) : bool -> Prop :=
  | ReflectT (H :   P) : reflect P true
  | ReflectF (H : ~ P) : reflect P false.

Theorem iff_reflect : forall P b, (P <-> b = true) -> reflect P b.
Proof.
  (* WORKED IN CLASS *)
  intros P b H. destruct b eqn:Eb.
  - apply ReflectT. rewrite H. reflexivity.
  - apply ReflectF. unfold not. rewrite H. intros H'. discriminate.
Qed.
  
Theorem reflect_iff : forall P b, reflect P b -> (P <-> b = true).
Proof.
  intros P b H.
  destruct H.
  - split.
    + intros _ . reflexivity.
    + intros _ . apply H.
  - split.
    + intros HP. destruct H. apply HP. 
    + intros Hfalse. discriminate Hfalse. 
Qed.

Lemma eqbP : forall n m, reflect (n = m) (n =? m).
Proof.
  intros n m. apply iff_reflect. rewrite eqb_eq. reflexivity.
Qed.

Theorem filter_not_empty_In' : forall n l,
  filter (fun x => n =? x) l <> [] ->
  In n l.
Proof.
  intros n l. induction l as [|m l' IHl'].
  - simpl. intros H. apply H. reflexivity.
  - simpl. destruct (eqbP n m) as [EQnm | NEQnm].
    + intros _. rewrite EQnm. left. reflexivity.
    + intros H'. right. apply IHl'. apply H'.
Qed.

Fixpoint count n l :=
  match l with 
  | [] => 0
  | m :: l' => (if n=? m then 1 else 0) + count n l'
  end.

Theorem eqbP_practice : forall n l,
  count n l = 0 -> ~(In n l).
Proof.
  intros n l Hcount.
  induction l as [| m l' IHl'].
  - simpl. intros []. 
  - simpl in Hcount.
    destruct (eqbP n m) as [Heq | Hneq].
    + discriminate Hcount.
    + simpl in Hcount.
      intros [Hhead | Htail].
      * symmetry in Hhead. apply Hneq. apply Hhead.
      * apply IHl'. apply Hcount. apply Htail.
Qed.