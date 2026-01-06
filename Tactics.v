Set Warnings "-notation-overridden".
From LF Require Export Poly.

(* THE APPLY TACTIC *)
Theorem silly1 : forall (n m : nat),
  n = m -> n =m.
Proof.
  intros n m eq.
apply eq. Qed.

Theorem silly2 : forall (n m o p: nat ),
  n = m ->
  (n = m -> [n;o]=[m;p]) ->
  [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  apply eq2.
  apply eq1.
Qed.

Theorem silly2a : forall (n m : nat),
  (n,n) = (m,m) ->
  (forall (q r : nat), (q,q) = (r,r) -> [q]=[r]) ->
  [n] = [m].
Proof.
  intros n m eq1 eq2.
apply eq2. apply eq1. Qed.

Theorem silly_ex : forall p,
  (forall n, even n = true -> even (S n)=false) ->
  (forall n, even n = false -> odd n = true) ->
  even p = true ->
  odd (S p)= true.
Proof.
  intros. 
apply H0. apply H. apply H1. Qed.

Theorem silly3 : forall (n m : nat),
  n = m ->
  m = n.
Proof.
  intros.
  symmetry. apply H. 
Qed.

Theorem rev_exercise1 : forall (l l' : list nat),
  l = rev l' ->
  l' = rev l.
Proof.
intros. rewrite H. symmetry. apply rev_involutive. Qed.

(* [apply] cannot be applied instead of [rewrite <- H], *)
(* should use [symmetry] before. *)

(* THE APPLY WITH TACTIC *)
Example trans_eq_example : forall (a b c d e f : nat ),
  [a;b] = [c;d] ->
  [c;d] = [e;f] ->
  [a;b] = [e;f].
Proof.
  intros.
  rewrite H.
  apply H0.
Qed.

Theorem trans_eq : forall (X : Type) (x y z : X),
  x = y -> y = z -> x = z.
Proof.
  intros.
  rewrite H.
  apply H0.
Qed.

Example trans_eq_example' : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros.
  apply trans_eq with (y:=[c;d]).
  apply H. apply H0.
Qed.

Example trans_eq_example'' : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  transitivity [c;d].
  apply eq1. apply eq2. Qed.

Example trans_eq_exercise : forall (n m o p : nat), 
  m = (minustwo o) ->
  (n+p) = m ->
  (n + p) = (minustwo o).
Proof.
  intros.
  transitivity m.
  apply H0. apply H.
Qed.

(* THE INJECTION AND DISCRIMINATE TACTICS  *)
Theorem S_injective : forall (n m : nat),
  S n = S m -> 
  n = m.
Proof. 
  intros n m H1.
  assert ( H2 : n = pred (S n)). { reflexivity. }
  rewrite H2. rewrite H1. simpl. reflexivity.
Qed.

Theorem S_injective' : forall (n m : nat),
  S n = S m ->
  n = m.
Proof.
  intros n m H.
  injection H as Hnm. apply Hnm.
Qed.

Theorem injection_ex1 : forall (n m o : nat),
  [n;m]=[o;o] ->
  n = m.
Proof.
  intros n m o H.
  injection H as H1 H2.
  rewrite H1. symmetry. apply H2.
Qed.

Example injection_ex3 : forall (X : Type)(x y z : X ) (l j : list X),
  x :: y :: l = z :: j ->
  j = z :: l ->
  x = y.
Proof.
  intros.
  injection H as H1 H2.
  rewrite H0 in H2.
  injection H2 as H3.
  rewrite H1. symmetry. apply H3.
Qed.

Theorem discriminate_ex1 : forall (n m : nat),
  false = true -> 
  n = m.
Proof.
  intros. 
  discriminate H.
Qed.

Theorem discriminate_ex2 : forall (n : nat),
  S n = O ->
  2 + 2 = 5.
Proof.
  intros.
  discriminate H.
Qed. 

Example discriminate_ex3 : 
  forall ( X : Type) (x y z : X)(l j : list X),
    x :: y :: l = [] ->
    x = z.
Proof.
  intros. 
  discriminate H.
Qed.

Theorem eqb_0_l : forall n,
  0 =? n = true -> n = 0.
Proof. 
  intros n.
  destruct n as [ | n'] eqn:E.
  - intros H. reflexivity.
  - intros H. discriminate H.
Qed. 

Theorem f_equal : forall (A B : Type) (f : A -> B) ( x y : A),
  x = y -> f x = f y.
Proof.
  intros A B f x y eq.
  rewrite eq.
  reflexivity.
Qed.

Theorem eq_implies_succ_equal : forall (n m : nat),
  n = m -> S n = S m.
Proof. 
  intros. apply f_equal.
  apply H.
Qed.

Theorem eq_implies_succ_equal' : forall ( n m : nat),
  n = m -> S n = S m.
Proof.
  intros n m H. f_equal. apply H. 
Qed.

(* USING TACTICS ON HYPOTHESES *)

Theorem S_inj : forall (n m : nat )(b : bool),
  ((S n) =? (S m)) = b ->
  (n =? m) = b.
Proof.
  intros n m b H. simpl in H. apply H. 
Qed.

Theorem silly4 : forall (n m p q : nat),
  (n = m -> p = q) ->
  m = n -> 
  q = p.
Proof.
  intros n m p q EQ H.
  symmetry in H. apply EQ in H. symmetry in H.
  apply H.
Qed.

(* SPECIALIZING HYPOTHESES *)

Theorem specialize_example : forall n,
  (forall m, m*n=0)
  -> n =0.
Proof.
  intros n H.
  specialize H with (m := 1).
  rewrite mult_1_l in H.
  apply H. 
Qed.

Example trans_eq_example''' : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  specialize trans_eq with (y:=[c;d]) as H.
  apply H.
  apply eq1.
  apply eq2.
Qed.

(* VARYING THE INDUCTION HYPOTHESIS *)

Theorem double_injective_FAILED : forall n m,
  double n = double m ->
  n = m.
Proof.
  intros n m. induction n as [ | n' IHn' ].
  - simpl. intros eq. destruct m as [ | m'] eqn:E.
    + reflexivity.
    + discriminate eq.
  - intros eq. destruct m as [ | m'] eqn:E.
    + discriminate eq.
    + f_equal.
Abort.

Theorem double_injective : forall n m,
  double n = double m ->
    n = m.
Proof.
  intros n. induction n as [ | n' IHn'].
  - simpl. intros m eq. destruct m as [ | m'] eqn:E.
    + reflexivity.
    + discriminate eq.
  - intros m eq.
    destruct m as [ | m'] eqn:E.
    + discriminate eq.
    + f_equal.
  apply IHn'.
  simpl in eq. 
  injection eq as goal.
  apply goal.
Qed.

Theorem eqb_true : forall n m,
  n =? m = true -> n = m.
Proof.
  intros n.
  induction n as [ | n' IHn'].
  - intros m H.
    destruct m as [| m'].
    + reflexivity.
    + discriminate H.
  - intros m H.
    destruct m as [ | m'].
    + discriminate H.
    + apply IHn' in H.  rewrite H. reflexivity.
Qed.

Theorem plus_n_n_injective : forall n m,
  n + n = m + m ->
  n = m.
Proof.
  intros n. induction n as [| n' IHn'].
  - intros m H. destruct m as [| m'].
    + reflexivity.
    + simpl in H. discriminate H.
  - intros m H. destruct m as [| m'].
    + simpl in H. discriminate H.
    + simpl in H.
      rewrite <- plus_n_Sm in H.
      rewrite <- plus_n_Sm in H.
      injection H as H.
      apply IHn' in H.
      rewrite H.
      reflexivity.
Qed.

Theorem double_injective_take2 : forall n m,
    double n = double m ->
    n = m.
  Proof.
    intros n m.
    generalize dependent n.
    induction m as [| m' IHm'].
    - simpl. intros n eq. destruct n as [| n'] eqn:E.
      + reflexivity.
      + discriminate eq.
    - intros n eq. destruct n as [| n'] eqn:E.
      + discriminate eq.
      + f_equal.
        apply IHm'. injection eq as goal. apply goal. 
Qed.

(* REWRITING WITH CONDITIONAL STATEMENTS *)

Lemma sub_add_leb : forall n m, n <=? m = true -> (m-n)+n = m.
Proof.
  intros n.
  induction n as [ | n' IHn'].
  - intros m H.
    rewrite add_0_r.
    destruct m as [ | m'].
    + reflexivity.
    + reflexivity.
  - intros m H. destruct m as [ | m'].
    + discriminate.
    + simpl in H. simpl. rewrite <- plus_n_Sm. rewrite IHn'. reflexivity. apply H.
Qed.

Theorem nth_error_after_last : forall (n : nat)(X : Type) (l : list X),
  length l = n ->
  nth_error l n = None.
Proof.
  intros n X l H.
  revert n H.
  induction l as [ | x l' IHl'].
  - intros n H.
    destruct n as [ | n'].
    + reflexivity.
    + simpl. reflexivity.
  - intros n H.
    destruct n as [ | n'].
    + simpl in H. discriminate H.
    + simpl in H.
      injection H as Hlen.
      simpl. 
      apply IHl'.
      apply Hlen.
Qed.

(* UNFOLDING DEFINITIONS *)

Definition square n := n*n.

Lemma mul_succ_r : forall n m : nat,
  n * (S m) = n + n * m.
Proof.
  intros n m.
  induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl.
    rewrite IHn'.
    rewrite add_assoc.
    rewrite add_assoc.
    rewrite (add_comm m n').
    reflexivity.
Qed.

Theorem mul_comm : forall m n : nat,
  m*n = n*m.
Proof.
  intros n m.
  induction n as [ | n' IHn'].
  - simpl. rewrite mult_0_r. reflexivity.
  - simpl. rewrite mul_succ_r. rewrite IHn'. reflexivity.
Qed.

Lemma square_mult : forall n m, square (n*m) = square n * square m.
Proof.
  intros n m.
  simpl.
  unfold square. 
  rewrite mult_assoc.
  assert (H : n * m * n = n * n * m).
  { rewrite mul_comm. apply mult_assoc. }
  rewrite H. rewrite mult_assoc. reflexivity.
Qed.

Definition foo (x : nat) := 5.

Fact silly_fact_1 : forall m, foo m +1 = foo(m  +1) + 1.
Proof.
  intros m.
  simpl. reflexivity.
Qed.

Definition bar x :=
  match x with 
  | O => 5
  | S _ => 5
  end.

Fact silly_fact_2 : forall m, bar m  + 1 = bar ( m + 1) +1.
Proof.
  intros m.
  unfold bar.
  destruct m eqn:E.
  - reflexivity.
  - reflexivity.
Abort.


Definition sillyfun (n : nat) : bool :=
  if n =? 3 then false
  else if n =? 5 then false
  else false.

Theorem sillyfun_false : forall (n : nat),
  sillyfun n = false.
Proof.
  intros n. unfold sillyfun.
  destruct (n =? 3) eqn:E1.
    - reflexivity.
    - destruct (n =? 5) eqn:E2.
      + reflexivity.
      + reflexivity.
Qed.

Fixpoint split { X Y : Type} (l : list (X*Y)) : (list X)*(list Y) :=
  match l with 
    | [] => ([], [])
    | (x,y)::t => match split t with 
                  | (lx, ly) => (x :: lx, y :: ly)
                  end
  end.

Theorem combine_split : forall X Y (l : list (X * Y)) l1 l2,
  split l = (l1, l2) ->
  combine l1 l2 = l.
Proof.
  intros X Y l. induction l as [| [x y] l' IHl'].
  - (* Base Case *)
    intros l1 l2 H.
    simpl in H. injection H as H1 H2. subst.
    reflexivity.
  - (* Inductive Step *)
    intros l1 l2 H.
    simpl in H.
    destruct (split l') as [lx ly] eqn:Heq.
    injection H as H1 H2. subst.
    simpl.
    rewrite IHl'.
    + reflexivity.
    + reflexivity.
Qed.

Definition sillyfun1 (n : nat) : bool :=
  if n =? 3 then true
  else if n =? 5 then true
  else false.

Theorem sillyfun1_odd_FAILED : forall (n : nat),
  sillyfun1 n = true ->
  odd n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq.
  destruct (n =? 3).
Abort.

Theorem sillyfun1_odd : forall (n : nat),
  sillyfun1 n = true ->
  odd n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq.
  destruct (n =? 3) eqn:Heqe3.
  - apply eqb_true in Heqe3.
    rewrite -> Heqe3. reflexivity.
  - destruct (n =? 5) eqn:Heqe5.
    + apply eqb_true in Heqe5.
      rewrite -> Heqe5. reflexivity.
    + discriminate eq.
Qed.

Theorem bool_fn_applied_thrice :
  forall (f : bool -> bool) (b : bool),
  f (f (f b)) = f b.
Proof.
  intros f b. destruct b.
  - destruct (f true) eqn:Hft.
    + rewrite Hft. rewrite Hft. reflexivity.
    + destruct (f false) eqn:Hff.
      * rewrite Hft. reflexivity.
      * rewrite Hff. reflexivity.
  - destruct (f false) eqn:Hff.
    + destruct (f true) eqn:Hft.
      * rewrite Hft. reflexivity.
      * rewrite Hff. reflexivity.
    + rewrite Hff. rewrite Hff. reflexivity.
Qed.

(* ADDITIONAL EXERCISES *)

Theorem eqb_refl : forall n : nat,
  ( n =? n ) = true.
Proof.
  intros n.
  induction n as [ | n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem eqb_sym : forall (n m : nat),
  (n =? m) = (m =? n).
Proof.
  intros n m.
  destruct (n =? m) eqn:E.
  + (* true *)
    symmetry. apply eqb_true in E. rewrite -> E. apply eqb_refl.
  + (* false *)
    generalize dependent m.
    induction n.
    - destruct m.
      * intros E. discriminate E.
      * reflexivity.
    - destruct m.
      * reflexivity.
      * intros E. simpl in E. apply IHn in E. simpl. rewrite <- E. reflexivity.
Qed.

Theorem eqb_trans : forall n m p,
  n =? m = true ->
  m =? p = true ->
  n =? p = true.
Proof.
  intros n m p eq1 eq2.
  apply eqb_true in eq1. apply eqb_true in eq2.
  rewrite -> eq1. rewrite <- eq2.
  apply eqb_refl.
Qed.

Definition split_combine_statement : Prop
  := forall X Y (l1 : list X) (l2 : list Y), length l1 = length l2 -> split (combine l1 l2) = (l1, l2).

Theorem split_combine : split_combine_statement.
Proof.
  intros X Y.
  induction l1 as [| x].
  + intros l2 H.
    destruct l2 as [| y].
    - reflexivity.
    - discriminate H.
  + intros l2 H. destruct l2 as [| y].
    - discriminate H.
    - injection H as H. apply IHl1 in H.
      simpl. rewrite -> H.
      reflexivity.
Qed.

Theorem filter_exercise : forall (X : Type) (test : X -> bool)
                                 (x : X) (l lf : list X),
  filter test l = x :: lf ->
  test x = true.
Proof.
  intros X test x l lf.
  destruct l as [| x'].
  + simpl. intros H. discriminate H.
  + induction (x' :: l).
    - simpl. intros H. discriminate H.
    - simpl. destruct (test x0) eqn:T.
      * intros H. injection H as H. rewrite -> H in T. apply T.
      * apply IHl0.
Qed.

Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) : bool
  := match l with
     | [] => true
     | x :: l' => if test x then forallb test l' else false
     end.

Example test_forallb_1 : forallb odd [1;3;5;7;9] = true.
Proof. reflexivity. Qed.
Example test_forallb_2 : forallb negb [false;false] = true.
Proof. reflexivity. Qed.
Example test_forallb_3 : forallb even [0;2;4;5] = false.
Proof. reflexivity. Qed.
Example test_forallb_4 : forallb (eqb 5) [] = true.
Proof. reflexivity. Qed.

Fixpoint existsb {X : Type} (test : X -> bool) (l : list X) : bool
  := match l with
     | [] => false
     | x :: l' => if test x then true else existsb test l'
     end.

Example test_existsb_1 : existsb (eqb 5) [0;2;3;6] = false.
Proof. reflexivity. Qed.
Example test_existsb_2 : existsb (andb true) [true;true;false] = true.
Proof. reflexivity. Qed.
Example test_existsb_3 : existsb odd [1;0;0;0;0;3] = true.
Proof. reflexivity. Qed.
Example test_existsb_4 : existsb even [] = false.
Proof. reflexivity. Qed.

Definition existsb' {X : Type} (test : X -> bool) (l : list X) : bool
  := negb (forallb (fun x => negb (test x)) l).

Theorem existsb_existsb' : forall (X : Type) (test : X -> bool) (l : list X),
  existsb test l = existsb' test l.
Proof. intros X test.
  induction l.
  + reflexivity.
  + simpl.
    unfold existsb'.
    destruct (test x) eqn:T.
    - simpl. rewrite -> T. reflexivity.
    - simpl. rewrite -> T. rewrite -> IHl. reflexivity.
Qed.
