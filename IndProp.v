Set Warnings "-notation-overridden".
From LF Require Export Logic.
From LF Require Export Basics.
From LF Require Export Lists.



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