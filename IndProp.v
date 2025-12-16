Set Warnings "-notation-overridden".
From LF Require Export Logic.
From LF Require Export Basics.


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


(* EXAMPLE : PERMUTATIONS *)

