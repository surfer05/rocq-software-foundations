Set Warnings "-notation-overridden".
Require Nat.
From LF Require Import Tactics.

(* factual claims : propositions *)
(* evidences of their truth : proofs *)
(* equality propositions : e1 = e2 *)
(* implications : P -> Q *)
(* quantified propositions : forall x, P *)
(* Coq is a Typed Language : every sensible expression has an associated type *)
(* any statement we might try to prove in Coq has a type, namely Prop( the type of *propositions* ) *)

Check (forall n m : nat, n + m = m + n) : Prop.

(* Being a proposition is one thing; being provable is a different thing *)

Check 2 = 2 : Prop.
Check 3 = 2 : Prop.
Check forall n : nat, n = 2 : Prop.

(* propositions are first-class entities that can be manipulated in all the same ways as any of the other things in Coq's world. *)

Definition plus_claim : Prop := 2 + 2 = 4.
Check plus_claim : Prop.

Theorem plus_claim_is_true :
  plus_claim.
Proof. reflexivity. Qed.

(* parameterized propositions : functions that take arguments of some type and return a proposition *)
Definition is_three (n : nat) : Prop :=
  n = 3.
Check is_three : nat -> Prop.

(* In Coq, functions that return propositions are said to define properties of their arguments. *)
Definition injective {A B} (f : A -> B) : Prop :=
  forall x y : A, f x = f y -> x = y.

Lemma succ_inj : injective S.
Proof.
  intros x y H. injection H as H1. apply H1.
Qed.
(* n=m is syntactic sugar for `eq n m` *)
(* = operator is a (binary) function that returns a Prop. *)
Check @eq.


(* LOGICAL CONNECTIVES *)

(* Conjunction *)
(* logical and *)
Example and_example : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  split.
  - reflexivity.
  - reflexivity.
Qed.

Check @conj : forall A B : Prop, A -> B -> A /\ B.

Example and_example' : 3 + 4 = 7 /\ 2*2 = 4.
Proof.
  apply conj.
  - reflexivity.
  - reflexivity.
Qed.

Example plus_is_0 : 
  forall n m : nat, n + m = 0 -> n = 0 /\ m = 0.
Proof.
  intros.
  destruct n as [|n'].
  - simpl in H. apply conj.
    + reflexivity.
    + apply H.
  - simpl in H. discriminate H.
Qed.

Lemma and_example2 :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof. 
  intros n m H.
  destruct H as [Hn Hm].
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.

Lemma and_example2' : 
  forall n m : nat, n=0/\m=0 -> n + m = 0.
Proof.
  intros n m [Hn Hm].
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.

Lemma and_example2'' :
  forall n m : nat, n = 0 -> m =0 -> n + m = 0.
Proof.
  intros n m Hn Hm.
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.

Lemma and_example3 : 
  forall n m : nat, n+m=0 -> n*m=0.
Proof.
  intros n m H. 
  apply plus_is_0 in H.
  destruct H as [Hn Hm].
  rewrite Hn. reflexivity.
Qed.

Lemma proj1 : forall P Q : Prop,
  P /\ Q -> P.
Proof.
  intros P Q [HP _]. 
  apply HP. 
Qed.

Lemma proj2 : forall P Q : Prop,
  P /\ Q -> Q.
Proof.
  intros P Q [_ HQ]. 
  apply HQ. 
Qed.

Theorem and_commut : forall P Q : Prop,
  P /\ Q -> Q /\ P.
Proof.
  intros P Q [HP HQ].
  split.
    - apply HQ.
    - apply HP.
Qed.

Theorem and_assoc : forall P Q R : Prop,
  P /\ ( Q /\ R ) -> ( P /\ Q) /\ R.
Proof.
  intros P Q R [HP [HQ HR]].
  split.
  - split. apply HP. apply HQ.
  - apply HR.
Qed.

Check and.


(* Disjunction *)
(* logical or *)

Check or.

Lemma factor_is_0 :
  forall n m : nat, n = 0 \/ m = 0 -> n * m = 0.
Proof.
  intros n m [Hn | Hm].
  - rewrite Hn. reflexivity.
  - rewrite Hm. rewrite mult_0_r. reflexivity.
Qed.

Lemma or_intro_l : forall A B : Prop, A -> A \/ B.
Proof.
  intros A B HA.
  left.
  apply HA.
Qed.

Lemma zero_or_succ : 
  forall n : nat, n = 0 \/ n = S (pred n).
Proof.
  intros [ |n'].
  - left. reflexivity.
  - right. reflexivity.
Qed.

Lemma mult_is_0 :
 forall n m, n * m = 0 -> n = 0 \/ m = 0.
Proof.
  intros n m H. 
  destruct n as [ | n'].
  - left. reflexivity.
  - destruct m as [ | m'].
    + right. reflexivity.
    + simpl in H.
      discriminate H.
Qed.

Theorem or_commut : forall P Q : Prop,
  P \/ Q -> Q \/ P.
Proof.
  intros P Q [HP | HQ].
  - right. apply HP.
  - left. apply HQ.
Qed.

(* Falsehood and Negation *)

Definition not ( P : Prop) := P -> False.
Check not : Prop -> Prop.
Notation "~ x" := (not x) : type_scope.

Theorem ex_falso_quodlibet : forall (P : Prop),
  False -> P.
Proof.
  intros P contra.
  destruct contra.
Qed.

Theorem not_implies_our_not : forall (P : Prop),
   ~P -> (forall (Q:Prop), P -> Q).
Proof.
  intros P HnotP Q HP.
  unfold not in HnotP.
  apply HnotP in HP.
  destruct HP.
Qed.


Notation " x <> y" := (~(x=y)) : type_scope.
Theorem zero_not_one : 0 <> 1.
Proof. 
  unfold not.
  intros.
  discriminate H.
Qed.

Theorem not_False :
  ~ False.
Proof.
  unfold not. 
  intros H.
  apply H.
Qed.

Theorem contradiction_implies_anything : forall P Q : Prop,
  (P /\ ~P) -> Q.
Proof.
  intros P Q [HP HNP].
  unfold not in HNP.
  apply HNP in HP.
  destruct HP.
Qed.

Theorem double_neg : forall P : Prop,
  P -> ~~P.
Proof.
  intros P H.
  unfold not.
  intros G.
  apply G. 
  apply H.
Qed.

Theorem contrapositive : forall (P Q : Prop),
  (P -> Q) -> (~Q -> ~P).
Proof.
  intros P Q H HnotQ.
  unfold not.
  intros HP.
  apply H in HP.
  apply HnotQ in HP.
  apply HP.
Qed.

Theorem not_both_true_and_false : forall P : Prop,
  ~(P /\ ~P).
Proof.
  intros P [HP HnotP].
  unfold not in HnotP.
  apply HnotP in HP.
  apply HP.
Qed.

Theorem de_morgan_not_or : forall ( P Q : Prop),
  ~(P \/ Q) -> ~P /\ ~Q.
Proof.
  intros P Q H.
  split.
  - unfold not. intros HP. apply H. left. apply HP.
  - unfold not. intros HQ. apply H. right. apply HQ.
Qed.

Lemma not_S_pred_n : 
  ~(forall n : nat, S ( pred n) = n).
Proof.
  intros.
  unfold not.
  intros H.
  specialize H with (n := 0).
  simpl in H.
  discriminate H.
Qed.

Theorem not_true_is_false : forall b : bool,
  b <> true -> b = false.
Proof.
  intros b H.
  destruct b eqn:HE.
  - unfold not in H.
    apply ex_falso_quodlibet.
    apply H. reflexivity.
  - reflexivity.
Qed. 

Theorem not_true_is_false' : forall b : bool,
  b <> true -> b = false.
Proof.
  intros [] H. 
  - unfold not in H.
    exfalso. 
    apply H. reflexivity.
  - reflexivity.
Qed.

(* Truth *)
Lemma True_is_true : True.
Proof.
  apply I.
Qed.

Definition disc_fn (n : nat) : Prop :=
  match n with 
  | O => True
  | S _ => False
  end.

Theorem disc_example : forall n, ~ ( O = S n).
Proof.
  intros n contra.
  assert (H : disc_fn O). { simpl. apply I. }
  rewrite contra in H.
  simpl in H. apply H.
Qed.

Theorem nil_is_not_cons : forall X (x : X) (xs : list X),
  ~ (nil = x :: xs).
Proof.
  intros X x xs contra.
  assert (H : match @nil X with
              | nil => True
              | _ :: _ => False
              end).
  { simpl. apply I. }
  rewrite contra in H.
  simpl in H. apply H.
Qed.

(* Logical Equivalence *)

Theorem iff_sym : forall P Q : Prop,
  (P <-> Q ) -> ( Q <-> P).
Proof.
  intros P Q [ HAB HBA ].
  split.
  - apply HBA.
  - apply HAB.
Qed.

Lemma not_true_iff_false : forall b,
  b <> true <-> b = false.
Proof.
  intros b.
  split.
  - apply not_true_is_false.
  - intros H. rewrite H. intros H'. discriminate H'.
Qed.

Lemma apply_iff_example1 : 
  forall P Q R : Prop, (P <-> Q) -> (Q -> R) -> (P -> R).
Proof.
  intros P Q R Hiff H HP. apply H. apply Hiff. apply HP.
Qed.

Lemma apply_iff_example2 : 
  forall P Q R : Prop, (P <-> Q) -> (P -> R) -> (Q -> R).
Proof.
  intros P Q R Hiff H HQ. apply H. apply Hiff. apply HQ.
Qed.

Theorem iff_refl : forall P : Prop,
  P <-> P.
Proof.
  intros P.
  split.
  - intros H. apply H.
  - intros H. apply H.
Qed.

Theorem iff_trans : forall P Q R : Prop,
  (P <-> Q) -> (Q <-> R) -> ( P <-> R).
Proof.
  intros P Q R Hpq Hqr.
  split.
  - intros H. apply Hqr. apply Hpq. apply H.
  - intros H. apply Hpq. apply Hqr. apply H.
Qed.


Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R.
  split.
  - intros H.
    destruct H as [HP | [HQ HR]].
    + split.
      * left. apply HP.
      * left. apply HP.
    + split.
      * right. apply HQ.
      * right. apply HR.
  - intros H.
    destruct H as [ HPQ HPR ].
    destruct HPQ as [ HP | HQ ].
    + left. apply HP.
    + destruct HPR as [ HP | HR].
      * left. apply HP.
      * right. split.
        -- apply HQ.
        -- apply HR.
Qed.  
    

From Stdlib Require Import Setoids.Setoid.

Lemma mul_eq_0 : forall n m, n*m = 0 <-> n=0 \/ m=0.
Proof.
  split.
  - apply mult_is_0.
  - apply factor_is_0.
Qed.

Theorem or_assoc :
  forall P Q R : Prop, P \/ ( Q \/ R) <-> (P \/ Q) \/ R.
Proof.
  intros P Q R.
  split.
  - intros H.
    destruct H as [ H | [ H | H]].
    + left. left. apply H.
    + left. right. apply H.
    + right. apply H. 
  - intros H.
    destruct H as[[H | H] | H].
    + left. apply H.
    + right. left. apply H.
    + right. right. apply H.
Qed.

Lemma mul_eq_0_ternary  :
  forall n m p, n * m * p = 0 <-> n=0 \/ m=0 \/ p=0.
Proof.
  intros n m p. 
  rewrite mul_eq_0. rewrite mul_eq_0. rewrite or_assoc.
  reflexivity.
Qed.


(* Existential Quantification *)

Definition Even x := exists n : nat, x = double n.
Check Even.

Lemma four_is_even : Even 4.
Proof.
  unfold Even. exists 2. reflexivity.
Qed.

Theorem exists_example_2 : forall n,
  ( exists m, n = 4 + m) ->
  ( exists o, n = 2 + o).
Proof.
  intros n [m Hm].
  exists (2 + m).
  apply Hm. 
Qed.


(* "P holds for all x" implies "there is no x for which P does not hold." *)
Theorem dist_not_exists : forall (X  : Type) ( P : X -> Prop),
  (forall x, P x) -> ~ ( exists x, ~ P x).
Proof.
  intros X P H1 H2.
  destruct H2 as [x H3].
  specialize H1 with (x := x).
  apply H3. 
  apply H1.
Qed.

Theorem dist_exists_or : forall (X : Type) ( P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> ( exists x, P x) \/ ( exists x, Q x).
Proof.
  intros X P Q.
  split.
  - intros [x [ HP | HQ]].
    + left. exists x. apply HP.
    + right. exists x. apply HQ.
  - intros [[x HP] | [x HQ]].
    + exists x. left. apply HP.
    + exists x. right. apply HQ.
Qed.


Theorem leb_plus_exists : forall n m, n <=? m = true -> exists x, m = n + x.
Proof.
  intros n. induction n as [ | n IHn'].
  - intros m H.  exists m. reflexivity.
  - intros m H.
    destruct m as [ | m'].
    + simpl in H. discriminate H.
    + simpl in H. apply IHn' in H. simpl. destruct H as [ x Hx]. exists x. 
      rewrite Hx. reflexivity.
Qed.

Theorem plus_exists_leb : 
  forall n m, (exists x, m = n + x) -> n <=? m = true.
Proof.
  intros n.
  induction n as [ | n' IHn'].
  - simpl. reflexivity.
  - intros m [x H].
    destruct m as [ | m'].
    + discriminate H.
    + simpl. apply IHn'. exists x. injection H as H1. apply H1.
Qed.   



(* PROGRAMMING WITH PROPOSITIONS *)

Fixpoint In { A : Type } ( x : A) (l : list A) : Prop :=
  match l with 
    | [] => False
    | x' :: l' => x' = x \/ In x l'
    end.

Example In_example_1 : In 4 [1;2;3;4;5].
Proof.
  simpl. right. right. right. left. reflexivity.
Qed.

Example In_example_2 :
  forall n, In n [2;4] ->
  exists n', n = 2 * n'.
Proof.
  simpl.
  intros n [H | [H | []]].
  - exists 1. rewrite <- H. reflexivity.
  - exists 2. rewrite <- H. reflexivity.
Qed.

Theorem In_map : 
  forall ( A B : Type) ( f : A -> B ) ( l : list A) ( x : A),
    In x l -> 
    In (f x ) (map f l).
Proof.
  intros A B f l x.
  induction l as [ | x' l' IHl'].
  - simpl.
    intros [].
  - simpl.
    intros [ H | H].
    + rewrite H. left. reflexivity.
    + right. apply IHl'. apply H.
Qed. 

Theorem In_map_iff : 
  forall (A B : Type) ( f : A -> B) ( l : list A) ( y : B),
          In y ( map f l) <->
          exists x, f x = y /\ In x l.
Proof.
  intros.
  split.
  - induction l as [ | x l' IHl'].
    + simpl. intros []. 
    + simpl. intros [ H | H].
      * exists x. split.
        -- apply H.
        -- left. reflexivity.
      * apply IHl' in H.
      destruct H as [x0 [Hfx0 HIn]].
        exists x0. split.
        -- apply Hfx0.
        -- right. apply HIn.
  - intros [x [Heq HIn]].
    rewrite <- Heq.
    apply In_map.
    apply HIn.
Qed.

Theorem In_app_iff : forall A l l' (a : A),
  In a (l ++ l') <-> In a l \/ In a l'.
Proof.
  intros A l.
  induction l as [ | a' l' IH].
  - simpl. split.
    + intros H. right. apply H.
    + intros [H | H]. destruct H. apply H.
  - intros l''  a. simpl. rewrite IH.
    split.
    + intros [H | [ H | H]].
      * left. left. apply H.
      * left. right. apply H.
      * right. apply H.
    + intros [ [H | H] | H].
      * left. apply H.
      * right. left. apply H.
      * right. right. apply H.
Qed.  

Fixpoint All { T : Type} ( P : T -> Prop) ( l : list T) : Prop :=
  match l with 
    | [] => True
    | x :: l' => P x /\ All P l'
    end.

Theorem All_In : 
  forall T ( P : T -> Prop) ( l : list T),
    ( forall x, In x l -> P x) <-> All P l.
Proof.
  intros T P l. 
  induction l as [ | a l' IH].
  - simpl. split. auto. intros _ x [].
  - simpl. rewrite <- IH.
    split. intros.
    + split.
      * apply H. left. reflexivity.
      * intros x Hin. apply H. right. apply Hin.
    + intros H. destruct H as [Hpa Hall].
      intros x [ Heq | Hin].
      * subst. assumption. 
      * apply Hall. assumption. 
Qed.

Definition combine_odd_even ( Podd Peven : nat -> Prop) : nat -> Prop :=
  fun n => if odd n then Podd n else Peven n.

Check combine_odd_even.

Theorem combine_odd_even_intro : 
  forall (Podd Peven : nat -> Prop) ( n : nat),
         ( odd n = true -> Podd n) -> 
         ( odd n = false -> Peven n) -> 
         combine_odd_even Podd Peven n.
Proof.
  intros.
  unfold combine_odd_even.
  destruct (odd n).
  - apply H. reflexivity.
  - apply H0. reflexivity.
Qed.

Theorem combine_odd_even_elim_odd :
  forall (Podd Peven : nat -> Prop) (n : nat),
         combine_odd_even Podd Peven n -> 
         odd n = true -> 
         Podd n.
Proof.
  intros.
  unfold combine_odd_even in H.
  rewrite H0 in H.
  apply H.
Qed.

Theorem combine_odd_even_elim_even :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    odd n = false ->
    Peven n.
Proof.
  intros. 
  unfold combine_odd_even in H. 
  rewrite H0 in H.
  apply H.
Qed.

(* APPLYING THEOREMS AS ARGUMENTS *)

Lemma add_comm3_take4 : 
  forall x y z, x + ( y + z) = (z + y) + x.
Proof.
  intros x y z.
  rewrite( add_comm x ( y + z)).
  rewrite ( add_comm y z).
  reflexivity.
Qed.

Theorem in_not_nil :
  forall A ( x : A) (l : list A), In x l -> l <> [].
Proof.
  intros A x l H. unfold not. intro Hl.
  rewrite Hl in H. simpl in H. apply H.
Qed.

Lemma in_not_nil_42 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply ( in_not_nil _ _ _ H).
Qed.

Example lemma_application_ex :
  forall {n : nat} {ns : list nat},
          In n ( map ( fun m => m*0) ns) ->
          n = 0.
Proof.
  intros n ns H.
  destruct (proj1 _ _ (In_map_iff _ _ _ _ _) H) as [m [Hm _]].
  rewrite mult_0_r in Hm. 
  rewrite <- Hm.
  reflexivity.
Qed.



(* WORKING WITH DECIDABLE PROPERTIES *)

Example even_42_bool : even 42 = true.
Proof. reflexivity. Qed.

Example even_42_prop : Even 42.
Proof. unfold Even. exists 21. reflexivity. Qed.

Lemma even_double : forall k, even (double k) = true.
Proof.
  intros k.
  induction k as [ | k' IHk'].
  - simpl. reflexivity.
  - simpl. apply IHk'.
Qed.

Lemma even_double_conv : forall n, exists k,
  n = if even n then double k else S (double k).
Proof.
  induction n as [| n IH].
  - exists 0. simpl. reflexivity.
  - destruct IH as [k Hk].
    destruct (even n) eqn:Hev in Hk.
    + exists k.
      rewrite even_S. rewrite Hev. simpl.
      rewrite Hk. reflexivity.
    + exists (S k).
      rewrite even_S. rewrite Hev. simpl.
      rewrite Hk. simpl. reflexivity.
Qed.


Theorem even_bool_prop : forall n,
  even n = true <-> Even n.
Proof.
  intros n. split.
  - intros H. destruct (even_double_conv n) as [ k Hk].
    rewrite Hk. rewrite H. exists k. reflexivity.
  - intros [k Hk]. rewrite Hk. apply even_double.
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

Definition is_even_prime n :=
  if n =? 2 then true
  else false.

Example even_1000 : Even 1000.
Proof. unfold Even. exists 500. reflexivity. Qed.

Example even_1000' : even 1000 = true.
Proof. reflexivity. Qed.

Example even_1000'' : Even 1000.
Proof. apply even_bool_prop. reflexivity. Qed.

Example not_even_1001 : even 1001 = false.
Proof.
  reflexivity.
Qed.

Lemma plus_eqb_example : forall n m p : nat,
  n =? m = true -> n + p =? m + p = true.
Proof.
  (* WORKED IN CLASS *)
  intros n m p H.
  rewrite eqb_eq in H.
  rewrite H.
  rewrite eqb_eq.
  reflexivity.
Qed.

(* ------------ SOME THEOREMS FROM THE SECTION REMAINS --------------- *)
(* ------------------------------------------------------------------- *)
(* ------------------------------------------------------------------- *)
(* ------------------------------------------------------------------- *)
(* ------------------------------------------------------------------- *)
(* ------------------------------------------------------------------- *)
(* ------------------------------------------------------------------- *)
(* ------------------------------------------------------------------- *)

(* Pending theorems to prove  *)
(* andb_true_iff *)
(* orb_true_iff *)
(* eqb_neq *)


(* Fixpoint eqb_list *)
(* eqb_list_true_iff *)


Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) : bool
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
Theorem forallb_true_iff : forall X test (l : list X),
  forallb test l = true <-> All (fun x => test x = true) l.
Proof.
  (* FILL IN HERE *) Admitted.



(* ----------------- THE LOGIC OF COQ -------------------------------- *)

(* Functional Extensionality *)

Example function_equality_ex1 :
  (fun x => 3 + x) = ( fun x => (pred 4) + x).
Proof. reflexivity. Qed.

Axiom functional_extensionality : forall { X Y : Type} {f g : X -> Y},
  (forall (x : X), f x = g x) -> f = g.

Example function_equality_ex2 : 
  (fun x => plus x 1) = (fun x => plus 1 x).
Proof.
  apply functional_extensionality. intros x.
  apply add_comm.
Qed.

Print Assumptions function_equality_ex2.
