From Stdlib Require Extraction.
Set Extraction Output Directory ".".
Extraction Language OCaml.

Set Warnings "-notation-overridden,-notation-incompatible-prefix".
From Stdlib Require Import Arith.
From Stdlib Require Import Init.Nat.
From Stdlib Require Import EqNat.
From LF Require Import ImpCEvalFun.


Extraction "imp1.ml" ceval_step.

Extract Inductive bool => "bool" [ "true" "false" ].


Extract Inductive nat => "int"
  [ "0" "(fun x -> x + 1)" ]
  "(fun zero succ n ->
      if n=0 then zero () else succ (n-1))".

Extract Constant plus => "( + )".
Extract Constant mult => "( * )".
Extract Constant eqb => "( = )".


Extraction "imp2.ml" ceval_step.


From Stdlib Require Import ExtrOcamlBasic.
From Stdlib Require Import ExtrOcamlString.

(** We also need one more variant of booleans. *)

Extract Inductive sumbool => "bool" ["true" "false"].

(** The extraction is the same as always. *)

From LF Require Import Imp.
From LF Require Import ImpParser.
From LF Require Import Maps.
Extraction "imp.ml" empty_st ceval_step parse.

