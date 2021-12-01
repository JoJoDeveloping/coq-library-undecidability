(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*             Yannick Forster            [+]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(*                             [+] Affiliation Saarland Univ. *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

(** ** FRACTRAN_HALTING is undecidable *)

Require Import Undecidability.Synthetic.Undecidability.

From Undecidability.MinskyMachines
  Require Import MM MM_undec.

From Undecidability.FRACTRAN
  Require Import FRACTRAN Reductions.MM_FRACTRAN.

Theorem FRACTRAN_REG_undec : undecidable FRACTRAN_REG_HALTING.
Proof.
  apply (undecidability_from_reducibility MM_HALTING_undec).
  apply MM_FRACTRAN_REG_HALTING.
Qed.


Theorem FRACTRAN_REG_compl_undec : mundecidable (complement FRACTRAN_REG_HALTING).
Proof. 
  apply (mundecidability_from_reducibility MM_HALTING_compl_undec).
  apply reduces_complement.
  apply MM_FRACTRAN_REG_HALTING.
Qed.

Check FRACTRAN_REG_undec.

Theorem FRACTRAN_undec : undecidable FRACTRAN_HALTING.
Proof.
  apply (undecidability_from_reducibility FRACTRAN_REG_undec).
  apply FRACTRAN_REG_FRACTRAN_HALTING.
Qed.

Theorem FRACTRAN_compl_undec : mundecidable (complement FRACTRAN_HALTING).
Proof.
  apply (mundecidability_from_reducibility FRACTRAN_REG_compl_undec).
  apply reduces_complement.
  apply FRACTRAN_REG_FRACTRAN_HALTING.
Qed.
