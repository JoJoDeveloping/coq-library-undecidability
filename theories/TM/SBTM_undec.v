Require Import Undecidability.Synthetic.Undecidability.
Require Import Undecidability.TM.TM_undec.

Require Undecidability.TM.Reductions.HaltTM_1_to_HaltSBTM.
Require Undecidability.TM.Reductions.HaltSBTM_to_HaltSBTMu.

(** ** HaltSBTM is undecidable  *)

Lemma HaltSBTM_undec :
  undecidable SBTM.HaltSBTM.
Proof.
  apply (undecidability_from_reducibility HaltTM_1_undec).
  eapply HaltTM_1_to_HaltSBTM.reduction.
Qed.

Lemma HaltSBTMu_undec :
  undecidable SBTM.HaltSBTMu.
Proof.
  apply (undecidability_from_reducibility HaltSBTM_undec).
  apply HaltSBTM_to_HaltSBTMu.reduction.
Qed.

Lemma HaltSBTM_compl_undec :
  mundecidable (complement SBTM.HaltSBTM).
Proof. 
  apply (mundecidability_from_reducibility HaltTM_1_compl_undec).
  apply reduces_complement.
  eapply HaltTM_1_to_HaltSBTM.reduction.
Qed.

Lemma HaltSBTMu_compl_undec :
  mundecidable (complement SBTM.HaltSBTMu).
Proof.
  apply (mundecidability_from_reducibility HaltSBTM_compl_undec).
  apply reduces_complement.
  apply HaltSBTM_to_HaltSBTMu.reduction.
Qed.