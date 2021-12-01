Require Import Undecidability.PCP.PCP.
Require Import Undecidability.Synthetic.Undecidability.

From Undecidability.PCP.Reductions Require 
  SR_to_MPCP MPCP_to_MPCPb MPCP_to_PCP PCP_to_PCPb PCPb_iff_iPCPb PCPb_iff_dPCPb.

Require Undecidability.StringRewriting.SR_undec.

(** ** PCP is undecidable *)

(* The modified Post correspondence problem is undecidable. *)
Lemma MPCP_undec : undecidable MPCP.
Proof.
  apply (undecidability_from_reducibility SR_undec.SR_undec).
  exact SR_to_MPCP.reduction.
Qed.
Lemma MPCP_compl_undec : mundecidable (complement MPCP).
Proof. (*
  apply (mundecidability_from_reducibility SR_undec.SR_compl_undec).
  apply reduces_complement.
  exact SR_to_MPCP.reduction.
Qed.*)
Admitted.

Check MPCP_undec.

(* The modified Post correspondence problem restricted to binary strings is undecidable. *)
Lemma MPCPb_undec : undecidable MPCPb.
Proof.
  apply (undecidability_from_reducibility MPCP_undec).
  exact MPCP_to_MPCPb.reduction.
Qed.

Check MPCPb_undec.

(* The Post correspondence problem is undecidable. *)
Lemma PCP_undec : undecidable PCP.
Proof.
  apply (undecidability_from_reducibility MPCP_undec).
  exact MPCP_to_PCP.reduction.
Qed.
Lemma PCP_compl_undec : mundecidable (complement PCP).
Proof.
  apply (mundecidability_from_reducibility MPCP_compl_undec).
  apply reduces_complement.
  exact MPCP_to_PCP.reduction.
Qed.

Check PCP_undec.

(* The Post correspondence problem restricted to binary strings is undecidable. *)
Lemma PCPb_undec : undecidable PCPb.
Proof.
  apply (undecidability_from_reducibility PCP_undec).
  exact PCP_to_PCPb.reduction.
Qed.
Lemma PCPb_compl_undec : mundecidable (complement PCPb).
Proof.
  apply (mundecidability_from_reducibility PCP_compl_undec).
  apply reduces_complement.
  exact PCP_to_PCPb.reduction.
Qed.

Check PCPb_undec.

(* The Post correspondence problem restricted to binary strings is undecidable. *)
Lemma iPCPb_undec : undecidable iPCPb.
Proof.
  apply (undecidability_from_reducibility PCPb_undec).
  exists id. exact PCPb_iff_iPCPb.PCPb_iff_iPCPb.
Qed.

(* Complement reduction. *)
Lemma iPCPb_compl_undec : mundecidable (complement iPCPb).
Proof.
  apply (mundecidability_from_reducibility PCPb_compl_undec).
  apply reduces_complement.
  exists id. exact PCPb_iff_iPCPb.PCPb_iff_iPCPb.
Qed.

Check iPCPb_undec.

(* The Post correspondence problem restricted to binary strings is undecidable. *)
Lemma dPCPb_undec : undecidable dPCPb.
Proof.
  apply (undecidability_from_reducibility PCPb_undec).
  exists id. exact PCPb_iff_dPCPb.PCPb_iff_dPCPb.
Qed.

Check dPCPb_undec.
