From Undecidability.FOL.Util Require Import Syntax sig_bin.
From Undecidability.FOL.Util Require  Tarski Deduction Kripke.
From Undecidability.DiophantineConstraints Require Import H10C H10C_undec.
From Undecidability.FOL.Reductions Require H10UPC_to_FOL_minimal H10UPC_to_FSAT.
From Undecidability.FOL.Reductions Require H10UPC_to_FOL_full_fragment.
From Undecidability.Synthetic Require Import Definitions Undecidability ReducibilityFacts.

Set Default Proof Using "Type".

(** * Validity, provability, satisfiability of dyadic first-order logic *)

(* 
  Problems(s):
    Dyadic validity
    Dyadic satisfiability
    Dyadic provability
    Dyadic classical provability
    Dyadic Kripke validity
    Dyadic Kripke satisfiability
    Dyadic finite validity
    Dyadic finite satisfiability

  All for a small logical fragment.
*)

(**

 The notation used throughout this file differs from the one presented in "Undecidability of Dyadic First-Order Logic in Coq" by Hostert et al (ITP 2022).
 The following table translates the most important differences.
 Individual reductions contain their own tables, if necessary.

 #<table><tr><td>Coq</td><td>Paper</td></tr>
         <tr><td>H10UPC</td><td>UDPC</td></tr>
         <tr><td>H10UC</td><td>UDC</td></tr>
         <tr><td>form</td><td>mathbb F</td></tr>
         <tr><td>Pr</td><td>rotated double tilde</td></tr>
</table>#

 

*)
Definition minimalForm (ff:falsity_flag) := @form sig_empty sig_binary FragmentSyntax.frag_operators ff.


Section full_fragment.
  Import H10UPC_to_FOL_full_fragment FullTarski.
  (** ** Dyadic validity, large fragment *)
  Lemma minSignatureValiditiyUndec : @undecidable (@form sig_empty sig_binary FullSyntax.full_operators falsity_on) valid.
  Proof.
    apply (undecidability_from_reducibility H10UPC_SAT_undec).
    exact fullFragValidReduction.
  Qed.
End full_fragment.

Section general.
  Import H10UPC_to_FOL_minimal Tarski Deduction Kripke.

  (** ** Dyadic validity, small fragment without negation *)
  Lemma minValidityUndec : undecidable (fun k : minimalForm falsity_off => valid k).
  Proof.
    apply (undecidability_from_reducibility H10UPC_SAT_undec).
    exact validReduction.
  Qed.

  (** ** Dyadic Kripke validity, small fragment without negation *)
  Lemma minKripkeValidityUndec : undecidable (fun k : minimalForm falsity_off => kvalid k).
  Proof.
    apply (undecidability_from_reducibility H10UPC_SAT_undec).
    exact kripkeValidReduction.
  Qed.

  Definition int_provable (phi : minimalForm falsity_off) : Prop := nil ⊢M phi.
  Definition class_provable (phi : minimalForm falsity_off) : Prop := nil ⊢C phi.

  (** ** Dyadic int. provability, small fragment without negation *)
  Lemma minProvabilityUndec : undecidable int_provable.
  Proof.
    apply (undecidability_from_reducibility H10UPC_SAT_undec).
    exact proveReduction.
  Qed.

  (** ** Dyadic classical provability, small fragment without negation *)
  Lemma minClassicalProvabilityUndec (LEM : forall P:Prop, P \/ ~P) : undecidable class_provable.
  Proof.
    apply (undecidability_from_reducibility H10UPC_SAT_undec).
    apply classicalProveReduction, LEM.
  Qed.

  (** ** Dyadic satisfiability, small fragment with negation *)
  Lemma minSatisfiabilityUndec : undecidable (fun k : minimalForm falsity_on => satis k).
  Proof.
    apply (undecidability_from_reducibility H10UPC_SAT_compl_undec).
    apply satisReduction.
  Qed.

  (** ** Dyadic Kripke satisfiability, small fragment with negation *)
  Lemma minKripkeSatisfiabilityUndec : undecidable (fun k : minimalForm falsity_on => ksatis k).
  Proof.
    apply (undecidability_from_reducibility H10UPC_SAT_compl_undec).
    apply kripkeSatisReduction.
  Qed.

End general.


Section finite.
  Import H10UPC_to_FSAT.
  (** Reduction into fragment syntax. Step 1: define FSAT for fragment syntax *)
  Definition FSAT_frag (phi : minimalForm falsity_on) :=
  exists D (I : Tarski.interp D) rho, FSAT.listable D /\ decidable (fun v => Tarski.i_atom (P:=tt) v) /\ @Tarski.sat _ _ D I _ rho phi.

  (** Also define FVAL for fragment syntax *)
  Definition FVAL_frag (phi : minimalForm falsity_on) :=
  forall D (I : Tarski.interp D) rho, FSAT.listable D /\ decidable (fun v => Tarski.i_atom (P:=tt) v) -> @Tarski.sat _ _ D I _ rho phi.

  (** Also define FVAL for negation-free fragment *)
  Definition FVAL_frag_no_negation (phi : minimalForm falsity_off) :=
  forall D (I : Tarski.interp D) rho, FSAT.listable D /\ decidable (fun v => Tarski.i_atom (P:=tt) v) -> @Tarski.sat _ _ D I _ rho phi.

  (** ** Dyadic finite satisfiability, small fragment with negation *)
  Lemma minFiniteSatisfiabilityUndec : undecidable FSAT_frag.
  Proof.
    apply (undecidability_from_reducibility H10UPC_SAT_undec).
    eapply reduces_transitive.
    * eexists. apply fsat_reduction.
    * eexists. apply frag_reduction_fsat.
  Qed.

  (** ** Dyadic finite validity, small fragment with negation *)
  Lemma minFiniteValidityUndec : undecidable FVAL_frag.
  Proof.
    apply (undecidability_from_reducibility H10UPC_SAT_compl_undec).
    eapply reduces_transitive.
    * eexists. apply fval_reduction.
    * eexists. apply frag_reduction_fval.
  Qed.

  (** This is a conjecture *)
  Lemma minFiniteValidityConjecture : undecidable FVAL_frag_no_negation.
  Abort.

End finite.
(*
Print Assumptions minFiniteValidityUndec.
Print Assumptions minFiniteSatisfiabilityUndec.
Print Assumptions minProvabilityUndec.
Print Assumptions minSatisfiabilityUndec.
Print Assumptions minValidityUndec.
Print Assumptions minKripkeSatisfiabilityUndec.
Print Assumptions minKripkeValidityUndec. *)

(* Closed under the global context *)
