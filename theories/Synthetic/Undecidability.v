Require Export Undecidability.Synthetic.Definitions Undecidability.Synthetic.ReducibilityFacts.
Require Import Undecidability.TM.TM.

Definition undecidable {X} (p : X -> Prop) :=
  decidable p -> decidable (HaltTM 1).

Polymorphic Definition mundecidable {X} (p : X -> Prop) :=
  decidable p -> semi_decidable (complement (HaltTM 1)).

Lemma undecidability_HaltTM :
  undecidable (HaltTM 1).
Proof.
  intros H. exact H.
Qed.

Lemma mundecidability_HaltTM :
  mundecidable (HaltTM 1).
Proof.
  intros [f H].
  exists (fun x n => if f x then false else true). intros x.
  unfold decider, reflects in H.
  unfold complement. rewrite H. firstorder. econstructor. 1:exact 0.
  all: destruct (f x); congruence.
Qed.

Lemma mundecidability_HaltTM_compl :
  mundecidable (complement (HaltTM 1)).
Proof.
  intros [f H].
  exists (fun x n => f x). intros x.
  unfold decider, reflects in H.
  rewrite H. firstorder. econstructor.
Qed.

Lemma undecidability_from_reducibility {X} {p : X -> Prop} {Y} {q : Y -> Prop} :
  undecidable p -> p ⪯ q -> undecidable q.
Proof.
  unfold undecidable, decidable, decider, reduces, reduction, reflects.
  intros H [f Hf] [d Hd]. eapply H. exists (fun x => d (f x)). intros x. rewrite Hf. eapply Hd.
Qed.

Lemma mundecidability_from_reducibility {X} {p : X -> Prop} {Y} {q : Y -> Prop} :
  mundecidable p -> p ⪯ q -> mundecidable q.
Proof.
  unfold mundecidable, decidable, decider, reduces, reduction, reflects, semi_decidable, semi_decider.
  intros H [f Hf] [d Hd]. eapply H. exists (fun x => d (f x)). intros x. rewrite Hf. eapply Hd.
Qed.

Lemma mundecidability_from_reducibility' {X} {p : X -> Prop} {Y} {q : Y -> Prop} :
  undecidable p -> p ⪯ q -> mundecidable q.
Proof.
  intros H. apply mundecidability_from_reducibility.
  intros H'. specialize (H H').
  now apply mundecidability_HaltTM.
Qed.

Module UndecidabilityNotations.

Tactic Notation "undec" "from" constr(H) :=
  apply (undecidability_from_reducibility H).

Tactic Notation "reduce" "with" "chain" constr(H) := 
  repeat (apply reduces_reflexive || (eapply reduces_transitive; [ apply H | ])).

Tactic Notation "undec" "from" constr(U) "using" "chain" constr(C) :=
  undec from U; reduce with chain C.

End UndecidabilityNotations.
